open Vocab

exception UndefinedSemantics

type id = string 
type exprtype = Int | BV | String | Bool 
type const = CInt of int 
	| CBV of Int64.t 
	| CString of string 
	| CBool of my_bool 
and my_bool = Concrete of bool | Abstract (* can be either of true or false *) 
	
type expr =  
	| Param of int * exprtype (* position and type *)
	| Var of string * exprtype (* name and type : only for SMT *) 
	| Const of const 
	| Function of id * expr list * exprtype  

let string_of_type ?(z3=false) ty = 
	match ty with 
	| Int -> "Int"
	| BV -> if z3 then "(_ BitVec 64)" else "(BitVec 64)"
	| String -> "String"
	| Bool -> "Bool"

type iospec = ((const list) * const) list 

type signature = const list  

let get_param_id expr = 
	match expr with 
	| Param (i, _) -> i 
	| _ -> failwith "get_param_id"

let rec get_params expr = 
	match expr with 
	| Param _ -> BatSet.singleton expr 
	| Function (_, exprs, _) -> 
		List.fold_left (fun acc e -> BatSet.union acc (get_params e)) BatSet.empty exprs 
	| _ -> BatSet.empty  

let get_trivial_value ty = 
	match ty with 
	| Int -> CInt 0  
	| BV -> CBV (Int64.zero) 
	| String -> CString "" 
	| Bool -> CBool (Concrete true) 

let get_trivial_value2 ty = 
	match ty with 
	| Int -> CInt 1  
	| BV -> CBV (Int64.one) 
	| String -> CString "a" 
	| Bool -> CBool (Concrete false) 

let is_function_expr expr = 
	match expr with 
	| Function _ -> true 
	| _ -> false 
	
let is_const_expr expr = 
	match expr with 
	| Const _ -> true
	| _ -> false 

let type_of_const const = 
	match const with 
	| CInt _ -> Int 
	| CBV _ -> BV 
	| CString _ -> String 
	| CBool _ -> Bool 
	
let type_of_expr expr = 
	match expr with 
	| Param (_, ty) -> ty
	| Var (_, ty) -> ty  
	| Function (_, _, ty) -> ty 
	| Const const -> type_of_const const  

let rec join strlist = 
	match strlist with 
	| [] -> ""
	| hd :: [] -> hd 
	| hd :: tl -> hd ^ ", " ^ (join tl)  
		
let string_of_my_bool mybool = 
	match mybool with 
	| Concrete b -> string_of_bool b 
	| Abstract -> "*" 

let rec string_of_const const = 
	match const with 
	| CInt n -> string_of_int n
	| CBV n -> 
		(* Int64.to_string n *)
		Printf.sprintf "#x%016Lx" n
	| CString s -> "\"" ^ s ^ "\"" 
	| CBool b -> string_of_my_bool b 

let string_of_signature signature =
	string_of_list string_of_const signature

let rec string_of_expr expr = 
	match expr with 
	| Const const -> string_of_const const 
	| Var (id, ty) -> id 
	| Param (n, ty) -> Printf.sprintf "arg_%d" n 
	| Function (op, exprs, ty) -> 
		Printf.sprintf "(%s %s)" op 
			(string_of_list ~first:"" ~last:"" ~sep:" " string_of_expr exprs)

let rec size_of_expr expr = 
	match expr with 
	| Const _ -> 1 
	| Param _ -> 1 
	| Var _ -> 1 
	| Function (op, exprs, ty) -> List.fold_left (fun size expr -> size + (size_of_expr expr)) 1 exprs  

let expr2const expr = 
	match expr with 
	| Const const -> const 
	| _ -> assert false
		
let get_op expr = 
	match expr with 
	| Function(op, _, _) -> op
	| _ -> failwith "get_op"  

let get_children expr = 
	match expr with 
	| Function(op, children, _) -> children
	| _ -> failwith "get_children"
		
let get_bv expr = 
	match expr with 
	| (CBV i) -> i 
	| _ -> assert false
			
let get_string expr = 
	match expr with 
	| (CString s) -> s 
	| _ -> assert false 

let get_int expr = 
	match expr with 
	| (CInt i) -> i 
	| _ -> assert false 

let is_abstract_bool expr = 
	match expr with 
	| CBool Abstract -> true 
	| _ -> false 
	
let get_concrete_bool expr = 
	match expr with 
	| CBool (Concrete b) -> b 
	| _ -> assert false 

let rec change_param_to_var param2var expr =
	match expr with 
	| Param _ -> (try BatMap.find expr param2var with _ -> assert false)
	| Function (op, exprs, ty) -> Function (op, List.map (change_param_to_var param2var) exprs, ty)   
	| _ -> expr  	

let sexpstr_of_fun args_map name expr =
	(* Param _ -> Var _ *)
	let param2var = 
		BatMap.foldi (fun id param_expr acc ->
			let ty = type_of_expr param_expr in 
			BatMap.add param_expr (Var(id, ty)) acc  
		) args_map BatMap.empty
	in
	let expr = change_param_to_var param2var expr in 
	let params = 
		BatMap.foldi (fun id param_expr acc -> (id, param_expr) :: acc) args_map []
		|> List.sort (fun (_, param_expr1) (_, param_expr2) -> (get_param_id param_expr1) - (get_param_id param_expr2)) 
		|> List.map (fun (id, param_expr) -> Var(id, type_of_expr param_expr))
	in
	let params_str =
		(List.fold_left (fun acc param -> 
			Printf.sprintf "%s (%s %s)" acc (string_of_expr param) (string_of_type (type_of_expr param))
		 ) "" params) 
	in 
	let ret_type_str = (string_of_type (type_of_expr expr)) in 
	Printf.sprintf "(define-fun %s (%s) %s %s)" 
		name
		params_str 
		ret_type_str 
		(string_of_expr expr)

(* string -> signature list -> signature *)
let fun_apply_signature op values =
	if (String.compare op "=") = 0 then
		let sig1 = (List.nth values 0) in
		let sig2 = (List.nth values 1) in
		List.map2 (fun const1 const2 -> CBool (Concrete ((Pervasives.compare const1 const2) = 0))) sig1 sig2
	else if (String.compare op "<") = 0 then
		let sig1 = (List.nth values 0) in
		let sig2 = (List.nth values 1) in
		List.map2 (fun const1 const2 -> CBool (Concrete ((Pervasives.compare const1 const2) < 0))) sig1 sig2
	else if (String.compare op ">") = 0 then
		let sig1 = (List.nth values 0) in
		let sig2 = (List.nth values 1) in
		List.map2 (fun const1 const2 -> CBool (Concrete ((Pervasives.compare const1 const2) > 0))) sig1 sig2
	else if (String.compare op "<=") = 0 then
		let sig1 = (List.nth values 0) in
		let sig2 = (List.nth values 1) in
		List.map2 (fun const1 const2 -> CBool (Concrete ((Pervasives.compare const1 const2) <= 0))) sig1 sig2
	else if (String.compare op ">=") = 0 then
		let sig1 = (List.nth values 0) in
		let sig2 = (List.nth values 1) in
		List.map2 (fun const1 const2 -> CBool (Concrete ((Pervasives.compare const1 const2) >= 0))) sig1 sig2
	else if (String.compare op "ite") = 0 then
		let bools = List.map get_concrete_bool (List.nth values 0) in
		let sig1 = (List.nth values 1) in
		let sig2 = (List.nth values 2) in
		map3 (fun bool const1 const2 -> if bool then const1 else const2) bools sig1 sig2
	(** Bool theory **)
	else if (String.compare op "and") = 0 then
		let bools1 = List.map get_concrete_bool (List.nth values 0) in 
		let bools2 = List.map get_concrete_bool (List.nth values 1) in
		List.map2 (fun const1 const2 -> CBool (Concrete (const1 && const2))) bools1 bools2
	else if (String.compare op "or") = 0 then
		let bools1 = List.map get_concrete_bool (List.nth values 0) in 
		let bools2 = List.map get_concrete_bool (List.nth values 1) in
		List.map2 (fun const1 const2 -> CBool (Concrete (const1 || const2))) bools1 bools2
	else if (String.compare op "xor") = 0 then
		let bools1 = List.map get_concrete_bool (List.nth values 0) in 
		let bools2 = List.map get_concrete_bool (List.nth values 1) in
		List.map2 (fun const1 const2 -> CBool (Concrete (const1 <> const2))) bools1 bools2
	else if (String.compare op "not") = 0 then
		let bools1 = List.map get_concrete_bool (List.nth values 0) in
		List.map (fun const1 -> CBool (Concrete (not const1))) bools1
	(** STRING theory **)
	else if (String.compare op "str.len") = 0 then 
		let strs = List.map get_string (List.nth values 0) in 
		(List.map (fun str -> CInt (String.length str)) strs)
	else if (String.compare op "str.to.int") = 0 then 
		let strs = List.map get_string (List.nth values 0) in 
		(List.map (fun str -> CInt (int_of_string str)) strs)
	else if (String.compare op "int.to.str") = 0 then 
		let nums = List.map get_int (List.nth values 0) in 
		(List.map (fun num -> CString (string_of_int num)) nums)
	else if (String.compare op "str.at") = 0 then 
		let strs = List.map get_string (List.nth values 0) in 
		let nums = List.map get_int (List.nth values 1) in
		(List.map2 (fun str num -> CString (Printf.sprintf "%c" str.[num])) strs nums)
	else if (String.compare op "str.++") = 0 then
		let str1s = List.map get_string (List.nth values 0) in  
		let str2s = List.map get_string (List.nth values 1) in
		(List.map2 (fun str1 str2 -> CString (str1 ^ str2)) str1s str2s) 
	else if (String.compare op "str.contains") = 0 then
		let str1s = List.map get_string (List.nth values 0) in  
		let str2s = List.map get_string (List.nth values 1) in
		(List.map2 (fun str1 str2 -> CBool (Concrete (BatString.exists str1 str2))) str1s str2s)
	else if (String.compare op "str.prefixof") = 0 then
		let str1s = List.map get_string (List.nth values 0) in  
		let str2s = List.map get_string (List.nth values 1) in
		(List.map2 (fun str1 str2 -> CBool (Concrete (BatString.starts_with str2 str1))) str1s str2s)
	else if (String.compare op "str.suffixof") = 0 then
		let str1s = List.map get_string (List.nth values 0) in  
		let str2s = List.map get_string (List.nth values 1) in
		(List.map2 (fun str1 str2 -> CBool (Concrete (BatString.ends_with str2 str1))) str1s str2s)
	else if (String.compare op "str.indexof") = 0 then
		let str1s = List.map get_string (List.nth values 0) in  
		let str2s = List.map get_string (List.nth values 1) in
		let num1s = List.map get_int (List.nth values 2) in
		(map3 (fun str1 str2 num1 -> CInt (try BatString.find_from str1 num1 str2 with Not_found -> -1)) str1s str2s num1s)
	else if (String.compare op "str.replace") = 0 then
		let str1s = List.map get_string (List.nth values 0) in  
		let str2s = List.map get_string (List.nth values 1) in
		let str3s = List.map get_string (List.nth values 2) in
		map3 (fun str1 str2 str3 -> CString (Str.replace_first (Str.regexp_string str2) str3 str1)) str1s str2s str3s 
	else if (String.compare op "str.substr") = 0 then
		let str1s = List.map get_string (List.nth values 0) in  
		let num1s = List.map get_int (List.nth values 1) in
		let num2s = List.map get_int (List.nth values 2) in
		map3 (fun str1 num1 num2 ->
			let num2 = min ((String.length str1) - num1) num2 in
			CString (try (BatString.sub str1 num1 num2) with Invalid_argument _ -> "") 
		) str1s num1s num2s 
	(** BV theory **)
	else if (String.compare op "bvadd") = 0 then
		let num1s = List.map get_bv (List.nth values 0) in
		let num2s = List.map get_bv (List.nth values 1) in
		List.map2 (fun num1 num2 -> CBV (Int64.add num1 num2)) num1s num2s
	else if (String.compare op "bvsub") = 0 then
		let num1s = List.map get_bv (List.nth values 0) in
		let num2s = List.map get_bv (List.nth values 1) in
		List.map2 (fun num1 num2 -> CBV (Int64.sub num1 num2)) num1s num2s
	else if (String.compare op "bvneg") = 0 then
		let num1s = List.map get_bv (List.nth values 0) in
		List.map (fun num1 -> CBV (Int64.neg num1)) num1s
	else if (String.compare op "bvnot") = 0 then
		let num1s = List.map get_bv (List.nth values 0) in
		List.map (fun num1 -> CBV (Int64.lognot num1)) num1s
	else if (String.compare op "bvmul") = 0 then
		let num1s = List.map get_bv (List.nth values 0) in
		let num2s = List.map get_bv (List.nth values 1) in
		List.map2 (fun num1 num2 -> CBV (Int64.mul num1 num2)) num1s num2s
	else if (String.compare op "bvudiv") = 0 then
		let num1s = List.map get_bv (List.nth values 0) in
		let num2s = List.map get_bv (List.nth values 1) in
		List.map2 (fun num1 num2 -> CBV (Int64.unsigned_div num1 num2)) num1s num2s
	else if (String.compare op "bvsdiv") = 0 then
		let num1s = List.map get_bv (List.nth values 0) in
		let num2s = List.map get_bv (List.nth values 1) in
		List.map2 (fun num1 num2 -> CBV (Int64.div num1 num2)) num1s num2s
	else if (String.compare op "bvurem") = 0 then
		let num1s = List.map get_bv (List.nth values 0) in
		let num2s = List.map get_bv (List.nth values 1) in
		List.map2 (fun num1 num2 -> CBV (Int64.unsigned_rem num1 num2)) num1s num2s
	else if (String.compare op "bvsrem") = 0 then
		let num1s = List.map get_bv (List.nth values 0) in
		let num2s = List.map get_bv (List.nth values 1) in
		List.map2 (fun num1 num2 -> CBV (Int64.rem num1 num2)) num1s num2s
	else if (String.compare op "bvand") = 0 then
		let num1s = List.map get_bv (List.nth values 0) in
		let num2s = List.map get_bv (List.nth values 1) in
		List.map2 (fun num1 num2 -> CBV (Int64.logand num1 num2)) num1s num2s
	else if (String.compare op "bvor") = 0 then
		let num1s = List.map get_bv (List.nth values 0) in
		let num2s = List.map get_bv (List.nth values 1) in
		List.map2 (fun num1 num2 -> CBV (Int64.logor num1 num2)) num1s num2s
	else if (String.compare op "bvxor") = 0 then
		let num1s = List.map get_bv (List.nth values 0) in
		let num2s = List.map get_bv (List.nth values 1) in
		List.map2 (fun num1 num2 -> CBV (Int64.logxor num1 num2)) num1s num2s
	else if (String.compare op "bvashr") = 0 then
		let num1s = List.map get_bv (List.nth values 0) in
		let num2s = List.map get_bv (List.nth values 1) in
		List.map2 (fun num1 num2 ->
			let count = (Int64.unsigned_to_int num2) in
			let count = if BatOption.is_none count then 65 else BatOption.get count in 
			if count >= 64 then
				if (Int64.compare num1 Int64.zero) = -1 then (CBV (-1L))
				else (CBV 0L)
			else 
				CBV (Int64.shift_right num1 count)
		) num1s num2s
	else if (String.compare op "bvlshr") = 0 then
		let num1s = List.map get_bv (List.nth values 0) in
		let num2s = List.map get_bv (List.nth values 1) in
		List.map2 (fun num1 num2 ->
			let count = (Int64.unsigned_to_int num2) in
			let count = if BatOption.is_none count then 65 else BatOption.get count in 
			if count >= 64 then (CBV 0L)
			else CBV (Int64.shift_right_logical num1 count)
		) num1s num2s
	else if (String.compare op "bvshl") = 0 then
		let num1s = List.map get_bv (List.nth values 0) in
		let num2s = List.map get_bv (List.nth values 1) in
		List.map2 (fun num1 num2 ->
			let count = (Int64.unsigned_to_int num2) in
			let count = if BatOption.is_none count then 65 else BatOption.get count in 
			if count >= 64 then (CBV 0L)
			else CBV (Int64.shift_left num1 count)
		) num1s num2s
	else if (String.compare op "bvule") = 0 then
		let num1s = List.map get_bv (List.nth values 0) in
		let num2s = List.map get_bv (List.nth values 1) in
		List.map2 (fun num1 num2 ->
			let compare = Int64.unsigned_compare num1 num2 in
			CBool (Concrete (compare = 0 || compare = -1))
		) num1s num2s
	else if (String.compare op "bvult") = 0 then
		let num1s = List.map get_bv (List.nth values 0) in
		let num2s = List.map get_bv (List.nth values 1) in
		List.map2 (fun num1 num2 ->
			let compare = Int64.unsigned_compare num1 num2 in
			CBool (Concrete (compare = -1))
		) num1s num2s
	else if (String.compare op "bvugt") = 0 then
		let num1s = List.map get_bv (List.nth values 0) in
		let num2s = List.map get_bv (List.nth values 1) in
		List.map2 (fun num1 num2 ->
			let compare = Int64.unsigned_compare num1 num2 in
			CBool (Concrete (compare = 1))
		) num1s num2s
	else if (String.compare op "bvsle") = 0 then
		let num1s = List.map get_bv (List.nth values 0) in
		let num2s = List.map get_bv (List.nth values 1) in
		List.map2 (fun num1 num2 ->
			let compare = Int64.compare num1 num2 in
			CBool (Concrete (compare = 0 || compare = -1))
		) num1s num2s
	else if (String.compare op "bvslt") = 0 then
		let num1s = List.map get_bv (List.nth values 0) in
		let num2s = List.map get_bv (List.nth values 1) in
		List.map2 (fun num1 num2 ->
			let compare = Int64.compare num1 num2 in
			CBool (Concrete (compare = -1))
		) num1s num2s
	else if (String.compare op "bvsgt") = 0 then
		let num1s = List.map get_bv (List.nth values 0) in
		let num2s = List.map get_bv (List.nth values 1) in
		List.map2 (fun num1 num2 ->
			let compare = Int64.compare num1 num2 in
			CBool (Concrete (compare = 1))
		) num1s num2s
	else if (String.compare op "bvsge") = 0 then
		let num1s = List.map get_bv (List.nth values 0) in
		let num2s = List.map get_bv (List.nth values 1) in
		List.map2 (fun num1 num2 ->
			let compare = Int64.compare num1 num2 in
			CBool (Concrete (compare = 0 || compare = 1))
		) num1s num2s	
	(** LIA theory **)
	else if (String.compare op "+") = 0 then
		let num1s = List.map get_int (List.nth values 0) in
		let num2s = List.map get_int (List.nth values 1) in
		List.map2 (fun num1 num2 -> CInt (num1 + num2)) num1s num2s 
	else if (String.compare op "-") = 0 then
		let num1s = List.map get_int (List.nth values 0) in
		(* let num2s = List.map get_int (List.nth values 1) in *)
		let num2s = try List.map get_int (List.nth values 1)
		 (* if 'values' is too short, use '-' as unary operator  *)
			with Failure _ -> List.map (fun x -> 2*x) num1s in 
		List.map2 (fun num1 num2 -> CInt (num1 - num2)) num1s num2s
	else if (String.compare op "*") = 0 then
		let num1s = List.map get_int (List.nth values 0) in
		let num2s = List.map get_int (List.nth values 1) in
		List.map2 (fun num1 num2 -> CInt (num1 * num2)) num1s num2s
	else if (String.compare op "/") = 0 then
		let num1s = List.map get_int (List.nth values 0) in
		let num2s = List.map get_int (List.nth values 1) in
		List.map2 (fun num1 num2 -> CInt (num1 / num2)) num1s num2s
	else if (String.compare op "%") = 0 || (String.compare op "mod") = 0 then
		let num1s = List.map get_int (List.nth values 0) in
		let num2s = List.map get_int (List.nth values 1) in
		let pump r div =
			if r < 0 then
				(((abs r) - 1) / div + 1) * div + r
			else r
		in
		List.map2 (fun num1 num2 -> 
			CInt (pump (num1 mod num2) num2)
		) num1s num2s
	else failwith ("not supported operator: " ^ op)		 	  

(* param_valuation: (int, const list) BatMap.t *)
(* ret type: const list *)
let rec evaluate_expr param_valuation expr =
	let len = try List.length (BatMap.find 0 param_valuation) with _ -> assert false in  
	match expr with 
	| Const const -> BatList.make len const   
	| Param (pos, ty) -> (try BatMap.find pos param_valuation with _ -> assert false) 
	| Function (op, exprs, ty) ->
		let values = List.map (evaluate_expr param_valuation) exprs in
		fun_apply_signature op values
	| _ -> assert false

(* alt_spec : (const list) list *)
let rec evaluate_expr_faster alt_spec expr =
	let len = try List.length (List.hd alt_spec) with _ -> assert false in  
	match expr with 
	| Const const -> BatList.make len const   
	| Param (pos, ty) -> (try (List.nth alt_spec pos) with _ -> assert false) 
	| Function (op, exprs, ty) ->
		let values = List.map (evaluate_expr_faster alt_spec) exprs in
		fun_apply_signature op values
	| _ -> assert false

let compute_signature spec expr = 
	(* param_valuation : (int, const list) BatMap.t *)
	let param_valuation =  
		List.fold_left (fun param_valuation (inputs, _) ->
			(* inputs: const list *)
			let indexed_inputs = 
				List.combine 
					(BatList.range 0 `To ((List.length inputs) - 1))
					inputs
			in
			List.fold_left (fun param_valuation (input_index, input) ->   
				let param_vals = try BatMap.find input_index param_valuation with _ -> [] in
				BatMap.add input_index (param_vals @ [input]) param_valuation 
			) param_valuation indexed_inputs			
		) BatMap.empty spec
	in
	try
		evaluate_expr param_valuation expr
	with _ -> raise UndefinedSemantics
	
let compute_signature_wo_exception spec expr = 	
	let param_valuation =  
		List.fold_left (fun param_valuation (inputs, _) ->
			(* inputs: const list *)
			let indexed_inputs = 
				List.combine 
					(BatList.range 0 `To ((List.length inputs) - 1))
					inputs
			in
			List.fold_left (fun param_valuation (input_index, input) ->   
				let param_vals = try BatMap.find input_index param_valuation with _ -> [] in
				BatMap.add input_index (param_vals @ [input]) param_valuation 
			) param_valuation indexed_inputs			
		) BatMap.empty spec
	in
		evaluate_expr param_valuation expr