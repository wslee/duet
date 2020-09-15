open Exprs
open Vocab
open Graph 

type rewrite = 
	| NTRewrite of string 
	| ExprRewrite of expr 
	| FuncRewrite of id * rewrite list  

let nt_type_map = ref BatMap.empty 

let type_of_nt nt = try BatMap.find nt !nt_type_map with _ -> failwith "type_of_nt" 

type grammar = (rewrite, rewrite BatSet.t) BatMap.t 

let rec get_nts rewrite =
	match rewrite with 
	| FuncRewrite (op, rewrites) ->
		BatList.fold_left (fun acc rewrite' -> acc @ (get_nts rewrite')) [] rewrites
	| NTRewrite _ -> [rewrite] 
	| _ -> []
	
let op_of_rule rule = 
	match rule with 
	| FuncRewrite (op, _) -> op 
	| _ -> failwith "op_of_rule"

let expr_of_rewrite rewrite = 
	match rewrite with 
	| ExprRewrite expr -> expr  
	| _ -> assert false  

let ret_type_of_op rule =
	let op = op_of_rule rule in 
	(** theory agnostic *)
	if (String.compare op "=") = 0 then Bool
	else if (String.compare op "<") = 0 then Bool
	else if (String.compare op ">") = 0 then Bool
	else if (String.compare op "<=") = 0 then Bool
	else if (String.compare op ">=") = 0 then Bool
	else if (String.compare op "ite") = 0 then  
		let nts = get_nts rule in 
		let _ = assert ((BatList.length nts) = 3) in 
		type_of_nt (BatList.nth nts 1)
	(** Bool theory **)
	else if (String.compare op "and") = 0 then Bool
	else if (String.compare op "or") = 0 then Bool
	else if (String.compare op "xor") = 0 then Bool
	else if (String.compare op "not") = 0 then Bool
	(** STRING theory **)
	else if (String.compare op "str.len") = 0 then Int
	else if (String.compare op "str.to.int") = 0 then Int
	else if (String.compare op "int.to.str") = 0 then String
	else if (String.compare op "str.at") = 0 then String
	else if (String.compare op "str.++") = 0 then String 
	else if (String.compare op "str.contains") = 0 then Bool
	else if (String.compare op "str.prefixof") = 0 then Bool 
	else if (String.compare op "str.suffixof") = 0 then Bool
	else if (String.compare op "str.indexof") = 0 then Int
	else if (String.compare op "str.replace") = 0 then String 
	else if (String.compare op "str.substr") = 0 then String 
	(** BV theory **)
	else if (String.compare op "bvadd") = 0 then BV
	else if (String.compare op "bvsub") = 0 then BV
	else if (String.compare op "bvneg") = 0 then BV
	else if (String.compare op "bvnot") = 0 then BV
	else if (String.compare op "bvmul") = 0 then BV
	else if (String.compare op "bvudiv") = 0 then BV
	else if (String.compare op "bvsdiv") = 0 then BV
	else if (String.compare op "bvurem") = 0 then BV
	else if (String.compare op "bvsrem") = 0 then BV
	else if (String.compare op "bvand") = 0 then BV
	else if (String.compare op "bvor") = 0 then BV
	else if (String.compare op "bvxor") = 0 then BV
	else if (String.compare op "bvashr") = 0 then BV
	else if (String.compare op "bvlshr") = 0 then BV
	else if (String.compare op "bvshl") = 0 then BV
	(** LIA theory **)
	else if (String.compare op "+") = 0 then Int  
	else if (String.compare op "-") = 0 then Int
	else if (String.compare op "*") = 0 then Int 
	else if (String.compare op "/") = 0 then Int
	else if (String.compare op "%") = 0 then Int 
	else failwith ("not supported operator: " ^ op)		 	   


(* to determine which kinds of witness functions are used *)
let witness_type_of_op rule =
	let op = op_of_rule rule in 
	(** BV and STRING *)
	if (BatString.starts_with op "bv") then BV 
	else if (BatString.exists op "str") then String 
	(** Bool theory **)
	else if (String.compare op "and") = 0 then Bool
	else if (String.compare op "or") = 0 then Bool
	else if (String.compare op "xor") = 0 then Bool
	else if (String.compare op "not") = 0 then Bool
	(** LIA theory **)
	else Int 
	(* else if (String.compare op "<") = 0 then Int        *)
	(* else if (String.compare op ">") = 0 then Int        *)
	(* else if (String.compare op "<=") = 0 then Int       *)
	(* else if (String.compare op ">=") = 0 then Int       *)
	(* else if (String.compare op "+") = 0 then Int        *)
	(* else if (String.compare op "-") = 0 then Int        *)
	(* else if (String.compare op "*") = 0 then Int        *)
	(* else if (String.compare op "/") = 0 then Int        *)
	(* else if (String.compare op "%") = 0 then Int        *)
	(* else failwith ("not supported operator: " ^ op)		 *)

let exclude_ite_rules nt_rule_list =  
	List.filter (fun (nt, rule) -> 
		not (BatString.equal "ite" (try op_of_rule rule with _ -> ""))
	) nt_rule_list

								
let is_commutative_rule rule =
  match rule with
  | FuncRewrite (op, _) ->
		(BatList.mem op 
			["+"; "*"; "bvadd;"; "bvmul"; "bvand"; "bvor"; "bvxor"; "and"; "or"; "xor"])
  | _ -> false

let is_nt_rule rule =
	match rule with 
	| NTRewrite _ -> true 
	| _ -> false
	
let is_equal_nt nt nt' = 
	match nt, nt' with 
	| NTRewrite s, NTRewrite s' -> BatString.equal s s'
	| _ -> false
 
let is_function_rule rule =
	match rule with 
	| FuncRewrite _ -> true 
	| _ -> false 

let is_param_rule rule = 
	match rule with 
	| ExprRewrite (Param _ ) -> true 
	| _ -> false 

let is_constant_rule rule = 
	match rule with 
	| ExprRewrite (Const _ ) -> true 
	| _ -> false 

let rec string_of_rewrite rewrite = 
	match rewrite with 
	| NTRewrite nt_id -> "N_" ^ nt_id 
	| ExprRewrite expr -> "E_" ^ string_of_expr expr 
	| FuncRewrite (op, rewrites) -> 
		Printf.sprintf "(%s %s)" op
			(string_of_list ~first:"" ~last:"" ~sep:" " string_of_rewrite rewrites)  

let string_of_rewritelist rewritelist = 
	string_of_list string_of_rewrite rewritelist

let string_of_rewriteset rewriteset = 
	string_of_set string_of_rewrite rewriteset

let rec size_of_rewrite rewrite = 
	match rewrite with 
	| NTRewrite _ -> 0
	| ExprRewrite expr -> size_of_expr expr
	| FuncRewrite (op, rewrites) -> 
		List.fold_left (fun size rewrite -> size + (size_of_rewrite rewrite)) 1 rewrites  	

let compare_rewrite r1 r2 = 
	(* STR operators precedes LIA operators (.e.,g +, -) *)
	(* WHY? *)
	(*   In STR benchmarks, *)
	(*   I observed LIA witness functions often keep generating hopeless subspecs *)
	(*   wasiting resources. But STR witness functions often generate proper subspecs. *)
	(*   Therefore, we prioritize production rules. STR operators first. *)
	String.compare (string_of_rewrite r2) (string_of_rewrite r1)  

module NTNode = struct
	type t = rewrite (* non-terminal *) 
	let compare = compare_rewrite  
	let equal r1 r2 = (compare_rewrite r1 r2) = 0  
	let hash = Hashtbl.hash  
end

module NTGraph = Persistent.Digraph.ConcreteBidirectional(NTNode) 
module NTTopology = Topological.Make(NTGraph)

(* return a list of pairs of a non-terminal and a production rule*)
(* the list follows the topological order in the graph of non-terminals*)
(* e.g., having a rule N1 -> f(N2), N2 comes before N1 *)
let get_nt_rule_list grammar =
	let nt_rule_list =
		BatMap.foldi (fun nt rules lst ->
			BatSet.fold (fun rule lst -> (nt, rule) :: lst) rules lst
		) grammar []
	in
	let ntgraph = 
		BatMap.foldi (fun nt rules g ->
			BatSet.fold (fun rule g ->
				let nts = get_nts rule in 
				List.fold_left (fun g nt' ->
					NTGraph.add_edge g nt' nt
				) g nts
			) rules g
		) grammar NTGraph.empty
	in
	let topological_sorted_nts = 
		NTTopology.fold (fun nt lst ->
			if (List.mem nt lst) then lst 
			else lst @ [nt]  
		) ntgraph []
	in   
	List.map (fun nt -> 
		List.filter (fun (nt', _) -> is_equal_nt nt nt') nt_rule_list
		(* (try BatMap.find nt grammar with _ -> failwith (string_of_rewrite nt))  *)
		(* |> BatSet.elements                                                      *)
		(* |> List.map (fun rule -> (nt, rule))                                    *)
	) topological_sorted_nts |> List.flatten 
	

let start_nt = NTRewrite "Start"
(* let start_nt_ty = ref Int                                         *)

(* let string_nt_id = "String"                                       *)
(* let string_nt = (NTRewrite string_nt_id)                          *)
(* let int_nt_id = "Int"                                             *)
(* let int_nt = (NTRewrite int_nt_id)                                *)
(* let bv_nt_id = "BV"                                               *)
(* let bv_nt = (NTRewrite bv_nt_id)                                  *)
(* let bool_nt_id = "Bool"                                           *)
(* let bool_nt = (NTRewrite bool_nt_id)                              *)

(* let nt_of_type ty =                                               *)
(* 	match ty with                                                   *)
(* 	| Int -> int_nt                                                 *)
(* 	| BV -> bv_nt                                                   *)
(* 	| String -> string_nt                                           *)
(* 	| Bool -> bool_nt                                               *)

(* let type_of_nt nt =                                               *)
(* 	match nt with                                                   *)
(* 	| NTRewrite nt_id ->                                            *)
(* 		if (String.compare nt_id int_nt_id) = 0 then Int              *)
(* 		else if (String.compare nt_id string_nt_id) = 0 then String   *)
(* 		else if (String.compare nt_id bool_nt_id) = 0 then Bool       *)
(* 		else if (String.compare nt_id bv_nt_id) = 0 then BV           *)
(* 		else if (String.compare nt_id "Start") = 0 then !start_nt_ty  *)
(* 		else failwith nt_id                                           *)
(* 	| _ -> assert false                                             *)


let add_rule nt rule grammar =
	let rules = try BatMap.find nt grammar with _ -> BatSet.empty in 
	BatMap.add nt (BatSet.add rule rules) grammar   

let empty_grammar = BatMap.empty 
		
let string_of_grammar grammar = 
	BatMap.foldi (fun nt rules acc ->
		Printf.sprintf "%s -> %s\n%s" 
			(string_of_rewrite nt)
			(string_of_rewriteset rules)
			acc  
	) grammar ""
				
(* let init_grammar =                                                                 *)
(* 	let string_nt_id = "String" in                                                   *)
(*   let string_nt = (NTRewrite string_nt_id) in                                      *)
(*   let int_nt_id = "Int" in                                                         *)
(*   let int_nt = (NTRewrite int_nt_id) in                                            *)
(*   let bool_nt_id = "Bool" in                                                       *)
(*   let bool_nt = (NTRewrite bool_nt_id) in                                          *)
(* 	List.fold_left (fun m (nt,rule) -> add_rule nt rule m) BatMap.empty              *)
(* 	[                                                                                *)
(* 		(* (* String *)                                                             *) *)
(* 		(* (string_nt, ExprRewrite (Const (CString " ")));                          *) *)
(* 		(* (* (string_nt, ExprRewrite (Const (CString "("))); *)                    *) *)
(* 		(* (* (string_nt, ExprRewrite (Const (CString ")"))); *)                    *) *)
(* 		(* (* (string_nt, ExprRewrite (Const (CString "-"))); *)                    *) *)
(* 		(* (string_nt, ExprRewrite (Const (CString ".")));                          *) *)
(* 		(* (* (string_nt, ExprRewrite (Const (CString ","))); *)                    *) *)
(* 		(* (string_nt, FuncRewrite ("charAt", [string_nt; int_nt]));                *) *)
(* 		(* (string_nt, FuncRewrite ("concat", [string_nt; string_nt]));             *) *)
(* 		(* (string_nt, FuncRewrite ("replace", [string_nt; string_nt; string_nt])); *) *)
(* 		(* (string_nt, FuncRewrite ("substr", [string_nt; int_nt; int_nt]));        *) *)
		
(* 		(* Int *)                                                                      *)
(* 		(* (int_nt, ExprRewrite (Const (CInt 0)));        *)                           *)
(* 		(* (int_nt, ExprRewrite (Const (CInt 1)));        *)                           *)
(* 		(* (int_nt, ExprRewrite (Const (CInt 2)));        *)                           *)
(* 		(* (int_nt, ExprRewrite (Const (CInt 3)));        *)                           *)
(* 		(* (int_nt, ExprRewrite (Const (CInt 4)));        *)                           *)
(* 		(* (int_nt, ExprRewrite (Const (CInt 5)));        *)                           *)
(* 		(* (int_nt, ExprRewrite (Const (CInt 6)));        *)                           *)
(* 		(* (int_nt, ExprRewrite (Const (CInt 7)));        *)                           *)
(* 		(* (int_nt, ExprRewrite (Const (CInt 8)));        *)                           *)
(* 		(* (int_nt, ExprRewrite (Const (CInt 9)));        *)                           *)
(* 		(* (int_nt, FuncRewrite ("+", [int_nt; int_nt])); *)                           *)
(* 		(* (int_nt, FuncRewrite ("-", [int_nt; int_nt])); *)                           *)
(* 		(* (int_nt, FuncRewrite ("*", [int_nt; int_nt])); *)                           *)
(* 		(* (int_nt, FuncRewrite ("&", [int_nt; int_nt])); *)                           *)
(* 		(* (int_nt, FuncRewrite ("|", [int_nt; int_nt])); *)                           *)
(* 		(* (int_nt, FuncRewrite ("^", [int_nt; int_nt])); *)                           *)
(* 		(* (int_nt, FuncRewrite ("/", [int_nt; int_nt])); *)                           *)
(* 	]                                                                                *)
	
		