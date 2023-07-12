open Sexplib
open Exprs
open Grammar 
open Vocab

let op_type_map = ref BatMap.empty;;

let rec string_of_sexp sexp = 
	match sexp with
	| Sexp.List sexps -> "L["^(BatList.fold_left (fun acc sexp -> acc ^ " " ^ (string_of_sexp sexp)) "" sexps) ^ "]"
	| Sexp.Atom s -> "A:" ^ (*s*) (Sexp.to_string sexp)
;;

let sexp_to_const sexp = 
	let str = Sexp.to_string sexp in 
	if (String.compare str "true") = 0 then Const (CBool (Concrete true))
	else if (String.compare str "false") = 0 then Const (CBool (Concrete false))
	else if (BatString.starts_with str "#x") then 
		Const (CBV (Int64.of_string ("0" ^ (BatString.lchop ~n:1 str))))
	else if (BatString.starts_with str "#u") then 
		Const (CBV (Int64.of_string ("0" ^ (BatString.lchop ~n:1 str))))		
	else if (str.[0] = '\"') then
		(* let _ = prerr_endline str in *)
		Const (CString (BatString.replace_chars (function '\"' -> "" | ';' -> "" | c -> BatString.make 1 c) str))
	else 
		try Const (CInt (int_of_string str)) with _ -> Const (CString str)
;;

let sexp_to_type sexp = 
	match sexp with 
	| Sexp.List _ (* BitVec [bit-width] *) -> BV 
	| Sexp.Atom s -> 
		if (String.compare s "Int") = 0 then Int
		else if (String.compare s "String") = 0 then String
		else if (String.compare s "Bool") = 0 then Bool
		else failwith ("Unknown type: " ^ s) 
;;

let filter_sexps_for tag sexps =
	match sexps with
	| Sexp.Atom _ 
	-> failwith "filter_sexps_for: sexps must be a list of lists"
	| Sexp.List sexps' -> (
		BatList.filter (fun sexp -> 
			match sexp with
			| Sexp.List ((Sexp.Atom tag') :: _) -> tag = tag'
			| _ -> false
		) sexps'
	)
;;

let parse_target_function_arguments sexps =
	match sexps with
	| Sexp.Atom _ 
	-> failwith "parse_target_function_arguments: sexps must be a list of lists"
	| Sexp.List sexps' -> (
		let arguments = BatList.map (fun sexp -> 
			match sexp with
			| Sexp.List [Sexp.Atom name; type_] -> (name, sexp_to_type type_)
			| _ -> failwith "parse_target_function_arguments: target function arguments must be defined as (name type)"
		) sexps' in 
		let indexing_arguments = BatList.combine (BatList.range 0 `To ((BatList.length arguments) - 1)) arguments in
		let make_argument_map acc arg = (
			match arg with
			| (index, (name, type_)) ->
				BatMap.add name (Param(index, type_)) acc
		) in
		BatList.fold_left make_argument_map BatMap.empty indexing_arguments
	)
;;

let rec sexp_to_rule sexp nts args_map = 
	match sexp with
	| Sexp.List sexps' ->
		if (BatList.length sexps' == 0) then
			failwith "sexp_to_rule: production rule must have at least one element"
		else
			let operator = Sexp.to_string (BatList.hd sexps') in
			let children = BatList.tl sexps' in
			let rec sexp_to_rule' children acc =
				match children with
				| [] -> acc
				| child :: children' ->
					let child_rule = sexp_to_rule child nts args_map in
					sexp_to_rule' children' (child_rule :: acc)
				in
				let children = sexp_to_rule' children [] in
				FuncRewrite (operator, children)
	| Sexp.Atom id ->
		if BatSet.mem (NTRewrite id) nts then
			NTRewrite id
		else if BatMap.mem id args_map then
			ExprRewrite (BatMap.find id args_map)
		else
			ExprRewrite (sexp_to_const sexp)
;;

let rules_to_type rules ty = 
	let rules_to_type' ele acc = (
		match ele with
		| FuncRewrite (op, children) ->
			let _ = acc := BatMap.add op ty !acc in 
			acc
		| _ -> acc
	)	in
	op_type_map := !(BatSet.fold rules_to_type' rules op_type_map)
;;

let rec function_body_to_expr args_map body_sexp  =
	match body_sexp with
	| Sexp.List sexps ->
		if (BatList.length sexps) == 0 then
			failwith "function_body_to_expr: function body must have at least one element"
		else
			let operator = Sexp.to_string (BatList.hd sexps) in
			let children = BatList.map (function_body_to_expr args_map) (BatList.tl sexps) in
			let return_type = (
				if BatMap.mem operator !op_type_map then
					BatMap.find operator !op_type_map
				else
					failwith ("function_body_to_expr: unknown operator " ^ operator)
			)
			in
			Function (operator, children, return_type)
		| Sexp.Atom id ->
			if (BatMap.mem id args_map) then
				BatMap.find id args_map
			else
				sexp_to_const body_sexp
;;

let parse_grammar sexps args_map =
	let get_nts acc ele = (
		match ele with
		| Sexp.List sexps -> (
			if (BatList.length sexps) == 3 then
				let nt, ret, rules = (BatList.nth sexps 0, BatList.nth sexps 1, BatList.nth sexps 2) in
				let nt = NTRewrite (Sexp.to_string nt) in
				let ret = sexp_to_type ret in
				let _ = Grammar.nt_type_map := BatMap.add nt ret !Grammar.nt_type_map in
				BatSet.add nt acc
			else 
				failwith "parse_grammar: production rule must be defined as (operator children)"
		)
		| _ -> failwith "parse_grammar: production rule must be defined as (operator children)"
	) in
	let nts = BatList.fold_left get_nts BatSet.empty sexps in
	let get_rules nts args_map acc ele = (
		match ele with
		| Sexp.List sexps ->
			if (BatList.length sexps) == 3 then
				let nt, ret, rules = (BatList.nth sexps 0, BatList.nth sexps 1, BatList.nth sexps 2) in
				let nt = NTRewrite (Sexp.to_string nt) in
				let ret = sexp_to_type ret in
				let rules = (
					match rules with
					| Sexp.Atom _ -> failwith "parse_grammar: production rule must be defined as (operator children)"
					| Sexp.List sexps' -> sexps'
				) in
				let rules = BatList.fold_left (fun acc ele ->
					let rule = sexp_to_rule ele nts args_map in
					BatSet.add rule acc
				) BatSet.empty rules in
				let _ = rules_to_type rules ret in
				BatMap.add nt rules acc
			else
				failwith "parse_grammar: production rule must be defined as (operator children)"
		| _ -> failwith "parse_grammar: production rule must be defined as (operator children)"
	) in
	BatList.fold_left (get_rules nts args_map) BatMap.empty sexps
;;

let parse_synth_fun_sexps sexps =
	let synth_fun_data = filter_sexps_for "synth-fun" sexps in
	if (BatList.length synth_fun_data) <> 1 then
		failwith "parse_synth_fun_sexps: synth-fun must be defined exactly once"
	else
		let _ = my_prerr_endline (string_of_sexp (BatList.hd synth_fun_data)) in
		let synth_fun_data = (BatList.hd synth_fun_data) in
		match synth_fun_data with
		| Sexp.List [Sexp.Atom name; arguments; Sexp.Atom return_type; Sexp.List grammar] ->
			let target_function_name = name in
			let args_map = parse_target_function_arguments arguments in
			let grammar = parse_grammar grammar args_map in
			(target_function_name, args_map, grammar)
		| _ -> failwith "parse_synth_fun_sexps: synth-fun must be defined as (synth-fun name (params) return-type (grammar))"
;;

let parse_declare_var_sexps sexps =
	let declare_var_data = filter_sexps_for "declare-var" sexps in
	let parse_define_fun_sexps' acc ele = (
		match ele with
		| Sexp.List [Sexp.Atom name; type_] ->
			let var = Var(name, (sexp_to_type type_)) in
			BatMap.add name var acc
		| _ -> failwith "parse_declare_var_sexps: declare-var must be defined as (declare-var name type)"
	) in
	BatList.fold_left parse_define_fun_sexps' BatMap.empty declare_var_data
;;

let parse_define_fun_sexps sexps =
	let define_fun_data = filter_sexps_for "define-fun" sexps in
	let parse_define_fun_sexps' acc ele = (
		match ele with
		| Sexp.List [Sexp.Atom name; arguments; return_type; body] ->
			let args_map = parse_target_function_arguments arguments in
			let return_type = sexp_to_type return_type in
			let body = function_body_to_expr args_map body in
			BatMap.add name body acc
		| _ -> failwith "parse_define_fun_sexps: define-fun must be defined as (define-fun name (params) return-type body)"
	) in
	BatList.fold_left parse_define_fun_sexps' BatMap.empty define_fun_data
;;

let parse_constraints_sexps sexps grammar target_function_name macro_instantiator id2var =
	let constraint_data = filter_sexps_for "constraint" sexps in
	let parse_constraint_sexps' spec ele = (
		match ele with
		| Sexp.List _ ->
			let expr = function_body_to_expr id2var ele in
			if (String.compare (get_op expr) "=") == 0 then
				let child = get_children expr in
				let lhs = BatList.hd child in
				let rhs = BatList.nth child 1 in
				(*  (= (f const_0) const_1) *)
				if (Exprs.is_const_expr lhs) || (Exprs.is_const_expr rhs) then
					let inputs, output = (
						if (Exprs.is_const_expr lhs) then
							(get_children rhs, expr2const lhs)
						else 
							(get_children lhs, expr2const rhs)
					) in
					let inputs = BatList.map expr2const inputs in
					Specification.add_io_spec (inputs, output) spec
				(* (= (f const_0) (g const_0)) *)
				else if (Exprs.is_function_expr lhs) && (Exprs.is_function_expr rhs) then
					let target_expr, oracle_expr = (
						if (String.compare (get_op lhs) target_function_name) == 0 then
							(lhs, rhs)
						else 
							(rhs, lhs)
					) in
					if BatMap.mem (get_op oracle_expr) macro_instantiator then
						let oracle_expr_resolved = BatMap.find (get_op oracle_expr) macro_instantiator in
						let _ = Specification.oracle_expr := oracle_expr in
						let _ = Specification.oracle_expr_resolved := oracle_expr_resolved in
						let oracle_args = get_children oracle_expr in
						let oracle_args_indexing = BatList.combine (BatList.range 0 `To ((BatList.length oracle_args)-1)) oracle_args in
						let forall_var_map = BatList.fold_left (fun acc (index, arg) -> 
							BatMap.add (Exprs.string_of_expr arg) (Param(index, (Exprs.type_of_expr arg))) acc
						) BatMap.empty oracle_args_indexing in
						let _ = Specification.forall_var_map := forall_var_map in
						Specification.add_trivial_examples grammar spec
					else
						failwith "macro function is not defined"
				else
					failwith "Not supported: synth-fun is missing"
			else 
				failwith "Not supported: not a SyGus-pbe constraint"
		| _ -> failwith "parse_constraint_sexps: constraint must be defined as (constraint body)"
	) in
	BatList.fold_left parse_constraint_sexps'  Specification.empty_spec constraint_data
;;

(* input : file name *)
(* output : 6-tuple
  macro_instantiator    : BatMap [String -> Expr]
  -> user function
  target_function_name  : String
  -> target function name
  args_map              : BatMap [String -> expr.Param(int, exprtype)]
  -> function argument
  grammar               : BatMap [NTRewrite -> BatSet[Rewrite]]
  ->  production rule
  forall_var_map        : BatMap [String -> expr.Var(String, exprtype)]
  ->  user variable
  spec                  : Specification
  ->  constraint
  (Grammer.nt_type_map : BatMap [NTRewrite -> exprtype])
*)
let parse file =
  Random.self_init(); 
	let lines = read_lines file in
	let file' = file ^ "_" ^ (string_of_int (Random.int 1000)) in
	let lines = 
		BatList.map (fun line -> 
			BatString.fold_left (fun (opened, acc) c ->
				if (c = '\"') then
					if not opened then 
						(true, acc ^ (BatString.of_char c) ^ ";")
					else  
						(false, acc ^ (BatString.of_char c))
				else 
					(opened, acc ^ (BatString.of_char c))
			) (false, "") line |> snd 
		) lines 
	in  
	let _ = write_lines lines file' in  
	let sexps = Sexp.List (Sexp.load_sexps file') in
	let _ = Unix.unlink file' in
	let target_function_name, args_map, grammar = parse_synth_fun_sexps sexps in
	let id2var = parse_declare_var_sexps sexps in
	let macro_instantiator =  parse_define_fun_sexps sexps in
	let spec = parse_constraints_sexps sexps grammar target_function_name macro_instantiator id2var in
	my_prerr_endline (Specification.string_of_io_spec spec);
	(macro_instantiator, target_function_name, args_map, grammar, !Specification.forall_var_map, spec)  
;;