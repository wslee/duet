open Sexplib
open Vocab
open Exprs
open Z3
open BidirectionalUtils
open Compatibility

let rec string_of_sexp sexp = 
	match sexp with
	| Sexp.List sexps -> "L["^(BatList.fold_left (fun acc sexp -> acc ^ " " ^ (string_of_sexp sexp)) "" sexps) ^ "]"
	| Sexp.Atom s -> "A:" ^ (*s*) (Sexp.to_string sexp)

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
	
let rec sexp_to_cex sexp = 
	match sexp with 
	| Sexp.List sexps' ->
		let _ = assert ((BatList.length sexps') >= 1) in  
		let op = Sexp.to_string (BatList.nth sexps' 0) in
		let sexps' = (BatList.remove_at 0 sexps') in 
		let children = 
			BatList.map (fun sexp' -> sexp_to_cex sexp') sexps'
		in  
		Function (op, children, Grammar.ret_type_of_op (Grammar.FuncRewrite (op, [])))
	| Sexp.Atom s ->
		sexp_to_const sexp 	

let identifier = ref "_"
let do_enumeration = ref false
let synth_inv = ref false

(* make expr to get counter-example with Z3 *)
let rec plug_in expr target_function_name cex_in_map (param2sig, sig_list) =
	match expr with
	| Const _ -> expr
	| Var (id, _) -> BatMap.find id cex_in_map 
	| Function (op, exprs, ty) -> 
		if op = target_function_name then
			let now_sig = BatMap.find exprs param2sig in
			let _, param_idx = 
				BatList.fold_left (fun (found, idx) sig_in -> 
					if found then (found, idx)
					else if now_sig = sig_in then (true, idx)
					else (false, idx + 1)
				) (false, 0) sig_list
			in
			Var(target_function_name ^ !identifier ^ (string_of_int param_idx), ty)
		else
			Function (op, BatList.map (fun e -> plug_in e target_function_name cex_in_map (param2sig, sig_list)) exprs, ty)
	| _ -> assert false (* Param *)

type t = (Exprs.expr) list
let empty_spec : t = []

(* constraints that consist of logical spec *)
let spec = ref empty_spec
(* all possible parameters of target function *)
let target_params : (Exprs.expr list) BatSet.t ref = ref BatSet.empty

let add_constraint e target_function_name = 
	let _ = spec := (e :: !spec) in (* add constraints to spec *)
	(* add parameters of target_function to target_params *)
	let temporary_params = ref BatSet.empty in
	let rec find_params e target_function_name =
		match e with
		| Function (op, exprs, _) -> 
			if op = target_function_name then
				let _ = target_params := BatSet.add exprs !target_params in
				temporary_params := BatSet.add exprs !temporary_params
			else
				BatList.iter (fun e -> find_params e target_function_name) exprs
		| _ -> ()
	in
	let _ = find_params e target_function_name in 
	if ((BatSet.cardinal !temporary_params) >= 2) then
		do_enumeration := true
	else 
		()

let trivial_constraint = Const (get_trivial_value Bool)
let pre_constraint = ref trivial_constraint
let trans_constraint = ref trivial_constraint
let post_constraint = ref trivial_constraint
let synth_inv = ref false

let add_pre_constraint e = 
	pre_constraint := e

let add_trans_constraint e =
	trans_constraint := e

let add_post_constraint e =
	post_constraint := e

let forall_var_map : (string, Exprs.expr) BatMap.t ref =
	(* name -> Var *) 
	ref BatMap.empty

let string_of_logical_spec logical_spec = 
	string_of_list string_of_expr logical_spec

(* parameter -> var *)
let rec resolve_expr sol target_function_name expr  = 
	match expr with
	| Function (op, exprs, ty) -> 
		if op = target_function_name then
		begin 
			let param2var = 
				BatList.fold_left (fun acc var ->
					let ty = type_of_expr var in
					let param = Param(BatMap.cardinal acc, ty) in 
					BatMap.add param var acc  
				) BatMap.empty exprs
			in
			change_param_to_var param2var sol
		end
		else Function (op, BatList.map (resolve_expr sol target_function_name) exprs, ty)
	| _ -> expr

(* string -> ((string, expr) BatMap.t) Option *)
let process_z3query z3query =
	let ctx = Z3.mk_context	[("model", "true"); ("proof", "false")] in
	let exprSMT = Z3.SMT.parse_smtlib2_string ctx z3query [] [] [] [] in (* Z3.AST.ASTVector.ast_vector *)
	let sat = Z3.AST.ASTVector.to_expr_list exprSMT in (* Z3.Expr.expr list *)
	let solver = (Z3.Solver.mk_solver ctx None) in (* Z3.Solver.solver *)
	(Z3.Solver.add solver sat);
	let q = (Z3.Solver.check solver []) in (* ZMT.Solver.status *)
	if !do_enumeration then 
		begin
		match q with
		| UNSATISFIABLE -> None
		| SATISFIABLE -> Some (BatMap.empty) 
		| UNKNOWN -> assert false
		end
	else
		let cex_var_map_opt = (
		match q with
		| UNSATISFIABLE -> None
		| UNKNOWN -> assert false
		| SATISFIABLE -> (
			(* can get counter-example *)
			let model_opt = Z3.Solver.get_model solver in
			match model_opt with
			| None -> assert false
			| Some model ->
				(* ex. (define-fun arg_0 () Bool false) (define-fun arg_2 () Bool true) (define-fun arg_1 () Bool false) *)
				let decls = Z3.Model.get_decls model in (* vs. get_func_decls - only function delcarations *)
				let name2expr = BatList.fold_right (fun decl acc -> 
					let name = Z3.Symbol.to_string (Z3.FuncDecl.get_name decl) in (* ex. arg0 *)
					let interp_opt = Z3.Model.get_const_interp model decl in (* ex. false *)
					match interp_opt with
					| None -> assert false
					| Some interp -> 
						BatMap.add name interp acc
				) decls BatMap.empty in
				(* (string, const) BatMap.t *)
				let cex_var_map = BatMap.foldi (fun id z3expr acc ->
					try
						let sexp = Parsexp.Single.parse_string_exn (Z3.Expr.to_string z3expr) in
						BatMap.add id (Const (List.hd (evaluate_expr_faster [[CInt 0]] (sexp_to_cex sexp)))) acc
					(* don't care term *)
					with _ -> BatMap.add id (Const (get_trivial_value (type_of_expr (BatMap.find id !forall_var_map)))) acc
				) name2expr BatMap.empty in
				Some (cex_var_map)
			)
		)
		in 
		cex_var_map_opt

let rec make_cex_in target_function_name cex_in_map expr =
	match expr with
	| Function (op, exprs, ty) ->
		if op = target_function_name then
			let rec resolve_var_to_const expr =
				match expr with
				| Var (id, _) -> BatMap.find id cex_in_map
				| Function (op, exprs, ty) -> 
					Function (op, BatList.map resolve_var_to_const exprs, ty)
				| _ -> expr
			in
			let resolved = BatList.map resolve_var_to_const exprs in
			[BatList.map (fun e -> (List.hd (evaluate_expr_faster [[CInt 0]] e))) resolved]
		else 
			BatList.fold_left (fun acc e -> 
				acc @ (make_cex_in target_function_name cex_in_map e)
			) [] exprs
	| _ -> []

let get_counter_example sol target_function_name args_map old_spec = 
	if !spec = [] then 
		if !pre_constraint = trivial_constraint || !trans_constraint = trivial_constraint || !post_constraint = trivial_constraint then  
			None (* can't found logical spec *)
		else (
			(* invariant synthesis *)
			(* z3 query for pre-f, post-f *)
			let params_str_not_primed = 
				begin
					BatMap.fold (fun var acc ->
						match var with
						| Var (id, ty) -> 
							if id.[(String.length id) - 1] = '!' then acc
							else 
								Printf.sprintf "%s\n(declare-const %s %s)" 
								acc id (string_of_type ~z3:true ty)
						| _ -> assert false
					) !forall_var_map ""
				end
			in
			(* z3 query for trans-f *)
			let params_str = 
				begin
					BatMap.fold (fun var acc ->
						match var with
						| Var (id, ty) ->
							Printf.sprintf "%s\n(declare-const %s %s)" 
							acc id (string_of_type ~z3:true ty)
						| _ -> assert false
					) !forall_var_map ""
				end
			in 
			let resolved_pre = resolve_expr sol target_function_name !pre_constraint in
			let resolved_post	= resolve_expr sol target_function_name !post_constraint in
			let resolved_trans = resolve_expr sol target_function_name !trans_constraint in
			let pre_z3query = params_str_not_primed ^ (Printf.sprintf "\n(assert (not %s))" (Exprs.string_of_expr resolved_pre)) in
			let post_z3query = params_str_not_primed ^ (Printf.sprintf "\n(assert (not %s))" (Exprs.string_of_expr resolved_post)) in
			let trans_z3query = params_str ^ (Printf.sprintf "\n(assert (not %s))" (Exprs.string_of_expr resolved_trans)) in
			let pre_opt = process_z3query pre_z3query in
			let post_opt = process_z3query post_z3query in
			let trans_opt = process_z3query trans_z3query in
			(* STEP 01 : check if pre-constraint can give counter-example *)
			if (Option.is_some pre_opt) then (
				match pre_opt with
				| Some cex_var_map -> (
					let cex_in = make_cex_in target_function_name cex_var_map !pre_constraint in
					assert ((BatList.length cex_in) = 1);
					let cex_in = BatList.hd cex_in in
					Some (add_strong_spec cex_in true old_spec)
				)
				| None -> assert false
			)
			(* STEP 02 : check if post-constraint can give counter-example *)
			else if (Option.is_some (process_z3query post_z3query)) then (
				match post_opt with
				| Some cex_var_map -> (
					let cex_in = make_cex_in target_function_name cex_var_map !post_constraint in
					assert ((BatList.length cex_in) = 1);
					let cex_in = BatList.hd cex_in in
					Some (add_strong_spec cex_in false old_spec)
				)
				| None -> assert false
			)
			(* STEP 03 : check if trans-constraint can give counter-example *)
			else if (Option.is_some (process_z3query trans_z3query)) then (
				(* Some (BatSet.empty) *)
				match trans_opt with
				| Some cex_var_map -> (
					let cex_in = make_cex_in target_function_name cex_var_map !trans_constraint in
					assert ((BatList.length cex_in) = 2);
					(* always give two counter-examples. x = x' doesn't happen. *)
					let (l, l') =
					if (
						let tmp = BatList.hd cex_in in
						let alt_spec = BatList.map (fun e -> [e]) tmp in
						List.hd (evaluate_expr_faster alt_spec sol) 
						|> get_concrete_bool
					)
					then (BatList.nth cex_in 0, BatList.nth cex_in 1)
					else (BatList.nth cex_in 1, BatList.nth cex_in 0)
					in	
					Some (add_weak_spec [l;l'] old_spec)
				)
				| None -> assert false
			)
			else None
		)
	else 
		(* STEP 01 : make logical spec to one expression (combine by 'and') *)
		(* let combined = BatList.fold_left (fun acc_expr e ->
				(* STEP 02 : resolve target function *)
				Function ("and", [acc_expr; (resolve_expr sol target_function_name args_map e)], Bool)
			) (resolve_expr sol target_function_name args_map (List.hd !spec)) (List.tl !spec)
		in *)
		let combined_spec = BatList.fold_left (fun acc_expr e -> 
			Function ("and", [acc_expr; e], Bool)
		) (List.hd !spec) (List.tl !spec) in
		(* args_map : string -> Expr.Param : x1 -> Param(0, Int) *)
		(* param2var : Expr.Param -> Expr.Var : Param(0, Int) -> Var(x1, Int) *)
		(* let param2var = 
			BatMap.foldi (fun id param_expr acc ->
				let ty = type_of_expr param_expr in 
				BatMap.add param_expr (Var(id, ty)) acc  
			) args_map BatMap.empty
		in *)
		(* print_endline ("combined_spec : " ^ (string_of_expr combined_spec)); *)
		let combined = resolve_expr sol target_function_name combined_spec in
		(* print_endline ("combined : " ^ (string_of_expr combined)); *)
		(* STEP 03 : make Z3 query *)
		let params_str = 
			begin
				BatMap.fold (fun var acc ->
					match var with
					| Var (id, ty) -> 
						Printf.sprintf "%s\n(declare-const %s %s)" 
						acc id (string_of_type ~z3:true ty)
					| _ -> assert false
				) !forall_var_map ""
			end
		in
		let z3query = params_str ^ (Printf.sprintf "\n(assert (not %s))" (Exprs.string_of_expr combined)) in
		let cex_var_map_opt = process_z3query z3query in
		(* STEP 04 : get counter-example *)
		if !do_enumeration then
			Some ([])
		else 
		let cex = 
		match cex_var_map_opt with
		| None -> None
		| Some cex_var_map -> (
			let (param2sig, sig_list) = 
				BatSet.fold (fun param (acc_map, acc_list) ->
					let sig_in = BatList.map (fun e ->
						let plugged = plug_in e "" cex_var_map (BatMap.empty, []) in
						List.hd (evaluate_expr_faster [[CInt 0]] plugged)
					) param in
					(BatMap.add param sig_in acc_map, sig_in :: acc_list)
				) !target_params (BatMap.empty, [])
			in
			let combined = plug_in combined_spec target_function_name cex_var_map (param2sig, sig_list) in
			(* print_endline ("combined : " ^ (string_of_expr combined)); *)
			let _, params_str = 
				begin
					BatList.fold_left (fun (idx, acc) sig_in ->
						let ty = Grammar.type_of_nt Grammar.start_nt in
						(idx + 1, Printf.sprintf "%s\n(declare-const %s %s)" 
						acc (target_function_name ^ !identifier ^ (string_of_int idx)) (string_of_type ~z3:true ty))
					) (0, "") sig_list
				end
			in
			let z3query = params_str ^ (Printf.sprintf "\n(assert %s)" (Exprs.string_of_expr combined)) in
			let map_opt = process_z3query z3query in
			match map_opt with
			| None -> assert false
			| Some cex_var_map -> (
				let new_spec =
					BatMap.foldi (fun sig_id const acc ->
						let id_parse  = 
							String.sub sig_id 
							((String.length target_function_name) + (String.length !identifier) ) 
							((String.length sig_id) - ((String.length target_function_name) + (String.length !identifier)))
						in
						let sig_idx = int_of_string id_parse in
						let sig_in = List.nth sig_list sig_idx in
						match const with
						| Const c -> (sig_in, c)::acc
						| _ -> assert false
				)	cex_var_map old_spec in
				(* print_endline ("cex_all : " ^ (string_of_set (fun (sig_in, sig_out) -> 
					(string_of_list string_of_const sig_in) ^ " -> " ^ (string_of_const sig_out)) cex_all)); *)
				(* print_endline ("new_spec : " ^ (Specification.string_of_io_spec new_spec)); *)
				Some (new_spec)
			)
		)
		in
		cex
;;

let add_trivial_examples target_function_name args_map old_spec =
	if !spec = [] && (!pre_constraint = trivial_constraint || !trans_constraint = trivial_constraint || !post_constraint = trivial_constraint) then  
		None
	else 
		let trivial_sol = 
			Exprs.Const (Exprs.get_trivial_value (Grammar.type_of_nt Grammar.start_nt))
		in
		let exp_opt = get_counter_example trivial_sol target_function_name args_map old_spec in
		match exp_opt with
		| None -> 
			let cex_in =
				BatMap.fold (fun param cex_in ->
					match param with
					| Param (pos, ty) ->
						BatList.modify_at pos (fun _ -> 
							(Exprs.get_trivial_value ty)
						) cex_in
					| _ -> assert false
				) args_map (BatList.make (BatMap.cardinal args_map) (CInt 0))
			in
			let cex_out =
				match trivial_sol with
				| Const c -> c
				| _ -> assert false
			in
			Some ([(cex_in, cex_out)])
		| _ -> exp_opt