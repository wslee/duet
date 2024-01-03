open Sexplib
open Vocab
open Exprs
open Z3
open BidirectionalUtils

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
	let rec find_params e target_function_name =
		match e with
		| Function (op, exprs, _) -> 
			if op = target_function_name then
				target_params := BatSet.add exprs !target_params
			else
				BatList.iter (fun e -> find_params e target_function_name) exprs
		| _ -> ()
	in
	find_params e target_function_name	

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

let get_counter_example sol iospec target_function_name args_map = 
	if !spec = [] then None (* can't found logical spec *)
	else 
		let ctx = Z3.mk_context	[("model", "true"); ("proof", "false")] in
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
		print_endline ("combined_spec : " ^ (string_of_expr combined_spec));
		let combined = resolve_expr sol target_function_name combined_spec in
		print_endline ("combined : " ^ (string_of_expr combined));
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
		(* process query *)
    let exprSMT = Z3.SMT.parse_smtlib2_string ctx z3query [] [] [] [] in (* Z3.AST.ASTVector.ast_vector *)
    let sat = Z3.AST.ASTVector.to_expr_list exprSMT in (* Z3.Expr.expr list *)
    let solver = (Z3.Solver.mk_solver ctx None) in (* Z3.Solver.solver *)
  	(Z3.Solver.add solver sat);
    let q = (Z3.Solver.check solver []) in (* ZMT.Solver.status *)
		(* STEP 04 : get cex-in as counter example *)
		let cex_var_map_opt = 
		match q with
    | UNSATISFIABLE -> None
    | UNKNOWN -> assert false
    | SATISFIABLE ->
		begin  
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
        let cex_var_map = BatMap.foldi (fun id _ acc ->
					let z3expr = BatMap.find id name2expr in
					let sexp = Parsexp.Single.parse_string_exn (Z3.Expr.to_string z3expr) in
					BatMap.add id (Const (List.hd (evaluate_expr_faster [[CInt 0]] (sexp_to_cex sexp)))) acc
					(* BatMap.add id (Const (CInt (-2))) acc *)
				) !forall_var_map BatMap.empty in
				print_endline ("cex_var_map : " ^ (string_of_map (fun e -> e) string_of_expr cex_var_map));
				Some (cex_var_map)
		end
		in 
		let cex = 
		match cex_var_map_opt with
		| None -> None
		| Some cex_var_map ->
		begin
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
			print_endline ("combined : " ^ (string_of_expr combined));
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
			(* process query *)
			let exprSMT = Z3.SMT.parse_smtlib2_string ctx z3query [] [] [] [] in (* Z3.AST.ASTVector.ast_vector *)
			let sat = Z3.AST.ASTVector.to_expr_list exprSMT in (* Z3.Expr.expr list *)
			let solver = (Z3.Solver.mk_solver ctx None) in (* Z3.Solver.solver *)
			(Z3.Solver.add solver sat);
			let q = (Z3.Solver.check solver []) in (* ZMT.Solver.status *)
			match q with
			| SATISFIABLE -> 
			begin
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
					let cex_all = 
						BatMap.foldi (fun sig_id z3expr acc ->
							let id_parse  = 
								String.sub sig_id 
								((String.length target_function_name) + (String.length !identifier) ) 
								((String.length sig_id) - ((String.length target_function_name) + (String.length !identifier)))
							in
							print_endline ("id_parse : " ^ id_parse);
							let sig_idx = int_of_string id_parse in
							let sig_in = List.nth sig_list sig_idx in
							let sexp = Parsexp.Single.parse_string_exn (Z3.Expr.to_string z3expr) in
					 		let sig_out = List.hd (evaluate_expr_faster [[CInt 0]] (sexp_to_cex sexp)) in 
							BatSet.add (sig_in, sig_out) acc
					)	name2expr BatSet.empty in
					print_endline ("cex_all : " ^ (string_of_set (fun (sig_in, sig_out) -> 
						(string_of_list string_of_const sig_in) ^ " -> " ^ (string_of_const sig_out)) cex_all));
					Some (cex_all)
			end
			| _ -> assert false
		end 
		in 
		cex
;;

let add_trivial_examples iospec target_function_name args_map =
	let trivial_sol = 
		Exprs.Const (Exprs.get_trivial_value (Grammar.type_of_nt Grammar.start_nt))
	in
	get_counter_example trivial_sol iospec target_function_name args_map