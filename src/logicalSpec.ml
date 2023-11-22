open Sexplib
open Vocab
open Exprs
open Z3
open BidirectionalUtils

type t = (Exprs.expr) list
let empty_spec : t = []

(* constraints that consist of logical spec *)
let spec = ref empty_spec
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

let rec resolve_expr sol target_function_name args_map expr  = 
	match expr with
	| Function (op, exprs, ty) -> 
		begin
			if op = target_function_name then
				let param2var = 
					BatMap.foldi (fun id param_expr acc ->
						let ty = type_of_expr param_expr in 
						BatMap.add param_expr (Var(id, ty)) acc  
					) args_map BatMap.empty
				in
				change_param_to_var param2var sol
			else
				Function (op, BatList.map (resolve_expr sol target_function_name args_map) exprs, ty)
		end
	| _ -> expr

let get_counter_example sol iospec target_function_name args_map = 
	if !spec = [] then None (* can't found logical spec *)
	else 
		let ctx = Z3.mk_context	[("model", "true"); ("proof", "false")] in
		(* STEP 01 : make logical spec to one expression (combine by 'and') *)
		let combined = BatList.fold_left (fun acc_expr e ->
				(* STEP 02 : resolve target function *)
				Function ("and", [acc_expr; (resolve_expr sol target_function_name args_map e)], Bool)
			) (resolve_expr sol target_function_name args_map (List.hd !spec)) (List.tl !spec)
		in
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
		match q with
    | UNSATISFIABLE -> None
    | UNKNOWN -> assert false
    | SATISFIABLE -> 
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
        let cex_var_map = BatMap.foldi (fun id _ acc ->
					let sexp = BatMap.find id name2expr in
					BatMap.add id (Specification.sexp_to_const (Sexp.Atom (Z3.Expr.to_string sexp))) acc
				) !forall_var_map BatMap.empty in
				print_endline ("cex_var_map : " ^ (string_of_map (fun e -> e) string_of_const cex_var_map));
				None
;;

let add_trivial_examples iospec target_function_name args_map =
	let trivial_sol = 
		Exprs.Const (Exprs.get_trivial_value (Grammar.type_of_nt Grammar.start_nt))
	in
	get_counter_example trivial_sol iospec target_function_name args_map