open Sexplib
open Vocab
open Exprs
open Z3
open BidirectionalUtils

type t = (Exprs.expr) list
let empty_spec : t = []

(* constraints that consist of logical spec *)
let spec = ref empty_spec
let add_constraint e = 
	spec := (e :: !spec)

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
					| -> assert false
				) !forall_var_map ""
			end
		in
		let z3query = params_str ^ (Printf.sprintf "\n(assert (not %s))" Exprs.string_of_expr combined) in
		(* process query *)
    let exprSMT = Z3.SMT.parse_smtlib2_string ctx str [] [] [] [] in (* Z3.AST.ASTVector.ast_vector *)
    let sat = Z3.AST.ASTVector.to_expr_list exprSMT in (* Z3.Expr.expr list *)
    let solver = (Z3.Solver.mk_solver ctx None) in (* Z3.Solver.solver *)
  	(Z3.Solver.add solver sat);
    let q = (Z3.Solver.check solver []) in (* ZMT.Solver.status *)
		(* STEP 04 : get cex-in as counter example *)
		None

let add_trivial_examples iospec target_function_name args_map =
	let trivial_sol = 
		Exprs.Const (Exprs.get_trivial_value (Grammar.type_of_nt Grammar.start_nt))
	in
	get_counter_example trivial_sol iospec target_function_name args_map