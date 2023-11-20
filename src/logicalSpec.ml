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
				change_param_to_var param2var expr
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
			) (List.hd !spec) (List.tl !spec)
		in
		(* STEP 03 : make Z3 query *)
		(* STEP 04 : get cex-in as counter example *)
		None

let add_trivial_examples iospec target_function_name args_map =
	let trivial_sol = 
		Exprs.Const (Exprs.get_trivial_value (Grammar.type_of_nt Grammar.start_nt))
	in
	get_counter_example trivial_sol iospec target_function_name args_map