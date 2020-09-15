open Vocab
open Exprs
open BidirectionalUtils

(** Propositional theory *)
let witness available_height nt_sigs (int_sigs, bv_sigs, string_sigs, bool_sigs) rule output_sig arg_sigs =
	let op = Grammar.op_of_rule rule in
	let _ = assert ((type_of_signature output_sig) = Bool) in  
	if (String.compare op "and") = 0 then
		if (BatList.length arg_sigs) = 0 then
			BatSet.filter (fun arg0_sig ->
				BatList.for_all (fun (arg0_const, output_const) ->
					(is_abstract_bool output_const) || 
					(let arg0_v = get_concrete_bool arg0_const in
					 let output_v = get_concrete_bool output_const in
					 ((not (output_v = true)) || (arg0_v = true)))
				) (BatList.combine arg0_sig output_sig)
			) nt_sigs
		else
			let arg0_sig = List.nth arg_sigs 0 in
			BatSet.filter (fun arg1_sig ->
				BatList.for_all2 (fun (arg0_const, arg1_const) output_const ->
					(is_abstract_bool output_const) ||
					(let arg0_v = get_concrete_bool arg0_const in
					 let arg1_v = get_concrete_bool arg1_const in
					 let output_v = get_concrete_bool output_const in
					 (arg0_v && arg1_v) = output_v)
				) (BatList.combine arg0_sig arg1_sig) output_sig
			) nt_sigs
	else if (String.compare op "or") = 0 then
		if (BatList.length arg_sigs) = 0 then
			BatSet.filter (fun arg0_sig ->
				BatList.for_all (fun (arg0_const, output_const) ->
					(is_abstract_bool output_const) ||
					(let arg0_v = get_concrete_bool arg0_const in
					 let output_v = get_concrete_bool output_const in
					 ((not (output_v = false)) || (arg0_v = false)))
				) (BatList.combine arg0_sig output_sig)
			) nt_sigs
		else
			let arg0_sig = List.nth arg_sigs 0 in
			BatSet.filter (fun arg1_sig ->
				BatList.for_all2 (fun (arg0_const, arg1_const) output_const ->
					(is_abstract_bool output_const) ||
					(let arg0_v = get_concrete_bool arg0_const in
					 let arg1_v = get_concrete_bool arg1_const in
					 let output_v = get_concrete_bool output_const in
					 (arg0_v || arg1_v) = output_v)
				) (BatList.combine arg0_sig arg1_sig) output_sig
			) nt_sigs
	else if (String.compare op "xor") = 0 then
		if (BatList.length arg_sigs) = 0 then 
			BatSet.filter (fun arg0_sig ->
				let arg1_sig = fun_apply_signature "xor" [arg0_sig; output_sig] in 
				BatSet.mem arg1_sig bool_sigs
			) nt_sigs
		else
			let arg0_sig = List.nth arg_sigs 0 in
			BatSet.filter (fun arg1_sig ->
				BatList.for_all2 (fun (arg0_const, arg1_const) output_const ->
					(is_abstract_bool output_const) || 
					(let arg0_v = get_concrete_bool arg0_const in
					 let arg1_v = get_concrete_bool arg1_const in
					 let output_v = get_concrete_bool output_const in
					 (arg0_v <> arg1_v) = output_v)
				) (BatList.combine arg0_sig arg1_sig) output_sig
			) nt_sigs
			(* let arg0_sig = List.nth arg_sigs 0 in *)
			(* BatList.fold_left (fun acc (arg0_const, output_const) ->       *)
			(* 	let arg0_v = get_bool arg0_const in                          *)
			(* 	let output_v = get_bool output_const in                      *)
			(* 	acc @ [CBool (arg0_v <> output_v)]                           *)
			(* ) [] (BatList.combine arg0_sig output_sig) |> BatSet.singleton *)
	else if (String.compare op "not") = 0 then
		BatSet.filter (fun arg0_sig ->
			BatList.for_all (fun (arg0_const, output_const) ->
				(is_abstract_bool output_const) ||  
				(let arg0_v = get_concrete_bool arg0_const in
				 let output_v = get_concrete_bool output_const in
				 (not arg0_v) = output_v)
			) (BatList.combine arg0_sig output_sig)
		) nt_sigs
			(* BatList.fold_left (fun acc output_const -> *)
			(* 	let output_v = get_bool output_const in  *)
			(* 	acc @ [(CBool (not output_v))]           *)
			(* ) [] output_sig |> BatSet.singleton        *)
	else 
		failwith (Printf.sprintf "unsupported op: %s" op)