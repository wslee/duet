open Grammar
open Exprs
open Vocab
open Witness
open BidirectionalUtils

let synthesis (macro_instantiator, target_function_name, args_map, grammar, forall_var_map, spec) =
	let nts = BatMap.foldi (fun nt rules s -> BatSet.add nt s) grammar BatSet.empty in
  let nt_to_sigs : (rewrite, signature BatSet.t) BatMap.t = 
		BatSet.fold (fun nt m -> BatMap.add nt BatSet.empty m) nts BatMap.empty 
	in
  let nt_to_exprs : (rewrite, (expr * int) BatSet.t) BatMap.t = 
		BatSet.fold (fun nt m -> BatMap.add nt BatSet.empty m) nts BatMap.empty 
	in
  let nt_sig_to_expr : (rewrite * signature, expr) BatMap.t = BatMap.empty in
	let desired_sig = List.map (fun (inputs, output) -> output) spec in
  let nt_rule_list = get_nt_rule_list grammar in
  let rec iter sz ((nt_to_sigs, nt_to_exprs, nt_sig_to_expr) as maps) =
	  print_endline (string_of_int sz);
    let start = Sys.time () in
    let ((nt_to_sigs, nt_to_exprs, nt_sig_to_expr) as maps) = 
      get_sigs_of_size desired_sig spec maps nt_rule_list (sz, sz+1) in
    print_endline (string_of_float (Sys.time () -. start));	
    if BatMap.mem (Grammar.start_nt, desired_sig) nt_sig_to_expr then
      BatMap.find (Grammar.start_nt, desired_sig) nt_sig_to_expr
    else
      iter (sz+1) maps
  in 
  iter 1 (nt_to_sigs, nt_to_exprs, nt_sig_to_expr)