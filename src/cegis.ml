open Bottomup
open Oracle

open Exprs
open Grammar
open Vocab

let rec cegis (macro_instantiator, target_function_name, args_map, grammar, forall_var_map, spec) =
  let generater = Bottomup.synthesis in
  (* let generater = Tester.synthesis in *)
  let verifier = Oracle.verify in

  let sol = generater (macro_instantiator, target_function_name, args_map, grammar, forall_var_map, spec) in
  let cex_opt = verifier sol spec in
  match cex_opt with
  | None -> sol
  | Some cex -> cegis (macro_instantiator, target_function_name, args_map, grammar, forall_var_map, cex::spec)
;;