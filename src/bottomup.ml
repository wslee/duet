open Exprs
open Grammar
open Vocab

let rec propagation i grammar nts acc =  
  let nts_to_fun = BatSet.fold (fun nt nt2fun -> 
    let rules = BatMap.find nt grammar in
    let fun_plus = BatSet.fold (fun rule funs ->
      match rule with
      | NTRewrite _ -> BatSet.union (BatMap.find rule nt2fun) funs
      | _ -> funs
      ) rules (BatMap.find nt nt2fun) in
    BatMap.add nt fun_plus nt2fun
    ) nts acc in
  if i = (BatSet.cardinal nts) then nts_to_fun
  else propagation (i+1) grammar nts nts_to_fun
;;

(* return : (NTRewrite, Exprs.expr BatSep.t) BatMap.t *)
let get_level_1 grammar nts =
  let level_1 = BatSet.fold (fun ele acc ->
      let rules = BatMap.find ele grammar in
      let level_1 = BatSet.fold (fun ele acc ->
        match ele with
        | ExprRewrite expr -> BatSet.add expr acc
        | _ -> acc
      ) rules BatSet.empty in
      BatMap.add ele level_1 acc
    ) nts BatMap.empty in
  propagation 1 grammar nts level_1
;;

(* partition *)
(* TODO : use cache to solve with DP *)
let rec p n k =
  if k = 1 then [[n]]
  else
    let rec aux i =
      let prev = p (n-i) (k-1) in
      let prev = List.map (fun ele -> i::ele) prev in
      if i = (n-k+1) then prev
      else prev @ aux (i+1)
    in aux 1
;;


let rec level_up (lvl:int) (grammar : (rewrite, rewrite BatSet.t) BatMap.t) (nts : rewrite BatSet.t) (lvl2fun: (int, (rewrite, expr BatSet.t) BatMap.t) BatMap.t) spec =
  let nts_to_fun = BatSet.fold (fun nt acc ->
    let rules = BatMap.find nt grammar in
    let funs = BatSet.fold (fun rule fun_set ->
        match rule with
        | FuncRewrite (op, children) -> (
          let len = BatList.length children in
          (* let _ = print_endline ((string_of_int lvl)^" level -> "^op^" "^(string_of_int len)) in *)
          if lvl-1 < len then fun_set
          else (
            let partition = p (lvl-1) len in
            BatList.fold_right (fun part acc ->
              let nt_lvl = BatList.combine children part in 
              let children_cardinal = BatList.map (fun (nt, lvl) -> BatMap.find nt (BatMap.find lvl lvl2fun)) nt_lvl in
              (* let _ = print_endline ((string_of_list (string_of_set string_of_expr)) children_cardinal) in *)
              if (BatList.for_all (fun ele -> not (BatSet.is_empty ele)) children_cardinal) then
                let rec get_children cardinals = (
                  match cardinals with
                  | [] -> [[]]
                  | cardinal::tl ->
                    let children_ext = get_children tl in
                    BatSet.fold (fun child acc -> 
                      (BatList.fold_right (fun ele acc -> 
                        (child::ele)::acc) children_ext acc)
                      @ acc
                    ) cardinal []
                  ) in
                let children_ext = get_children children_cardinal in
                (* let _ = print_endline ((string_of_list (string_of_list string_of_expr)) children_ext) in *)
                let nt_type = BatMap.find nt !Grammar.nt_type_map in
                BatList.fold_right (fun children acc -> 
                  try (
                    let f = Function (op, children, nt_type) in
                    if (BatSet.is_empty (BatSet.intersect (BatSet.map (fun f' -> compute_signature spec f') acc) (BatSet.singleton (compute_signature spec f)))) then 
                      BatSet.add f acc 
                    else
                      acc
                  ) with _ -> acc 
                ) children_ext acc
              else
                acc
            ) partition fun_set
          )
        )
        | _ -> fun_set
      ) rules BatSet.empty in
    BatMap.add nt funs acc
    ) nts BatMap.empty in
    propagation 1 grammar nts nts_to_fun
;;

(* for PBE *)
let pruning lvl2fun spec nt2fun nts =
  BatMap.mapi (fun nt funs ->
    BatSet.filter (fun f -> 
      let sigs = compute_signature spec f in
      let old_sigs = BatMap.foldi (fun lvl nt2fun acc -> 
        let funs = BatMap.find nt nt2fun in
        BatSet.fold (fun f acc -> 
          BatSet.add (compute_signature spec f) acc
        ) funs acc
      ) lvl2fun BatSet.empty in
      BatSet.is_empty (BatSet.intersect old_sigs (BatSet.singleton sigs))
    ) funs
  ) nt2fun
;;
(* TODO : pruning, evaluate *)

let next_step lvl2fun lvl grammar nts spec = 
  BatMap.add lvl (
    pruning lvl2fun spec (level_up lvl grammar nts lvl2fun spec) nts
  ) lvl2fun
;;

let synthesis (macro_instantiator, target_function_name, args_map, grammar, forall_var_map, spec) =
  let nts = BatMap.foldi (fun nt rules s -> (BatSet.add nt s)) grammar BatSet.empty in
  let nt_to_function = get_level_1 grammar nts in
  let start_nt = BatList.hd (BatSet.to_list nts) in
  let level_to_function = BatMap.singleton 1 nt_to_function in
  let level_to_function = next_step level_to_function 2 grammar nts spec in
  (* let level_to_function = next_step level_to_function 3 grammar nts spec in *)
  (* let level_to_function = next_step level_to_function 4 grammar nts spec in *)
  level_to_function
  (* let expr = BatList.hd (BatSet.elements (BatMap.find start_nt (BatMap.find 3 level_to_function))) in *)
  (* let _ = print_endline (string_of_expr expr) in *)
  (* compute_signature spec expr *)
;;
