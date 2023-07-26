open Exprs
open Grammar
open Vocab

(* AST node *)
type node = 
  | Leaf of expr
  | NonLeaf of int * int list (* func id, children *)
;;

let nidx = ref 0;;
let idx2node = ref BatMap.empty;; (* (int, node) BatMap.t *)

let fidx = ref 0;;
let idx2func = ref BatMap.empty;; (* (int, (FuncRewrite, exprtype)) BatMap.t *)
let func2idx = ref BatMap.empty;; (* (FuncRewrite, int) BatMap.t *)

let rec expr_of_node x =
  match x with
  | Leaf expr -> expr
  | NonLeaf (idx, children) -> (
    let func, ty = BatMap.find idx !idx2func in
    match func with
    | FuncRewrite (op, _) -> Function (op, BatList.map expr_of_idx children, ty)
    | _ -> failwith "node2expr : not FuncRewrite"
  )
and expr_of_idx i = expr_of_node (BatMap.find i !idx2node);;

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

(* TODO : optimize with change expression [0, 1, 2, ... , n] to Range(0, n) *)
let idxes_of_size sz grammar nts sz2idxes spec = 
  if sz = 1 then
    let nt2idxes = BatSet.fold (fun nt nt2idxes ->
      let rules = BatMap.find nt grammar in
      let idxes = BatSet.fold (fun rule idxes ->
        match rule with
        | ExprRewrite expr -> (
          let idx = !nidx in
          let _ = nidx := !nidx + 1 in
          let _ = idx2node := BatMap.add idx (Leaf expr) !idx2node in
          BatSet.add idx idxes
        )
        | FuncRewrite _ -> (
          let idx = !fidx in
          let _ = fidx := !fidx + 1 in
          let _ = idx2func := BatMap.add idx (rule, BatMap.find nt !Grammar.nt_type_map) !idx2func in
          let _ = func2idx := BatMap.add rule idx !func2idx in
          idxes
        )
        | _ -> idxes
      ) rules BatSet.empty in
      BatMap.add nt idxes nt2idxes
    ) nts BatMap.empty in
    BatMap.add sz nt2idxes sz2idxes
  else
    let nt2idxes = BatSet.fold (fun nt nt2idxes -> 
      let _ = print_endline ((string_of_rewrite nt) ^ (string_of_int sz)) in
      let old = ref BatSet.empty in
      let rec get_old i () =
        if i = 0 then ()
        else 
          let idxes = BatMap.find nt (BatMap.find i sz2idxes) in
          let _ = BatSet.iter (fun idx ->
            old := BatSet.add (compute_signature spec (expr_of_idx idx)) !old;
          ) idxes in
          get_old (i-1) ()
      in
      let _ = get_old (sz-1) () in
      print_endline "old_function done!";
      let rules = BatMap.find nt grammar in
      let idxes = BatSet.fold (fun rule idxes ->
        match rule with
        | FuncRewrite (op, children) -> (
          if (BatList.length children) >= sz then idxes
          else 
            let partitions = p (sz-1) (BatList.length children) in
            let idxes = BatList.fold_right (fun partition idxes ->
              let sz_x_nt = BatList.combine partition children in
              let is_all_not_empty x =
                BatList.for_all (fun (sz, nt) -> 
                  not (BatSet.is_empty (BatMap.find nt (BatMap.find sz sz2idxes)))
                ) x in            
              if is_all_not_empty sz_x_nt then
                let now = ref BatSet.empty in
                let rec get_idxes x acc () = 
                  match x with
                  | [] -> (
                    (* add function to set *)
                    let idx = !nidx in
                    let node = NonLeaf (BatMap.find rule !func2idx, acc) in
                    (* print_endline (string_of_expr (expr_of_node node)); *)
                    try (
                      let out = compute_signature spec (expr_of_node node) in
                      (* print_endline "pass"; *)
                      if BatSet.mem out !old then ()
                      else
                        old := BatSet.add out !old;
                        let _ = nidx := !nidx + 1 in
                        let _ = idx2node := BatMap.add idx node !idx2node in
                        now := BatSet.add idx !now
                    ) with _ -> ();
                    (* print_endline "get idxes done!"; *)
                  )
                  | (sz, nt)::tl -> (
                    let idxes' = BatMap.find nt (BatMap.find sz sz2idxes) in
                    BatSet.iter (fun idx -> 
                      get_idxes tl (idx::acc) ()
                    ) idxes'
                  ) in 
                let _ = get_idxes sz_x_nt [] () in
                (* print_endline "get idxes done!"; *)
                BatSet.union !now idxes
              else idxes
            ) partitions idxes in
            idxes
        )
        | _ -> idxes
      ) rules BatSet.empty in
      (* let _ = print_endline (string_of_rewrite nt) in
      let _ = print_endline (string_of_set string_of_int idxes) in *)
      BatMap.add nt idxes nt2idxes
    ) nts BatMap.empty in
    BatMap.add sz nt2idxes sz2idxes
;;

(* TODO : pruning, check if valid function (no runtime-error)  *)

let synthesis (macro_instantiator, target_function_name, args_map, grammar, forall_var_map, spec) =
  let nts = BatMap.foldi (fun nt rules s -> (BatSet.add nt s)) grammar BatSet.empty in
  let sz2idxes = idxes_of_size 1 grammar nts BatMap.empty spec in
  (* let _ = print_endline (string_of_int (BatMap.cardinal (BatMap.find 1 sz2idxes))) in *)
  let sz2idxes = idxes_of_size 2 grammar nts sz2idxes spec in
  let sz2idxes = idxes_of_size 3 grammar nts sz2idxes spec in
  let sz2idxes = idxes_of_size 4 grammar nts sz2idxes spec in
  let sz2idxes = idxes_of_size 5 grammar nts sz2idxes spec in
  let sz2idxes = idxes_of_size 6 grammar nts sz2idxes spec in
  let sz2idxes = idxes_of_size 7 grammar nts sz2idxes spec in
  let sz2idxes = idxes_of_size 8 grammar nts sz2idxes spec in
  let sz2idxes = idxes_of_size 9 grammar nts sz2idxes spec in
  (* let sz2idxes = idxes_of_size 10 grammar nts sz2idxes spec in *)
  let start_nt = BatList.hd (BatSet.to_list nts) in
  let _ = print_endline "synthesis complete" in
  sz2idxes
;;
