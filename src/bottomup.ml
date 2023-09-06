open Exprs
open Grammar
open Vocab

(* AST node *)
type node = 
  | Leaf of expr
  | NonLeaf of int * int list (* func id, children *)
;;

let nidx = ref 0;;
let idx2node = ref BatMap.empty;; (* (int, node) BatMap.t  *)

let fidx = ref 0;;
let idx2func = ref BatMap.empty;; (* (int, (FuncRewrite, exprtype)) BatMap.t *)
let func2idx = ref BatMap.empty;; (* (FuncRewrite, int) BatMap.t *)

let nt2out = ref BatMap.empty;; (* (NTRewrite, const list) BatMap.t *)
let idx2out = ref BatMap.empty;; (* (int, const list) BatMap.t *)

let nt_order = ref [];; (* NTRewrite list *)
let nt_edge = ref BatMap.empty;; (* (NTRewrite, NTRewrite BatSet.t) BatMap.t *)

let spec_out = ref [];;
let alt_time = ref 0.0;;
let alt_comp = ref 0;;
let compute_time = ref 0.0;;

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

let rec count_exprs node = 
  match node with
  | Leaf expr -> 1
  | NonLeaf (_, children) -> 
    BatList.fold_right (fun child cnt -> cnt + count_exprs (BatMap.find child !idx2node)) children 1
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

(* TODO : optimize with change expression [0, 1, 2, ... , n] to Range(0, n) *)
let idxes_of_size sz grammar nts sz2idxes spec = 
  (* print_endline (string_of_int sz); *)
  if sz = 1 then
    let _ = nidx := 0 in
    let _ = idx2node := BatMap.empty in
    let _ = fidx := 0 in 
    let _ = idx2func := BatMap.empty in 
    let _ = func2idx := BatMap.empty in
    let _ = nt2out := BatMap.empty in
    let _ = idx2out := BatMap.empty in
    let _ = spec_out := BatList.map (fun (_, y) -> y) spec in
    let nt2idxes = BatSet.fold (fun nt nt2idxes ->
      nt2out := BatMap.add nt BatSet.empty !nt2out;
      (* print_endline ((string_of_rewrite nt) ^ (string_of_int sz)); *)
      let rules = BatMap.find nt grammar in
      let idxes = BatSet.fold (fun rule idxes ->
        match rule with
        | ExprRewrite expr -> (
          let idx = !nidx in
          nidx := !nidx + 1;
          idx2node := BatMap.add idx (Leaf expr) !idx2node;
          idx2out := BatMap.add idx (compute_signature spec expr) !idx2out;
          nt2out := BatMap.add nt (BatSet.add (compute_signature spec (expr_of_idx idx)) (BatMap.find nt !nt2out)) !nt2out;
          BatSet.add idx idxes
        )
        | FuncRewrite _ -> (
          let idx = !fidx in
          fidx := !fidx + 1;
          idx2func := BatMap.add idx (rule, BatMap.find nt !Grammar.nt_type_map) !idx2func;
          func2idx := BatMap.add rule idx !func2idx;
          idxes
        )
        | _ -> idxes
      ) rules BatSet.empty in
      BatMap.add nt idxes nt2idxes
    ) nts BatMap.empty in
    BatMap.add sz nt2idxes sz2idxes
  else
    let nt2idxes = BatSet.fold (fun nt nt2idxes -> 
      (* let _ = print_endline ((string_of_rewrite nt) ^ (string_of_int sz)) in *)
      let rules = BatMap.find nt grammar in
      let idxes = BatSet.fold (fun rule idxes ->
        match rule with
        | FuncRewrite (op, children) -> (
          if (BatList.length children) >= sz then idxes
          else 
            let functype = BatMap.find nt !Grammar.nt_type_map in
            let expr_for_now = 
                Function (op, (BatList.fold_right (fun rewrite children ->
                    children @ [Param (BatList.length children, BatMap.find rewrite !Grammar.nt_type_map)]
                  ) children []),
                  functype
                )
            in
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
                    let start_alt = Sys.time () in
                    let use_new_spec = 
                      match !Options.new_spec with
                      | 0 -> false
                      | 1 -> true
                      | 2 -> 2*(BatList.length children) < (count_exprs node) - 1
                      | 3 -> (BatList.length children) < (sz - 1)
                      | _ -> false
                    in
                    (* print_endline((string_of_bool use_new_spec) ^ " -> " ^ (string_of_int (sz-1)) ^ " " ^ (string_of_int (BatList.length children))); *)
                    let new_spec = 
                      if use_new_spec then
                        BatList.map (fun x -> BatMap.find x !idx2out) acc in
                      else
                        []
                    in
                    let _ = alt_time := !alt_time +. (Sys.time () -. start_alt) in
                    let start_cpt = Sys.time () in
                    try (
                      let out = (if use_new_spec then evaluate_expr_faster else compute_signature)
                        (if use_new_spec then new_spec else spec)
                        (if use_new_spec then expr_for_now else expr_of_node node) in
                      let _ = compute_time := !compute_time +. (Sys.time () -. start_cpt) in
                      (* print_endline "pass"; *)
                      if BatSet.mem out (BatMap.find nt !nt2out) then 
                        (* let _ = print_endline ("overlapped : " ^ (string_of_expr (expr_of_node node)) ^ " -> " ^ (string_of_list string_of_const out)) in *)
                        ()
                      else
                        let _ = nt2out := BatMap.add nt (BatSet.add out (BatMap.find nt !nt2out)) !nt2out in
                        let _ = idx2out := BatMap.add idx out !idx2out in
                        let _ = nidx := !nidx + 1 in
                        let _ = idx2node := BatMap.add idx node !idx2node in
                        let _ = now := BatSet.add idx !now in
                        let _ = if use_new_spec then alt_comp := !alt_comp + 1 else () in
                        ()
                    ) with _ -> (
                      let _ = compute_time := !compute_time +. (Sys.time () -. start_cpt) in
                      ();
                    )
                    (* print_endline "get idxes done!"; *)
                  )
                  | (sz, nt)::tl -> (
                    let idxes' = BatMap.find nt (BatMap.find sz sz2idxes) in
                    BatSet.iter (fun idx -> 
                      get_idxes tl (acc @ [idx]) ()
                    ) idxes'
                  ) in 
                let _ = get_idxes sz_x_nt [] () in
                (* print_endline "get idxes done!"; *)
                (* print_endline (string_of_set string_of_expr (BatSet.map expr_of_idx !now)); *)
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
    (* print_endline (string_of_float (Sys.time () -. start_t)); *)
    BatMap.add sz nt2idxes sz2idxes
;;

let rec search sz nt is_start_nt grammar nts spec sz2idxes = 
  let tg_out = BatList.map (fun (_, y) -> y) spec in
  let trivial = Const (get_trivial_value (BatMap.find nt !Grammar.nt_type_map)) in
  let sz2idxes = if is_start_nt then idxes_of_size sz grammar nts sz2idxes spec else sz2idxes in
  let idxes = BatMap.find nt (BatMap.find sz sz2idxes) in
  let (success, func) = BatSet.fold (fun idx (success, func) ->
    if success then (success, func)
    else
      let out = BatMap.find idx !idx2out in
      if BatList.for_all (fun (x, y) -> x=y) (BatList.combine tg_out out) then
        (true, expr_of_idx idx)
      else (success, func)
  ) idxes (false, trivial) in
  if success then (success, func)
  else
    let rules = BatMap.find nt grammar in
    let (success, func) = BatSet.fold (fun rule (success, func) -> 
      if success then (success, func)
      else
        match rule with
        | NTRewrite _ -> search sz rule false grammar nts spec sz2idxes
        | _ -> (success, func)
    ) rules (success, func) in
    if success then (success, func)
    else if is_start_nt then search (sz+1) nt is_start_nt grammar nts spec sz2idxes
    else (false, trivial)
;;

let synthesis (macro_instantiator, target_function_name, args_map, grammar, forall_var_map, spec) =
  let nts = BatMap.foldi (fun nt rules s -> (BatSet.add nt s)) grammar BatSet.empty in
  (* let start_nt = BatList.hd (BatSet.to_list nts) in *)
  let (_, func) = search 1 Grammar.start_nt true grammar nts spec BatMap.empty in
  let _ = print_endline "synthesis complete" in
  func
;;

let sort nts grammar = 
  nt_order := [];
  (* inDegree *)
  let inD = ref (BatSet.fold (fun nt inD ->
    BatMap.add nt 0 inD
  ) nts BatMap.empty) in
  (* initialize *)
  nt_edge := BatSet.fold (fun nt nt_edge ->
    BatMap.add nt BatSet.empty nt_edge
  ) nts BatMap.empty;
  (* make adj-list *)
  let adj = BatMap.foldi (fun nt rules adj ->
    (* print_endline (string_of_set string_of_rewrite rules); *)
    BatSet.fold (fun rule now -> 
      match rule with
      | NTRewrite _ -> 
      begin
        (* print_endline ((string_of_rewrite nt) ^ " -> " ^ (string_of_rewrite rule)); *)
        BatSet.add (rule, nt) now (* (StartString, Start) *)
      end
      | _ -> now 
    ) rules adj
  ) grammar BatSet.empty in
  (* adj-list -> edge & inDegree *)
  (* print_endline (string_of_set (fun (a, b) -> string_of_rewrite a ^ " -> " ^ string_of_rewrite b) adj); *)
  BatSet.iter (fun (u, v) -> 
    nt_edge := BatMap.add u (BatSet.add v (BatMap.find u !nt_edge)) !nt_edge;
    inD := BatMap.add v ((BatMap.find v !inD) + 1) !inD;
  ) adj;
  (* topological sort *)
  let queue = BatMap.foldi (fun nt indegree queue ->
    if indegree = 0 then BatSet.add nt queue
    else queue  
  ) !inD BatSet.empty in
  assert (not (BatSet.is_empty queue));
  (* print_endline (string_of_map string_of_rewrite (string_of_set string_of_rewrite) !nt_edge); *)
  let rec iter queue =
    (* print_endline (string_of_set string_of_rewrite queue); *)
    BatSet.iter (fun nt ->
      nt_order := !nt_order @ [nt];
      let adj = BatMap.find nt !nt_edge in
      let next_queue = BatSet.fold (fun nt' next_queue ->
        inD := BatMap.add nt' ((BatMap.find nt' !inD) - 1) !inD;
        (* print_endline (string_of_map string_of_rewrite string_of_int !inD); *)
        if (BatMap.find nt' !inD) = 0 then 
          BatSet.add nt' next_queue
        else next_queue
      ) adj BatSet.empty in
      if BatSet.is_empty next_queue then ()
      else iter next_queue
    ) queue
  in
  iter queue;
  (* print_endline (string_of_list string_of_rewrite !nt_order); *)
  (* print_endline (string_of_map string_of_rewrite (string_of_set string_of_rewrite) !nt_edge); *)
;;

let expand nts grammar nt2idxes =
  if !nt_order = [] then 
    sort nts grammar;
  let nt2idxes_plus = nt2idxes in
  (* TODO: out expand *)
  let rec expand' order expanded = 
    match order with
    | nt::order' -> 
    begin
      let nxt = BatMap.find nt !nt_edge in
      let now_idxes = BatMap.find nt expanded in
      let now_sig = BatSet.map (fun idx ->
        BatMap.find idx !idx2out
      ) now_idxes in
      BatSet.fold (fun nt' expanded ->
        nt2out := BatMap.add nt' (BatSet.union now_sig (BatMap.find nt' !nt2out)) !nt2out;
        BatMap.add nt' (BatSet.union now_idxes (BatMap.find nt' expanded)) expanded
      ) nxt expanded |> expand' order' 
    end
    | _ -> expanded
  in
  expand' !nt_order nt2idxes_plus
;;

let get_sigs_of_size _ (* desired_sig *) spec nts size_to_nt_to_idxes 
    nt_rule_list full_grammar (curr_size, max_size) = 
  let grammar = BatSet.fold (fun nt grammar ->
    BatMap.add nt (BatSet.of_list (BatList.map (fun (_, rule) -> rule) (BatList.filter (fun (nt_l, _) -> nt_l = nt) nt_rule_list))) grammar
  ) nts BatMap.empty in
  let rec iter i size_to_nt_to_idxes =
    if i >= max_size then size_to_nt_to_idxes
    else 
      let size_to_nt_to_idxes = idxes_of_size i grammar nts size_to_nt_to_idxes spec in
      iter (i+1) size_to_nt_to_idxes
  in
  let size_to_nt_to_idxes = iter curr_size size_to_nt_to_idxes in
  let nt2idxes = expand nts full_grammar (BatMap.find curr_size size_to_nt_to_idxes) in
  let size_to_nt_to_idxes = BatMap.add curr_size nt2idxes size_to_nt_to_idxes in
  (* let nt_to_exprs = 
    BatMap.map (fun idxes -> 
      BatSet.map expr_of_idx idxes
    ) (BatMap.find curr_size size_to_nt_to_idxes) in
  (* let nt_to_sig = 
    BatMap.map (fun idxes -> 
      BatSet.map (fun idx -> BatMap.find idx !idx2out) idxes
    ) (BatMap.find curr_size size_to_nt_to_idxes) in *)
  print_endline (string_of_int curr_size);
  print_endline (string_of_map string_of_rewrite (string_of_set string_of_expr) nt_to_exprs); *)
  (* print_endline (string_of_map string_of_rewrite (string_of_set (string_of_list string_of_const)) !nt2out); *)
  (!nt2out, size_to_nt_to_idxes, !idx2out)
;;