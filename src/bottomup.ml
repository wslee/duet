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

let rec expr_of_node x =
  match x with
  | Leaf expr -> expr
  | NonLeaf (idx, children) -> (
    let func, ty = BatMap.find idx !idx2func in
    match func with
    | FuncRewrite (op, _) -> Function (op, BatList.map (fun idx -> expr_of_node (BatMap.find idx !idx2node)) children, ty)
    | _ -> failwith "node2expr : not FuncRewrite"
  )
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
        | _ -> idxes
      ) rules BatSet.empty in
      BatMap.add nt idxes nt2idxes
    ) nts BatMap.empty in
    BatMap.add sz nt2idxes sz2idxes
  else
    (* TODO *)
    sz2idxes
;;

let synthesis (macro_instantiator, target_function_name, args_map, grammar, forall_var_map, spec) =
  let nts = BatMap.foldi (fun nt rules s -> (BatSet.add nt s)) grammar BatSet.empty in
  let sz2idxes = idxes_of_size 1 grammar nts BatMap.empty spec in
  let start_nt = BatList.hd (BatSet.to_list nts) in
  sz2idxes
;;
