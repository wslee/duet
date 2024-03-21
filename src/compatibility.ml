open Exprs
open Vocab

(* Can given new io-spec be compatible with old io-spec? *)
(* Strong true/false : always can/can't be *)
(* Weak   true/false : can/can't be for now *)
type compatibility = 
  | Strong of bool 
  | Weak of bool

(* how to modify a io-spec *)
(* ( [c0;c1;c2], None        ) -> delete [c0;c1;c2] from io-spec *)
(* ( [c0;c1;c2], Some (true) ) -> modify (or add) f(c0, c1, c2) = true *)
type plan = (const list * bool option) list

let get_bool c =
  match c with
  | Strong b -> b
  | Weak b -> b

(* map for all of io-spec *)
(* ex. [0;3] -> (-1, true) : f(0, 3) = true  is always true. *)
(* ex. [1;2] -> (0, false) : f(1, 2) = false is in weak-stack, and its idx is 0.  *)
let all_map : (const list, (int * bool)) BatMap.t ref = ref BatMap.empty
(* stack for io-spec that may not be compatible. the more sooner io-spec is in stack, the stronger *)
(* ex. ( [[0;1]; [2;3]], 0 ) : f(0, 1) = true /\ f(2, 3) = true. the pair of inputs matches their output according to b_list  *)
let weak_stack : ((const list) list * int) list ref = ref []
let b_list = [[true; true]; [false; true]; [false; false]]
let strong_idx = -1 (* for strong io-specs in the all_map *)

let string_of_stack s = 
  string_of_list (fun (aa, i) -> 
    (string_of_list (string_of_list string_of_const) aa) ^ " " ^ (string_of_int i)
  ) s

(* is f(A) = B compatible? *)
let is_compatible (a:const list) (b:bool)  =
  try 
    let (idx, b') = BatMap.find a !all_map in
    if idx = strong_idx then 
      Strong (b = b')
    else 
      Weak (b = b')
  with Not_found -> Weak true

(* is there strong io-spec when input is A? *)
let is_strong (a:const list) = 
  try 
    let (idx, b) = BatMap.find a !all_map in
    idx = strong_idx
  with Not_found -> false

let bool_to_const b =
  CBool (Concrete b)

exception StrongParadox (* can't fix *)
exception WeakParadox (* can fix *)

(* add strong io-spec that f(A) = B *)
let add_strong (a:const list) (b:bool) = 
  let cmp = is_compatible a b in
  match cmp with
  | Strong b' ->
    if b' then ()
    else raise StrongParadox
  | Weak b' ->
    if b' then 
      all_map := BatMap.add a (strong_idx, b) !all_map
    else
      let _ = all_map := BatMap.add a (strong_idx, b) !all_map in 
      raise WeakParadox 

(* add weak io-spec *)
(* aa = [a_0 ; a_1] *)
(* bb = [b_0 ; b_1] which its index is i at b_list *)
(* f(a_0) = b_0 /\ f(a_1) = b_1 *)
let add_weak (aa: (const list) list) (i: int) =
  assert (0 <= i && i <= 2);
  assert (BatList.length aa = 2);
  let tmp_map = ref !all_map in
  let _ = BatList.iter (fun (a, b) ->
    let cmp = is_compatible a b in
    match cmp with
    | Strong b' ->
      if b' then ()
      else raise WeakParadox
    | Weak b' ->
      if b' then 
        if not (BatMap.mem a !tmp_map) then
          tmp_map := BatMap.add a (BatList.length !weak_stack, b) !tmp_map
        else 
          ()
      else
        raise WeakParadox
  ) (BatList.combine aa (BatList.nth b_list i)) in 
  let _ = all_map := !tmp_map in
  weak_stack := (aa, i) :: !weak_stack

(* remove weak io-specs from all_map *)
let remove_weak (a_list: (const list) list) = 
  all_map := BatList.fold_left (fun acc a ->
    if BatMap.mem a !all_map then
      let (idx, b) = BatMap.find a !all_map in
      if idx = strong_idx then
        acc
      else
        BatMap.remove a acc
    else
      acc
  ) !all_map a_list

(* modify the top element of weak_stack to increase its output type by 1 *)
(* if its output type equals 2, pop it from weak_stack and modify the next top element recursively *)
(* returns plan that makes modified io-spec from old io-spec *)
let rec modify () : plan =
  if BatList.is_empty !weak_stack then raise StrongParadox
  else
    let (aa, out_ty) = BatList.hd !weak_stack in
    if out_ty = 2 then
      let _ = remove_weak aa in
      let _ = weak_stack := BatList.tl !weak_stack in
      let rtn : (const list * bool option) list = modify () in
      let rtn = 
        if is_strong (BatList.nth aa 1) then rtn 
        else ((BatList.nth aa 1, None) :: rtn) in
      let rtn = 
        if is_strong (BatList.nth aa 0) then rtn 
        else ((BatList.nth aa 0, None) :: rtn) in
      rtn 
    else 
      try
        let _ = remove_weak aa in
        let _ = weak_stack := BatList.tl !weak_stack in
        let _ = add_weak aa (out_ty + 1) in
        let bb = BatList.nth b_list (out_ty + 1) in
        let a_x_b = BatList.combine aa bb in
        BatList.fold_left (fun acc (a, b) ->
          (a, Some b) :: acc
        ) [] a_x_b 
      with WeakParadox ->
        let _ = weak_stack := (aa, out_ty + 1) :: !weak_stack in
        modify ()

let is_in_stack a = 
  BatList.exists (fun (aa, _) -> BatList.mem a aa) !weak_stack

(* pop elements from weak_stack until a is not in weak_stack, then use function 'modify' *)
let rec pop_and_modify a : plan = 
  assert (is_in_stack a);
  let (aa, out_ty) = BatList.hd !weak_stack in
  if BatList.mem a aa then
    modify ()
  else 
    let _ = remove_weak aa in
    let _ = weak_stack := BatList.tl !weak_stack in
    let rtn = pop_and_modify a in
    let rtn = 
      if is_strong (BatList.nth aa 1) then rtn 
      else ((BatList.nth aa 1, None) :: rtn) in
    let rtn = 
      if is_strong (BatList.nth aa 0) then rtn 
      else ((BatList.nth aa 0, None) :: rtn) in
    rtn

(* revise io-spec to modified io-spec by using 'plan' *)
let revise_spec spec plan' = 
  let plan_map = 
    BatList.fold_left (fun acc (a, opt) ->
      BatMap.add a opt acc 
    ) BatMap.empty plan'
  in
  BatList.fold_left (fun acc (i, o) ->
    if BatMap.mem i plan_map then 
      let opt = BatMap.find i plan_map in
      match opt with
      | Some b -> (i, bool_to_const b) :: acc
      | None -> acc
    else
      (i, o) :: acc
  ) [] spec

let add_if_does_not_exist (new_i, new_o) spec = 
  if BatList.exists (fun (i, _) -> i = new_i) spec then
    spec
  else
    (new_i, new_o) :: spec

(* add strong io-spec using function 'add_strong' *)
(* if there is any paradox, handle it by modifying io-spec *)
let add_strong_spec a b spec =
  try
    let _ = add_strong a b in
    (a, bool_to_const b) :: spec
  with 
  | StrongParadox ->
    failwith "There's no such loop invariant that fulfills given constraints.";
  | WeakParadox -> (
    try 
      let plan' = pop_and_modify a in
      add_if_does_not_exist (a, bool_to_const b) (revise_spec spec plan')
    with StrongParadox ->
      failwith "There's no such loop invariant that fulfills given constraints.";
  )

(* modify io-spec using function 'modify' *)
(* if there is any paradox, handle it by modifying io-spec *)
let modify_spec spec = 
  try 
    let plan' = modify () in
    revise_spec spec plan'
  with StrongParadox -> (
    failwith "There's no such loop invariant that fulfills given constraints.";
  )

(* add weak io-spec using function 'add_weak' *)
(* if there is any paradox, handle it by modifying io-spec *)
let add_weak_spec aa idx spec =
  let rec add_weak_iter i =
    if i = 3 then
      let plan' = modify () in
      revise_spec spec plan'
    else
      try
        let _ = add_weak aa i in
        let a_x_b  = BatList.combine aa (BatList.nth b_list i) in
        BatList.fold_left (fun acc (a, b) ->
          add_if_does_not_exist (a, bool_to_const b) acc
        ) spec a_x_b
      with WeakParadox ->
        add_weak_iter (i + 1)
  in
  try
    add_weak_iter idx
  with StrongParadox ->
    failwith "There's no such loop invariant that fulfills given constraints.";