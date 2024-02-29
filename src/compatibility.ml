open Exprs

type compatibility = 
  | Strong of bool 
  | Weak of bool

let get_bool c =
  match c with
  | Strong b -> b
  | Weak b -> b

let all_map = ref BatMap.empty
let weak_stack = ref []
let b_list = [[true; true]; [false; true]; [false; false]]
let strong_idx = -1

let is_compatible a b  =
  try 
    let (idx, b') = BatMap.find a !all_map in
    if idx = strong_idx then 
      Strong (b = b')
    else 
      Weak (b = b')
  with Not_found -> Weak true

let is_strong a = 
  try 
    let (idx, b) = BatMap.find a !all_map in
    idx = strong_idx
  with Not_found -> false

let bool_to_const b =
  CBool (Concrete b)

exception StrongParadox (* can't fix *)
exception WeakParadox (* can fix *)

let add_strong a b = 
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

let add_weak a_list i =
  assert (0 <= i && i <= 2);
  assert (BatList.length a_list = 2);
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
  ) (BatList.combine a_list (BatList.nth b_list i)) in 
  let _ = all_map := !tmp_map in
  weak_stack := (a_list, i) :: !weak_stack

(* return (sig, bool option) list *)
let rec modify () =
  if BatList.is_empty !weak_stack then raise StrongParadox
  else
    let (aa, out_ty) = BatList.hd !weak_stack in
    if out_ty = 2 then
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

let rec pop_and_modify a = 
  assert (is_in_stack a);
  let (aa, out_ty) = BatList.hd !weak_stack in
  if BatList.mem a aa then
    modify ()
  else 
    let _ = weak_stack := BatList.tl !weak_stack in
    let rtn = pop_and_modify a in
    let rtn = 
      if is_strong (BatList.nth aa 1) then rtn 
      else ((BatList.nth aa 1, None) :: rtn) in
    let rtn = 
      if is_strong (BatList.nth aa 0) then rtn 
      else ((BatList.nth aa 0, None) :: rtn) in
    rtn

let revise_spec spec plan = 
  let plan_map = 
    BatList.fold_left (fun acc (a, opt) ->
      BatMap.add a opt acc 
    ) BatMap.empty plan 
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

let add_strong_spec a b spec =
  try
    let _ = add_strong a b in
    (a, bool_to_const b) :: spec
  with 
  | StrongParadox ->
    failwith "There's no such loop invariant that fulfills given constraints.";
  | WeakParadox -> (
    try 
      let plan = pop_and_modify a in
      add_if_does_not_exist (a, bool_to_const b) (revise_spec spec plan)
    with StrongParadox ->
      failwith "There's no such loop invariant that fulfills given constraints.";
  )

let modify_spec spec = 
  try 
    let plan = modify () in
    revise_spec spec plan
  with StrongParadox -> (
    failwith "There's no such loop invariant that fulfills given constraints.";
  )

let add_weak_spec aa spec =
  let rec add_weak_iter i =
    if i = 3 then
      let plan = modify () in
      revise_spec spec plan
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
    add_weak_iter 0
  with StrongParadox ->
    failwith "There's no such loop invariant that fulfills given constraints.";