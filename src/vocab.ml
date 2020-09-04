let (<<<) f g = fun x -> f (g x)
let (>>>) f g = fun x -> g (f x)
let ($>) x f = match x with Some s -> f s | None -> None
let (&>) x f = match x with Some s -> Some (f s) | None -> None
let (@) l1 l2 = BatList.append l1 l2
let id x = x
let flip f = fun y x -> f x y
let cond c f g x = if c then f x else g x
let opt c f x = if c then f x else x
let tuple x = (x, x)
let map3 f l1 l2 l3 =
	(* try   *)
	let lst = List.combine l1 (List.combine l2 l3) in 
	List.map (fun (e1, (e2, e3)) -> f e1 e2 e3) lst
	(* with _ ->                                                                                        *)
	(* 	failwith (Printf.sprintf "map3: %d %d %d" (List.length l1) (List.length l2) (List.length l3))  *)

let read_lines name : string list =
  let ic = open_in name in
  let try_read () =
    try Some (input_line ic) with End_of_file -> None in
  let rec loop acc = match try_read () with
    | Some s -> loop (s :: acc)
    | None -> close_in ic; List.rev acc in
  loop []

let write_lines lines name = 
	let oc = open_out name in
	List.iter (fun line -> Printf.fprintf oc "%s\n" line) lines; 
	close_out oc 		
					
let set_map f set = 
	BatSet.fold (fun elt acc -> BatSet.add (f elt) acc) set BatSet.empty 
	
let list2set lst = 
	List.fold_left (fun set elt -> BatSet.add elt set) BatSet.empty lst 

(** This applies [List.fold_left], but the argument type is the same with
    [PSet.fold].  *)
let list_fold : ('a -> 'b -> 'b) -> 'a list -> 'b -> 'b
= fun f list init ->
  List.fold_left (flip f) init list
	

let link_by_sep sep s acc = if acc = "" then s else acc ^ sep ^ s

let string_of_list ?(first="[") ?(last="]") ?(sep=";") : ('a -> string)
  -> ('a list) -> string
= fun string_of_v list ->
  let add_string_of_v v acc = link_by_sep sep (string_of_v v) acc in
  first ^ list_fold add_string_of_v list "" ^ last

let string_of_set ?(first="{") ?(last="}") ?(sep=",") : ('a -> string)
  -> ('a BatSet.t) -> string
= fun string_of_v set ->
  let add_string_of_v v acc = link_by_sep sep (string_of_v v) acc in
  first ^ BatSet.fold add_string_of_v set "" ^ last

let string_of_map ?(first="{") ?(last="}") ?(sep=",\n") ?(indent="") : ('a -> string)
  -> ('b -> string) -> (('a, 'b) BatMap.t) -> string
= fun string_of_k string_of_v map ->
  let add_string_of_k_v k v acc =
    let str = string_of_k k ^ " -> " ^ string_of_v v in
    link_by_sep (sep^indent) str acc in
  if BatMap.is_empty map then "empty"
  else indent ^ first ^ BatMap.foldi add_string_of_k_v map "" ^ last

let my_prerr_endline str = if !Options.debug then prerr_endline str
let my_prerr_newline () = if !Options.debug then prerr_newline ()
let my_prerr_string str = if !Options.debug then prerr_string str
