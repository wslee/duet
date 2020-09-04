open Grammar
open Exprs
open Vocab
open Core_kernel

let int_max = Pervasives.max_int - 1000
type signature = Exprs.const list  
type state = rewrite * signature  (* production rule and abstr sig *) 
type operator = string 
type transition = operator * (state list) * state   
type edge = (state list) * state

module StateSet = BatSet.Make(struct type t = state let compare = Pervasives.compare end)
module TransitionSet = BatSet.Make(struct type t = transition let compare = Pervasives.compare end)
module EdgeSet = BatSet.Make(struct type t = (state list) * state  let compare = Pervasives.compare end)

let nt_of_state (nt, sg) = nt 
let sig_of_state (nt, sg) = sg 
let create_edge states state = (states, state)

let type_of_signature signature =
	let _ = assert ((BatList.length signature) > 0) in
	type_of_const (BatList.hd signature)  
	
let string_of_sig sigature = 
	BatList.fold_left (fun acc x -> acc ^ " " ^ (string_of_const x)) "" sigature

let string_of_state (nt, sigature) =
	Printf.sprintf "q^%s_%s" (Grammar.string_of_rewrite nt) (string_of_sig sigature)
	
let string_of_statelist states = 
	BatList.fold_left (fun acc (nt, sigature) ->
		acc ^ "," ^ (string_of_state (nt, sigature))  
	) "" states  

let string_of_stateset states = 
	StateSet.fold (fun (nt, sigature) acc ->
		acc ^ "," ^ (string_of_state (nt, sigature)) 	 
	) states "" 
		 
let print_afta (states, final_states, transitions) = 
	prerr_endline "=== Transitions === "; 
	TransitionSet.iter (fun (op, states, state) ->
		prerr_endline (Printf.sprintf "%s(%s) ->%s%s" 
			op 
			(string_of_statelist states)
			(if (StateSet.mem state final_states) then " #" else " ") 
			(string_of_state state)) 
	) transitions
			
let share_prefix : string -> string -> bool 
= fun str1 str2 -> 
	if (String.length str1) * (String.length str2) = 0 then false 
	else
		let c1 = (str1.[0]) in 
		let c2 = (str2.[0]) in 
		BatChar.equal c1 c2   
	
let share_suffix str1 str2 =
	if (String.length str1) * (String.length str2) = 0 then false 
	else
		let c1 = BatString.get (BatString.rev str1) 0 in 
		let c2 = BatString.get (BatString.rev str2) 0 in   
		BatChar.equal c1 c2
