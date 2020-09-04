open Grammar
open Exprs
open Vocab
open Generator
open Sexplib


module BitSet = 
struct
	open Containers
	include CCBV
	let intset2bitset s = 
  	BatSet.fold (fun i acc -> 
  		set acc i; acc
  	) s (create ~size:32 false)
end 
let intset2bitset = BitSet.intset2bitset

let int_max = Pervasives.max_int - 1000
let curr_comp_size = ref !Options.init_comp_size  

type vsa = Union of vsa BatSet.t 
	| Join of rewrite * vsa list  
	| Direct of expr 
	| Empty

exception NoSolInVSA
exception VSAFound of vsa BatSet.t
exception Covered
exception LearnDTFailure
exception LearnSinglePathFailure
exception LearnForEachFailure

(* sig -> expr (<= size) *)
let get_sigs_of_size desired_sig spec (nt_to_sigs, nt_to_exprs, nt_sig_to_expr) 
		nt_rule_list (curr_size, max_size) = 
	let (nt_to_sigs, nt_to_exprs, nt_sig_to_expr) = 
  	if (curr_size = 1) then 
  		List.fold_left (fun (nt_to_sigs, nt_to_exprs, nt_sig_to_expr) (nt, rule) ->
  			let holes = get_holes [] rule in 
  			if (List.length holes) = 0 then
  				let expr = (expr_of_rewrite rule) in 
  				let signature = compute_signature spec expr in
  				if (compare desired_sig signature) = 0 then raise (SolutionFound expr)
  				else 
  					(add_signature nt signature nt_to_sigs, 
  					 add_expr nt (expr, 1) nt_to_exprs,
  					 BatMap.add (nt, signature) expr nt_sig_to_expr) 
  			else (nt_to_sigs, nt_to_exprs, nt_sig_to_expr) 
  		) (nt_to_sigs, nt_to_exprs, nt_sig_to_expr) nt_rule_list 
  	else (nt_to_sigs, nt_to_exprs, nt_sig_to_expr) 
	in	
	let rec iter size (nt_to_sigs, nt_to_exprs, nt_sig_to_expr) =
		if (size >= max_size) then (nt_to_sigs, nt_to_exprs, nt_sig_to_expr)
		else 
  		let (nt_to_sigs, nt_to_exprs, nt_sig_to_expr) = 
				List.fold_left (fun (nt_to_sigs, nt_to_exprs, nt_sig_to_expr) (nt, rule) ->
					let (nt_to_sigs, nt_to_exprs, nt_sig_to_expr) = 
						grow nt rule (nt_to_sigs, nt_to_exprs, nt_sig_to_expr) desired_sig spec size
					in
					(nt_to_sigs, nt_to_exprs, nt_sig_to_expr)
				) (nt_to_sigs, nt_to_exprs, nt_sig_to_expr) nt_rule_list 
  		in 
			iter (size + 1) (nt_to_sigs, nt_to_exprs, nt_sig_to_expr)   
	in
	iter curr_size (nt_to_sigs, nt_to_exprs, nt_sig_to_expr)
	

let rec string_of_vsa vsa = 
	match vsa with 
	| Union vsas -> string_of_set ~first:"{" ~last:"}" ~sep:" U " string_of_vsa vsas 
	| Join (rule, vsa_lst) -> 
		(Grammar.op_of_rule rule) ^ (string_of_list ~first:"(" ~last:")" ~sep:", " string_of_vsa vsa_lst)   
	| Direct expr -> Exprs.string_of_expr expr 	
	| Empty -> "" 

(* return (lowerbound, upperbound) of size of programs in vsa *)
let rec pgm_size_of_vsa vsa =
	match vsa with 
	| Direct expr -> (Exprs.size_of_expr expr, Exprs.size_of_expr expr)
	| Join (_, vsa_list) ->
		let sizes = BatList.map pgm_size_of_vsa vsa_list in 
		BatList.fold_left (fun (lb, ub) (lb', ub') ->
			(lb + lb', ub + ub') 	 
		) (1, 1) sizes  
	| Union vsa_set -> 
		BatSet.fold (fun vsa' (lb, ub) ->
			let (lb', ub') = pgm_size_of_vsa vsa' in 
			((if (lb' < lb) then lb' else lb),
			 (if (ub' > ub) then ub' else ub)) 	 
		) vsa_set (int_max, -int_max)
	| Empty -> (0, 0) 
		  
let rec choose_best_from_vsa vsa = 
	match vsa with 
	| Direct expr -> expr 
	| Union vsa_set ->
		let _ = assert (not (BatSet.is_empty vsa_set)) in 
		let vsa_list = BatSet.elements vsa_set in 
		let vsa_list_with_size = List.map (fun vsa -> (pgm_size_of_vsa vsa, vsa)) vsa_list in 
		let vsa_list_with_size = 
			List.sort (fun ((lb1, ub1), vsa1) ((lb2, ub2), vsa2) -> lb1 - lb2) vsa_list_with_size
		in 
		BatList.hd vsa_list_with_size |> snd |> choose_best_from_vsa   
		(* choose_best_from_vsa (BatSet.choose vsa_set) *)
	| Join (rule, vsa_list) ->
		Function (op_of_rule rule, (BatList.map choose_best_from_vsa vsa_list), ret_type_of_op rule) 
	| Empty -> raise NoSolInVSA	 
		 		
let not_covered nt_sigs desired_sig =
	let desired_sig_opt = BatList.map (fun x -> Some x) desired_sig in
	try 
		let desired_sig_opt = 
    	BatSet.fold (fun nt_sig desired_sig_opt -> 
    		if (List.for_all (fun x -> x = None) desired_sig_opt) then raise Covered
    		else 
    			BatList.map (fun (nt_const, desired_const_opt) ->
    				match desired_const_opt with 
    				| None -> None
    				| Some desired_const ->  
    					if (Pervasives.compare nt_const desired_const) = 0 then None
    					else desired_const_opt
    			) (BatList.combine nt_sig desired_sig_opt)
    	) nt_sigs desired_sig_opt 
		in
		List.fold_left (fun acc (x, i) -> 
			if x = None then acc else acc @ [i] 
		) [] (List.combine desired_sig_opt (BatList.range 0 `To ((List.length desired_sig_opt) - 1)))
  with Covered -> [] 	 


let rec remove_redundant_sigs sigs desired_sig = 
	BatSet.filter (fun sg ->
		List.exists 
			(fun (const, desired_const) -> (Pervasives.compare const desired_const) = 0) 
			(List.combine sg desired_sig)  		 
	) sigs 

		
(* l, u : signature set *)
let rec scan_coarsen (l, u) desired_sig = 
	if (BatSet.equal l u) then u
	else 
		let elem = BatSet.diff u l |> BatSet.choose in  
		let u_wo_elem = BatSet.remove elem u in 
		if (not_covered u_wo_elem desired_sig) = [] then 
			scan_coarsen (l, u_wo_elem) desired_sig 
		else  		
			scan_coarsen (BatSet.add elem l, u) desired_sig
			
			
			

		(* let rec create_ite nt_sigs =                                                                  *)
		(* 	let nt_sig = BatSet.choose nt_sigs in                                                       *)
		(* 	let nt_sigs' = BatSet.remove nt_sig nt_sigs in                                              *)
		(* 	let term = BatMap.find (nt, nt_sig) nt_sig_to_expr in                                       *)
		(* 	if (BatSet.is_empty nt_sigs') then term                                                     *)
		(* 	else                                                                                        *)
  	(* 		let bool_sig =                                                                            *)
  	(* 			BatList.map (fun (nt_const, desired_const) ->                                           *)
  	(* 				CBool ((Pervasives.compare nt_const desired_const) = 0)                               *)
  	(* 			) (BatList.combine nt_sig desired_sig)                                                  *)
  	(* 		in                                                                                        *)
		(* 		let _ =                                                                                   *)
		(* 			if (Pervasives.compare (snd !goal) desired_sig) = 0 then                                *)
		(* 			begin                                                                                   *)
  	(* 				let _ = prerr_endline (Printf.sprintf "desired  : %s" (string_of_sig desired_sig)) in *)
    (* 				let _ = prerr_endline (Printf.sprintf "nt_sig  : %s" (string_of_sig nt_sig)) in       *)
		(* 				let _ = prerr_endline (Printf.sprintf "term  : %s" (Exprs.string_of_expr term)) in    *)
		(* 				let _ = prerr_endline (Printf.sprintf "bool_sig : %s" (string_of_sig bool_sig)) in    *)
		(* 				()                                                                                    *)
  	(* 			end                                                                                     *)
		(* 		in                                                                                        *)
		(* 		let pred =                                                                                *)
    (* 			learn (available_height, available_size)                                                *)
    (* 					  (bool_nt, bool_sig)                                                               *)
    (* 						(spec, nt_rule_list, total_sigs, nt_to_sigs, nt_sig_to_expr)                      *)
  	(* 			|> (fun x -> (*prerr_endline (string_of_vsa x);*) x) |> choose_best_from_vsa            *)
  	(* 		in                                                                                        *)
		(* 		let _ =                                                                                   *)
		(* 			if (Pervasives.compare (snd !goal) desired_sig) = 0 then                                *)
		(* 			begin                                                                                   *)
  	(* 				let _ = prerr_endline ("term: " ^ (Exprs.string_of_expr term)) in                     *)
  	(* 				let _ = prerr_endline ("pred: " ^ (Exprs.string_of_expr pred)) in                     *)
		(* 				()                                                                                    *)
		(* 			end                                                                                     *)
		(* 		in                                                                                        *)
		(* 		Function ("ite", [pred; term; (create_ite nt_sigs')], nt_ty)                              *)
		(* in                                                                                            *)