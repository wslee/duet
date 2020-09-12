open Grammar
open Exprs
open Vocab
open Witness
open BidirectionalUtils

let cache : (int BatSet.t, float) BatMap.t ref = ref BatMap.empty
 
(* cover : signature -> int BatSet.t (set of point indices) *)
let compute_entropy pts cover pt2covers pt2covered_array nt_sigs = 
	if (BatMap.mem pts !cache) then BatMap.find pts !cache 
	else 
	let total_pts = BatSet.cardinal pts in
	let pts_bitset = intset2bitset pts in 
	let get_prob nt_sig =
		let cover_t : BitSet.t = (BatMap.find nt_sig cover) in
		let n_covered_pts = 
			BitSet.cardinal (BitSet.inter cover_t pts_bitset)
		in
		let sum_of_cond_prob = 
			BatSet.fold (fun pt acc ->
				if (BitSet.get cover_t pt) then
					let total_covered_pts =
						(** heuristic for fast learning of DTs *)
						if (!Options.fast_dt) then 
							List.length (BatMap.find pt pt2covers)
						(** original DT learning *)
						else 
  						List.fold_left (fun denom covered ->
  							let intersect =
  								BitSet.cardinal (BitSet.inter covered pts_bitset)
  							in
  							denom + intersect
  						) 0 (BatMap.find pt pt2covers)
					in
					(float_of_int n_covered_pts) /. (float_of_int total_covered_pts)   
				else acc    		 
			) pts 0.    
		in
		sum_of_cond_prob /. (float_of_int total_pts) 		 
	in
	let entropy = 
  	BatSet.fold (fun nt_sig acc ->   
  		let p_pts_label_t = get_prob nt_sig in
  		if p_pts_label_t = 0. then acc 
  		else acc +. p_pts_label_t *. ((log p_pts_label_t) /. log 2.)
  	) nt_sigs 0. |> (fun x -> -1. *. x) 
	in
	let _ = cache := BatMap.add pts entropy !cache in  
	entropy 
	
	
let get_best_bool_sig pts bool_nt bool_sigs nt_sigs cover pt2covers pt2covered_array =
	let pts = list2set pts in 
	let total_pts = BatSet.cardinal pts in
	(* bool_sig * score list *) 
	let g_scores =
		List.map (fun bool_sig ->
			let pts_y = 
  			BatSet.fold (fun pt acc -> 
  				if (get_concrete_bool (List.nth bool_sig pt)) then BatSet.add pt acc
  				else acc 
  			) pts BatSet.empty   
			in
			let pts_n = BatSet.diff pts pts_y in 
			let h_pts_y = compute_entropy pts_y cover pt2covers pt2covered_array nt_sigs in 
			let h_pts_n = compute_entropy pts_n cover pt2covers pt2covered_array nt_sigs in  
			let score = 
				(float_of_int (BatSet.cardinal pts_y)) /. (float_of_int total_pts) *. h_pts_y +. 
				(float_of_int (BatSet.cardinal pts_n)) /. (float_of_int total_pts) *. h_pts_n 
			in
			my_prerr_endline (Printf.sprintf "score: %.2f" score);
			(bool_sig, score)			 
		) (BatSet.elements bool_sigs) 
	in 
	List.sort (fun (_,x) (_,y) -> if x > y then 1 else if x = y then 0 else -1) g_scores |> List.hd |> fst
	 

let choose_best_pred cover pt2covers pt2covered_array pts bool_nt bool_sigs nt_sigs desired_sig nt_sig_to_expr =
	let bool_sig : signature = get_best_bool_sig pts bool_nt bool_sigs nt_sigs cover pt2covers pt2covered_array in  
	(bool_sig, try BatMap.find (bool_nt, bool_sig) nt_sig_to_expr with _ -> assert false) 
	
(* pts: list of indices of inputs to cover, *)
(* bool_sigs: signatures of available predicates *)
let rec learndt (pts, bool_sigs, cover, pt2covers, pt2covered_array)
			(available_height, available_size) (nt, desired_sig) 
			(spec, nt_rule_list, rule, nt_to_sigs, nt_sig_to_expr)
=
	(* remove non-covering sigs *)
	let nt_to_sigs =
		let pts = (list2set pts) in  
		BatMap.add nt 
			(BatSet.filter 
				(fun sg -> 
					let pts_bitset = intset2bitset pts in
					let cover_sg = (BatMap.find sg cover) in 
					(BitSet.cardinal (BitSet.inter pts_bitset cover_sg)) > 0 
				) (BatMap.find nt nt_to_sigs)
			) nt_to_sigs 
	in
	let nt_sigs = BatMap.find nt nt_to_sigs in
	my_prerr_endline (Printf.sprintf "minimal |nt_sigs| = %d" (BatSet.cardinal nt_sigs));
	(* get all "distinguishing" predicates *)
	let bool_sigs =
		BatSet.filter (fun bool_sig ->
			let bool_sig = List.fold_left (fun acc i -> acc @ [List.nth bool_sig i]) [] pts in
			List.exists (fun x -> (Pervasives.compare x (CBool (Concrete true))) = 0) bool_sig &&
			List.exists (fun x -> (Pervasives.compare x (CBool (Concrete false))) = 0) bool_sig
		) bool_sigs
	in
	my_prerr_endline (Printf.sprintf "|bool_sigs|: %d" (BatSet.cardinal bool_sigs));
	let nt_sigs = BatMap.find nt nt_to_sigs in
	let nt_ty = type_of_signature desired_sig in 
	let bool_nt = List.nth (get_nts rule) 0 in
	(* check if an expr covers all the points *)
	let nt_sigs' =
		let desired_sig = List.fold_left (fun acc i -> acc @ [List.nth desired_sig i]) [] pts in 
		BatSet.filter (fun nt_sig ->
			(* nt_sigs are transformed accordingly to the current points *)
			let nt_sig = List.fold_left (fun acc i -> acc @ [List.nth nt_sig i]) [] pts in
			List.for_all (fun (nt_const, desired_const) ->
				(Pervasives.compare nt_const desired_const) = 0
			) (BatList.combine nt_sig desired_sig)		
		) nt_sigs 
	in
	(* if we have exprs covering all the points, pick the smallest one *)
	if not (BatSet.is_empty nt_sigs') then
		BatSet.elements nt_sigs'
		|> List.map (fun nt_sig -> BatMap.find (nt, nt_sig) nt_sig_to_expr)
		|> List.sort (fun e1 e2 -> (Exprs.size_of_expr e1) - (Exprs.size_of_expr e2))
		|> List.hd 
	else
	(* otherwise, do dt learning *)		
		(* no predicates. failure *)
		if (BatSet.is_empty bool_sigs) then
			raise LearnDTFailure
		else
		(* get the best predicate *)	
		let (bool_sig, pred) = choose_best_pred cover pt2covers pt2covered_array pts bool_nt bool_sigs nt_sigs desired_sig nt_sig_to_expr in 
		let bool_sigs' = BatSet.remove bool_sig bool_sigs in
		(* left_pts : pts satisfying pred *)
		let left_pts =  
			List.fold_left (fun acc (bool_const, i) -> 
				if (get_concrete_bool bool_const) && (List.mem i pts) then acc @ [i] else acc  
			) [] (List.combine bool_sig (BatList.range 0 `To ((List.length bool_sig) - 1))) 
		in
		(* right_pts : pts unsatisfying pred *) 
		let right_pts = 
			List.fold_left (fun acc (bool_const, i) -> 
				if not (get_concrete_bool bool_const) && (List.mem i pts) then acc @ [i] else acc  
			) [] (List.combine bool_sig (BatList.range 0 `To ((List.length bool_sig) - 1))) 
		in  
		(* learn left & right subtree *)
		let left = learndt (left_pts, bool_sigs', cover, pt2covers, pt2covered_array) (available_height, available_size) (nt, desired_sig) (spec, nt_rule_list, rule, nt_to_sigs, nt_sig_to_expr) in 
		let right = learndt (right_pts, bool_sigs', cover, pt2covers, pt2covered_array) (available_height, available_size) (nt, desired_sig) (spec, nt_rule_list, rule, nt_to_sigs, nt_sig_to_expr) in
		(* return the resulting branching expr *)
		Function ("ite", [pred; left; right], nt_ty) 	
