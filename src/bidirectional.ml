open Grammar
open Exprs
open Vocab
open Witness
open BidirectionalUtils

(** Global mutable variables *)
(* (nt, sig, spec) -> vsa * height *)
let learn_cache = ref BatMap.empty
let goal = ref (Grammar.start_nt, [])
let now_learning = ref BatSet.empty 
let bu_time = ref 0.
let td_time = ref 0.
let adapt_time = ref 0.
let curr_comp_size = ref !Options.init_comp_size
let num_components = ref 0   


let rec learn (available_height, available_size) (nt, desired_sig) 
							(spec, nt_rule_list, total_sigs, nt_to_sigs, nt_sig_to_expr) =	
	(* already consumed availble_size *)
	if (available_height <= 0 || available_size <= 0) then Empty
	(* to avoid revisit the same synthesis problem *)
	else if (BatSet.mem (nt, desired_sig, spec) !now_learning) then
	(* let _ = my_prerr_endline (Printf.sprintf "*** Already learning *** %s %s" (string_of_rewrite nt) (string_of_sig desired_sig)) in *)
		Empty
	else if ( (BatMap.mem (nt, desired_sig, spec) !learn_cache) &&
						let (vsa, height) = 
  						BatMap.find (nt, desired_sig, spec) !learn_cache
  					in	
  					(available_height <= height || vsa <> Empty)
					) 
	then
		let (vsa, _) = 
			BatMap.find (nt, desired_sig, spec) !learn_cache
		in
		vsa
	else 
	begin 
  	let _ = 
  		my_prerr_endline (Printf.sprintf "Learning (%d, %d) : (%s, %s, %s)" available_height available_size (string_of_rewrite nt) (string_of_sig desired_sig) (Specification.string_of_io_spec spec));
  		now_learning := BatSet.add (nt, desired_sig, spec) !now_learning 
  	in	
  	let result =
  		(* terminal node *)   
    	if (BatMap.mem (nt, desired_sig) nt_sig_to_expr) then
				let _ = my_prerr_endline (Printf.sprintf "Direct : %s" (Exprs.string_of_expr (BatMap.find (nt, desired_sig) nt_sig_to_expr))) in 
    		Direct (BatMap.find (nt, desired_sig) nt_sig_to_expr) 
    	else 
    		let vsas = 
        	BatList.fold_left (fun acc (nt', rule) ->
    				(* if (Pervasives.compare nt nt') = 0 then *)
  					if (is_equal_nt nt nt') then
  						(* Rule: A -> F(B, C)  *)
    					if (is_function_rule rule) then
								let op = op_of_rule rule in  
            		let vsa = 
      						learn_rule (available_height, available_size) (nt, desired_sig) 
  									(spec, nt_rule_list, rule, total_sigs, nt_to_sigs, nt_sig_to_expr)
      					in 
            		if (vsa <> Empty) then
									let _ =
										(* if (available_height > 1) then                                              *)
										(* 	prerr_endline (Printf.sprintf "learn_rule success %s" (op_of_rule rule))  *)
										add_learn_rule_cache true op
									in
  								let _ =
  									(* if the user wants to find a "single" solution, stop *)
  									if (Pervasives.compare (nt, desired_sig) !goal) = 0 &&
  										 not (!Options.find_all) then
  									(
  										my_prerr_endline "solution found! - stop searching";
  										raise (VSAFound (BatSet.singleton vsa))
  									)
  								in
  								BatSet.add vsa acc 
  							else
									let _ =
										(* if (available_height > 1) then                                              *)
										(* 	prerr_endline (Printf.sprintf "learn_rule failure %s" (op_of_rule rule))  *)
										add_learn_rule_cache false op  
									in  
									acc  				 
    					(* Rule: A -> B  *)
  						else if (is_nt_rule rule) then
    						let nt' = BatList.hd (get_nts rule) in  
    						let vsa = 
      						learn (available_height, available_size) (nt', desired_sig) 
  								  (spec, nt_rule_list, total_sigs, nt_to_sigs, nt_sig_to_expr)
      					in 
            		if (vsa <> Empty) then
  								let _ =
  									(* if the user wants to find a "single" solution, stop *)
  									if (Pervasives.compare (nt, desired_sig) !goal) = 0 &&
  										 not (!Options.find_all) then
  									(
  										my_prerr_endline "solution found! - stop searching";
  										raise (VSAFound (BatSet.singleton vsa))
  									)
  								in
  								BatSet.add vsa acc 
  							else acc  				  
    					else (* constant rule *) acc 
    				else 
  						(* the currently considered non-terminal is not the symbol to synthesize. ignore it *) 
  						acc 
        	) BatSet.empty nt_rule_list   
    		in
    		if (BatSet.is_empty vsas) then Empty 
    		else Union vsas
  	in
  	let (lb, ub) = pgm_size_of_vsa result in
  	
  	(* possible to generate an |expr| <= availble_size *)
  	if (lb <= available_size) then
  		(* caching *)
  		let _ =
  			(* Some rule may consume all the heights and sizes (e.g., +/-), and *)
  			(* wrongly conclude no VSA exists, which may prevent other rules from finding solutions.*)
  			(* To prevent such situation, we only cache a VSA when it is not empty.  *)
  			(* if result <> Empty then  *)
  				learn_cache := BatMap.add (nt, desired_sig, spec) (result, available_height) !learn_cache 
  		in
  		let _ = now_learning := BatSet.remove (nt, desired_sig, spec) !now_learning in
    	result
  	(* can't generate an |expr| <= availble_size *)
  	else
  		(* let expr = choose_best_from_vsa result in *)
  		(* Direct expr                               *)
  		(* let _ = prerr_endline (Printf.sprintf "%s %d > %d" (Exprs.string_of_expr expr) lb available_size) in *)
  		Empty
	end

and learn_rule (available_height, available_size) (nt, desired_sig) 
							 (spec, nt_rule_list, rule, total_sigs, nt_to_sigs, nt_sig_to_expr) =
	let result =  
  	let _ =
			my_prerr_endline (Printf.sprintf "Learning rule (%d, %d) :%s for %s"
				available_height available_size (string_of_rewrite rule) (string_of_sig desired_sig))
		in
  	match rule with 
  	| FuncRewrite (op, rewrites) ->
  	begin
			let nts = get_nts rule in
			(* there's no hope to generate |expr| < available_size  *)
			if (available_size < (1 + (List.length nts))) then Empty
			else
				(* for if-then-else expr, do divide-and-conquer *)
				if (String.compare op "ite") = 0 then
					let vsa = 
  					learn_ite (available_height, available_size) 
  						(nt, desired_sig) (spec, nt_rule_list, rule, total_sigs, nt_to_sigs, nt_sig_to_expr)
					in
					vsa
				else 
    		(* process args in order of from-left-to-right *)
    		(* obtain all sub-specifications [(nt1, sig1), ..., (ntn, sign)] where *)
				(*   nt_i is i-th parameter non-terminal *)
				(*   sig_i is the desired signature of nt_i *)
    		let nt_sig_lists =
					learn_paths available_height 0 rule nts desired_sig total_sigs nt_to_sigs BatSet.empty
				in
    		if (BatSet.is_empty nt_sig_lists) then Empty 
    		else 
    		(* Learn a VSA for each nt_sig_list, and union all of them *)
    			let vsas =
						try 
    				BatSet.fold (fun nt_sig_list acc ->
							try 
        				let _, vsas = 
        					BatList.fold_left (fun (available_size', acc) (nt, sg) ->
      							let vsa = 
  										learn (available_height - 1, available_size') (nt, sg) 
											  (spec, nt_rule_list, total_sigs, nt_to_sigs, nt_sig_to_expr) 
  									in
  									(* no program for this parameter. no need to consider this subspec *)
  									if (vsa = Empty) then raise LearnSinglePathFailure
  									else
											let lb, _ = pgm_size_of_vsa vsa in 
      								(available_size' - lb, acc @ [vsa])
        					) (available_size, []) nt_sig_list 
        				in 
								(* report once a single solution is found if !Options.find_all = false *)
								if !Options.find_all then BatSet.add (Join (rule, vsas)) acc
      					else raise (VSAFound (BatSet.singleton (Join (rule, vsas))))
							(* try next subspec *)
							with LearnSinglePathFailure _ -> acc 
      			) nt_sig_lists BatSet.empty
						(* report once a single solution is found if !Options.find_all = false *)
						with VSAFound vsas -> vsas  
    			in
    			if (BatSet.is_empty vsas) then Empty
    			else Union vsas
  	end
  	| _ -> assert false 		 
	in
	result


and learn_for_each pts (available_height, available_size) (nt, desired_sig) 
							(spec, nt_rule_list, rule, total_sigs, nt_to_sigs, nt_sig_to_expr) = 
	let f (available_height, available_size) i =
		(* let _ =                                                              *)
		(* 	if (Pervasives.compare (snd !goal) desired_sig) = 0 then           *)
		(* 		prerr_endline (Printf.sprintf "trying %s -> %s"                  *)
		(* 			(string_of_list Exprs.string_of_const (fst (List.nth spec i))) *)
		(* 			(Exprs.string_of_const (List.nth desired_sig i))               *)
		(* 		)                                                                *)
		(* in                                                                   *)
		let (int_sigs, bv_sigs, string_sigs, bool_sigs) = total_sigs in 
		(* pick outputs on i-th input example *)
		let (int_sigs, bv_sigs, string_sigs, bool_sigs) as total_sigs = 
			(set_map (fun x -> [List.nth x i]) int_sigs,
			 set_map (fun x -> [List.nth x i]) bv_sigs,
			 set_map (fun x -> [List.nth x i]) string_sigs,
			 set_map (fun x -> [List.nth x i]) bool_sigs)  
		in
		(* nt_to_sigs only for the i-th input example *) 
		let nt_to_sigs =
			BatMap.foldi (fun nt sigs m -> 
				BatMap.add nt (set_map (fun sg -> [List.nth sg i]) sigs) m 	 
			) nt_to_sigs BatMap.empty 
		in
		(* not consider ite rule. we're trying to find terms of an ite expression *) 
		let nt_rule_list = exclude_ite_rules nt_rule_list in 
		(* nt_sig_to_expr only for the i-th input example *)
		let nt_sig_to_expr = 
			BatMap.foldi (fun (nt, nt_sig) expr m ->
				let nt_sig = [List.nth nt_sig i] in 
				BatMap.add (nt, nt_sig) expr m 	 
			) nt_sig_to_expr BatMap.empty 
		in 
		let vsa = 
  		learn (available_height, available_size) 
    				(nt, [List.nth desired_sig i]) 
    				([List.nth spec i], nt_rule_list, total_sigs, nt_to_sigs, nt_sig_to_expr)
		in
		(* prerr_endline (string_of_sig  [List.nth desired_sig 0]);                                                                       *)
		(* if (Pervasives.compare (snd !goal) desired_sig) = 0 then                                                                       *)
		(* 	prerr_endline (Printf.sprintf "trying %s learned: %s" (Exprs.string_of_const (List.nth desired_sig i)) (string_of_vsa vsa)); *)
		vsa
	in
	(* Here, folding is important. *)
	(* For example, suppose we have two I/O examples (I1, O1), (I2, O2)   *)
	(* which can be satisfied by an expression e. *)
	(* Because the witness functions are incomplete, *)
	(* it may be case that e can be learned from (I1, O1) but not from (I2, O2).*)
	(* Suppose we do mapping. then we would fail to learn an expression for I2 *)
	(* and conclude we can't learn an ite expression because not every I/O example has been covered. *)
	(* By folding, we can learn e for I1 and mark I2 as covered. *)
	let _, _, _, vsa_list = 
		List.fold_left (fun (already_covered, available_height, available_size, vsa_list) i ->
			if (BatSet.mem i already_covered) then 
				(already_covered, available_height, available_size, vsa_list) 
			else  
  			let vsa = f (available_height, available_size) i in
  			let _ = if vsa = Empty then raise LearnForEachFailure in 
  			let lb, _ = pgm_size_of_vsa vsa in
				let expr = choose_best_from_vsa vsa in 
				let covered = covered_pts spec expr desired_sig in
				let already_covered = BatSet.union covered already_covered in    
  			(already_covered, available_height, available_size - lb, vsa_list @ [vsa])    
	  ) (BatSet.empty, available_height, available_size, []) pts 
	in
	vsa_list
		

(* for each cover in covers*)
(* 		bool_sig[i] = (cover[i] = desired_sig[i])  *)
(* 		preds[i] := learn (ntBool, bool_sig) *)
(* sol: ite preds[0] covers[0] (ite preds[1] covers[1] ... covers[n]) *)
and learn_ite (available_height, available_size) (nt, desired_sig) 
							(spec, nt_rule_list, rule, total_sigs, nt_to_sigs, nt_sig_to_expr) =
	try
	let nt_ty = type_of_signature desired_sig in 
	let bool_nt = BatList.hd (get_nts rule) in
	let _ = 
		if (Pervasives.compare (snd !goal) desired_sig) = 0 then
			my_prerr_endline (Printf.sprintf "learn_ite %s" (string_of_sig desired_sig))
	in
	(* for each input (point), learn vsa *)
	let pts_to_cover =
		let nt_sigs = BatMap.find nt nt_to_sigs in 
		not_covered nt_sigs desired_sig 
	in
	let (nt_to_sigs, nt_sig_to_expr) =
		(* already covered *)
		if (List.length pts_to_cover) = 0 then (nt_to_sigs, nt_sig_to_expr)
		else (* if not all points are covered, learn for each non-covered point *)
			let vsa_list =
				(* if any point is not learnable, raise exception and stop *)
				(* ite b e e *)
    		learn_for_each pts_to_cover (available_height (*- 1*), available_size) (nt, desired_sig)
    							(spec, nt_rule_list, rule, total_sigs, nt_to_sigs, nt_sig_to_expr)
    	in
  		List.fold_left (fun (nt_to_sigs, nt_sig_to_expr) vsa ->
  			try
    			let nt_sigs = try BatMap.find nt nt_to_sigs with _ -> assert false in
    			let expr = (choose_best_from_vsa vsa) in
    			let new_sig = Exprs.compute_signature spec expr in
    			(BatMap.add nt (BatSet.add new_sig nt_sigs) nt_to_sigs,
    			 BatMap.add (nt, new_sig) expr nt_sig_to_expr)
  			with NoSolInVSA -> assert false  (* exception should have been raised earlier *)
				| UndefinedSemantics ->
					(nt_to_sigs, nt_sig_to_expr)
  		) (nt_to_sigs, nt_sig_to_expr) vsa_list
	in
	(* should be here. do not move forward. *)
	let nt_sigs = BatMap.find nt nt_to_sigs in
	(* not all points are covered. no hope for finding an ite solution *)
	let _ = if (not_covered nt_sigs desired_sig) <> [] then raise NoSolInVSA in   
	let _ = if (Pervasives.compare desired_sig (snd !goal)) = 0 then
		my_prerr_endline (Printf.sprintf "|nt_sigs| = %d" (BatSet.cardinal nt_sigs))
	in
	(* pts: list of indices of inputs to cover, *)
	(* bool_sigs: signatures of available predicates *)
	(** learning ite expression with learning-based unifier *)
	let rec learnite_lbu pts bool_sigs =
		(* prerr_endline ("learnite_lbu pts      : " ^ (string_of_list string_of_int pts)); *)
		let nt_sigs =
			let desired_sig = List.fold_left (fun acc i -> acc @ [List.nth desired_sig i]) [] pts in
			BatSet.filter (fun nt_sig ->
				let nt_sig = List.fold_left (fun acc i -> acc @ [List.nth nt_sig i]) [] pts in
				List.for_all (fun (nt_const, desired_const) ->
					(Pervasives.compare nt_const desired_const) = 0
				) (BatList.combine nt_sig desired_sig)
			) nt_sigs
		in
		if not (BatSet.is_empty nt_sigs) then
			BatSet.elements nt_sigs
			|> List.map (fun nt_sig -> BatMap.find (nt, nt_sig) nt_sig_to_expr)
			|> List.sort (fun e1 e2 -> (Exprs.size_of_expr e1) - (Exprs.size_of_expr e2))
			|> List.hd
		else
			(* find "distinguishing" boolean expressions usable for predicates *)
			let bool_sigs =
				BatSet.filter (fun bool_sig ->
					let bool_sig = List.fold_left (fun acc i -> acc @ [List.nth bool_sig i]) [] pts in
					List.exists (fun x -> (Pervasives.compare x (CBool (Concrete true))) = 0) bool_sig &&
					List.exists (fun x -> (Pervasives.compare x (CBool (Concrete false))) = 0) bool_sig
				) bool_sigs
			in
			(* learn additional predicates if no such distinguishing pred remains *)
			let bool_sigs, nt_sig_to_expr =
				if (BatSet.is_empty bool_sigs) then
					let pred_opt =
						(* for each (pt1, pt2) in Pts x Pts, learn a predicate which *)
						(* evaluates to true on pt1 and false on pt2. If we find such a *)
						(* distinguishing predicate, stop finding. *)
						List.fold_left (fun acc (pts_index1, pts_index2) ->
							if (acc <> None) || pts_index1 = pts_index2 then acc
							else
								(* constructing desired bool sig for learning predicates *)
  							let bool_sig =
    							List.fold_left (fun bool_sig i ->
  									let const =
  										if (i = pts_index1) then (CBool (Concrete true))
  										else if (i = pts_index2) then (CBool (Concrete false))
  										else
												CBool Abstract
  									in
    								bool_sig @ [const]
    							) [] (BatList.range 0 `To ((List.length desired_sig) - 1))
  							in
								(* learn vsa of predicates *)
  							let vsa =
            			learn (available_height, available_size)
            					  (bool_nt, bool_sig)
            						(spec, nt_rule_list, total_sigs, nt_to_sigs, nt_sig_to_expr)
          			in
								if vsa = Empty then acc else Some (choose_best_from_vsa vsa)
						) None (BatList.cartesian_product pts pts)
					in
					(* failed to learn a new distinguishing predicate *)
					if pred_opt = None then (bool_sigs, nt_sig_to_expr)
					else
						(* add the learnt distinguishing predicate *)
						let pred = BatOption.get pred_opt in
						let bool_sig = 
							try 
								Exprs.compute_signature_wo_exception spec pred 
							with exn -> 
								prerr_endline (Printexc.to_string exn); 
								assert false 
						in
						((BatSet.add bool_sig bool_sigs), BatMap.add (bool_nt, bool_sig) pred nt_sig_to_expr)
				else
					(bool_sigs, nt_sig_to_expr)
			in
			(* lack of predicates *)
			if (BatSet.is_empty bool_sigs) then raise LearnDTFailure
			else
			let bool_sig = BatSet.choose bool_sigs in
			let pred = try BatMap.find (bool_nt, bool_sig) nt_sig_to_expr with _ -> assert false in
			let bool_sigs' = BatSet.remove bool_sig bool_sigs in
			let left_pts =
				List.fold_left (fun acc (bool_const, i) ->
					if (get_concrete_bool bool_const) && (List.mem i pts) then acc @ [i] else acc
				) [] (List.combine bool_sig (BatList.range 0 `To ((List.length bool_sig) - 1)))
			in
			let right_pts =
				List.fold_left (fun acc (bool_const, i) ->
					if not (get_concrete_bool bool_const) && (List.mem i pts) then acc @ [i] else acc
				) [] (List.combine bool_sig (BatList.range 0 `To ((List.length bool_sig) - 1)))
			in
			(* let _ =                                                                             *)
			(* 	if (Pervasives.compare desired_sig (snd !goal)) = 0 then                          *)
			(* 	begin                                                                             *)
  		(* 		prerr_endline (Printf.sprintf "pred: %s" (Exprs.string_of_expr pred));          *)
			(* 		prerr_endline ("bool sig: " ^ (string_of_list Exprs.string_of_const bool_sig)); *)
			(* 		prerr_endline ("pts      : " ^ (string_of_list string_of_int pts));             *)
			(* 		prerr_endline ("left pts : " ^ (string_of_list string_of_int left_pts));        *)
			(* 		prerr_endline ("right pts: " ^ (string_of_list string_of_int right_pts));       *)
			(* 	end                                                                               *)
  		(* in                                                                                  *)
			let left = learnite_lbu left_pts bool_sigs' in
			let right = learnite_lbu right_pts bool_sigs' in
			Function ("ite", [pred; left; right], nt_ty)
	in
	let expr =
		(** learning ite expression with learning-based unifier *)
		(** - synthesize predicates in case of insufficiency *)
		(** - effective for synthesis problems of finite domains (e.g., strings) *)
		if !Options.lbu then
  		let bool_sigs = BatMap.find bool_nt nt_to_sigs in 
  		learnite_lbu (BatList.range 0 `To ((List.length desired_sig) - 1)) bool_sigs
		else
		(** learning ite expression with decision-tree learning *)
		(** - do NOT synthesize predicates; just give up in case of insufficiency *)
		(** - effective for synthesis problems of virtually infinite domains (e.g., BV, LIA) *)
		let pts_indices = (BatList.range 0 `To ((List.length desired_sig) - 1)) in
		let bool_sigs = BatMap.find bool_nt nt_to_sigs in
		(* cover : signature -> int BatSet.t *)
		(* (set of indices of inputs with correct outputs) *)
    let cover : (signature, int BatSet.t) BatMap.t =
    	BatSet.fold (fun nt_sig cover ->
    		let _, covered_pts =
    			List.fold_left (fun (i, acc) (const, desired_const) ->
    				if (Pervasives.compare const desired_const) = 0 then
							(i + 1, BatSet.add i acc)
    				else (i + 1, acc)
    			) (0, BatSet.empty) (List.combine nt_sig desired_sig)
    		in
    		BatMap.add nt_sig covered_pts cover
    	) nt_sigs BatMap.empty
    in
		let pt2covered_array =
			let n = (List.length desired_sig) in
			Array.make n (Array.make n 0)
		in
		let pt2covers : (int, BitSet.t list) BatMap.t =
			BatMap.foldi (fun _ pts pt2covers ->
				BatSet.fold (fun pt pt2covers ->
					let pts_list = try BatMap.find pt pt2covers with _ -> [] in
					BatMap.add pt ((intset2bitset pts) :: pts_list) pt2covers
				) pts pt2covers
			) cover BatMap.empty
		in
		let cover : (signature, BitSet.t) BatMap.t =
			BatMap.foldi (fun sg s m -> BatMap.add sg (intset2bitset s) m) cover BatMap.empty
		in
		let rec iterative_learn_dt pred_size (pts_indices, bool_sigs)
    			(available_height, available_size) (nt, desired_sig)
    			(spec, nt_rule_list, rule, nt_to_sigs, nt_sig_to_expr)
		=
			if pred_size > !Options.max_size then raise LearnDTFailure
			else
			try
				(* remove expressions which do not cover any input *)
				(* (they can't used as terms of an ite expression) *)
				let nt_to_sigs =
					BatMap.add nt
						(BatSet.filter (fun sg ->
							(BitSet.cardinal (BatMap.find sg cover)) > 0
						) nt_sigs)
						nt_to_sigs
				in
				my_prerr_endline (Printf.sprintf "pred_size: %d |bool_sigs|: %d |nt_to_sigs|:%d" pred_size (BatSet.cardinal bool_sigs) (BatMap.cardinal nt_to_sigs));
    		Dtlearning.learndt
    			(pts_indices, bool_sigs, cover, pt2covers, pt2covered_array)
    			(available_height, available_size) (nt, desired_sig)
    			(spec, nt_rule_list, rule, nt_to_sigs, nt_sig_to_expr)
  		(* failed due to lack of predicates *)
			with LearnDTFailure ->
				(* enumerate more predicates *)
				let sig_to_expr : (signature, Exprs.expr) BatMap.t =
					BatMap.foldi (fun (nt, sg) expr sig_to_expr ->
						BatMap.add sg expr sig_to_expr
					) nt_sig_to_expr BatMap.empty
				in
				let nt_to_exprs : (Grammar.rewrite, (Exprs.expr * int) BatSet.t) BatMap.t  =
					BatMap.foldi (fun nt sigs nt_to_exprs ->
						let exprs =
							set_map (fun sg ->
								let expr = BatMap.find sg sig_to_expr in
								(expr, size_of_expr expr)
							) sigs
						in
						BatMap.add nt exprs nt_to_exprs
					) nt_to_sigs BatMap.empty
				in
  			let (nt_to_sigs, nt_to_exprs, nt_sig_to_expr) =
					(* collect all production rules associated with the predicate nonterminal *)
    			let nt_rule_list =
    				List.filter (fun (nt, _) -> is_equal_nt nt bool_nt) nt_rule_list
    			in
      		get_sigs_of_size desired_sig spec (nt_to_sigs, nt_to_exprs, nt_sig_to_expr)
    				nt_rule_list (pred_size, pred_size + 1)
      	in
				let total_sigs =
      		BatMap.foldi (fun nt sigs total_sigs ->
      			BatSet.union sigs total_sigs
      		) nt_to_sigs BatSet.empty
      	in
				let bool_sigs = BatMap.find bool_nt nt_to_sigs in 
				iterative_learn_dt (pred_size + 1) (pts_indices, bool_sigs)
    			(available_height, available_size) (nt, desired_sig)
    			(spec, nt_rule_list, rule, nt_to_sigs, nt_sig_to_expr)
		in
		iterative_learn_dt (!curr_comp_size + 1) (pts_indices, bool_sigs) (available_height, available_size) (nt, desired_sig)
			(spec, nt_rule_list, rule, nt_to_sigs, nt_sig_to_expr)
	in
	(* clean up cache for entropy : should not clean up when adding more predicates *)
	let _ = Dtlearning.cache := BatMap.empty in 
	let _ = 
		if (Pervasives.compare (snd !goal) desired_sig) = 0 then
		begin
			my_prerr_endline ("ite sol: " ^ (Exprs.string_of_expr expr));
			my_prerr_endline ("available size: " ^ (string_of_int available_size));
			my_prerr_endline ("size: " ^ (string_of_int (Exprs.size_of_expr expr)))
		end 
	in
	Direct expr
	with LearnDTFailure ->
		let _ = if (Pervasives.compare desired_sig (snd !goal)) = 0 then 
  		my_prerr_endline ("learn dt failure") 
  	in 
		Empty
	| LearnForEachFailure ->
		let _ = if (Pervasives.compare desired_sig (snd !goal)) = 0 then 
  		my_prerr_endline ("learn for each failure") 
  	in 
		Empty
	| NoSolInVSA ->
		let _ = if (Pervasives.compare desired_sig (snd !goal)) = 0 then 
  		my_prerr_endline ("no sol in vsa") 
  	in 
		Empty
		
		
and learn_paths available_height i rule nts desired_sig total_sigs nt_to_sigs nt_sig_lists =
	let op = op_of_rule rule in 
	my_prerr_endline (Printf.sprintf "Processing %d-th arg of %s" i op);
	let nt_sig_lists : ((rewrite * const list) list) BatSet.t = nt_sig_lists in 
	(* the first argument *)
	if (i = 0) then  
		(* assumption : all the function rules are with just sygus builtins *)
		let nt = List.hd nts in 
		let nt_sigs = (BatMap.find nt nt_to_sigs) in 
		let arg_sigs = witness available_height nt_sigs total_sigs rule desired_sig [] in
		let nt_sig_lists : ((rewrite * const list) list) BatSet.t = 
			set_map (fun arg_sig -> [(nt, arg_sig)]) arg_sigs 
		in
		learn_paths available_height (i + 1) rule nts desired_sig total_sigs nt_to_sigs nt_sig_lists  
	(* done *)
	else if (i >= (BatList.length nts)) then
		(* remove cases where some arguments could not be learned *) 
		BatSet.filter (fun nt_sig_list -> 
			(BatList.length nt_sig_list) = (BatList.length nts)
		) nt_sig_lists
	(* i( > 1)-th argument *)
	else
		let nt = List.nth nts i in
		let nt_sigs = (BatMap.find nt nt_to_sigs) in
		(* nt_sig_lists is prefix-closed *)
		let nt_sig_lists : ((rewrite * const list) list) BatSet.t = 
			BatSet.fold (fun nt_sig_list acc ->
				if (BatList.length nt_sig_list) = i then
					let next_arg_sigs = 
						witness available_height nt_sigs total_sigs rule desired_sig (List.map snd nt_sig_list) 
					in
					let _ =
						my_prerr_endline
        		(Printf.sprintf "desired: %s args: %s next_args: %s"
        			(string_of_sig desired_sig)
							(string_of_list (fun (_,sg) -> string_of_sig sg) nt_sig_list)
							(string_of_set string_of_sig next_arg_sigs)
						)
					in
					BatSet.union acc
						(set_map (fun next_arg_sig -> nt_sig_list @ [(nt, next_arg_sig)]) next_arg_sigs)
				else acc 
			) nt_sig_lists nt_sig_lists
		in
		learn_paths available_height (i + 1) rule nts desired_sig total_sigs nt_to_sigs nt_sig_lists  
		
	
let init () = 
	let _ = learn_cache := BatMap.empty in
	let _ = now_learning := BatSet.empty in
	let _ = learn_rule_cache := BatMap.empty in 
	(* let _ = curr_comp_size := !Options.init_comp_size in   *)
	()
			

(** Main DUET algorithm *)						
let synthesis (macro_instantiator, target_function_name, grammar, forall_var_map, spec) =
	let _ = init () in 
	(* all nonterminal symbols *)
	let nts = BatMap.foldi (fun nt rules s -> BatSet.add nt s) grammar BatSet.empty in 
	(* signatures: outputs of enumerated expressions *)
	(* nt_to_sigs: outputs of enumerated expressions derivable from each nonterminal *)
	let nt_to_sigs : (rewrite, signature BatSet.t) BatMap.t = 
		BatSet.fold (fun nt m -> BatMap.add nt BatSet.empty m) nts BatMap.empty 
	in
	(* nt_to_exprs: enumerated expressions derivable from each nonterminal *) 
	let nt_to_exprs : (rewrite, (expr * int) BatSet.t) BatMap.t = 
		BatSet.fold (fun nt m -> BatMap.add nt BatSet.empty m) nts BatMap.empty 
	in
	(* size_to_nt_to_idxes: index of AST nodes whose size of expression is S from each nonterminal *)
	let size_to_nt_to_idxes : (int, (rewrite, int BatSet.t) BatMap.t) BatMap.t = BatMap.empty in
	(* nt_sig_to_expr: "(N, sig) -> expr" means expr is derivable from N and its output is sig *)
	let nt_sig_to_expr : (rewrite * signature, expr) BatMap.t = BatMap.empty in
	let desired_sig = List.map (fun (inputs, output) -> output) spec in
	(* Synthesis goal *)
	let _ = goal := (Grammar.start_nt, desired_sig) in
	(* Setting the maximum height of VSAs *)
	(*   - if the user provided a value for it, use it*)
	(*   - otherwise, log_2 (max_size) where max_size is the max. number of AST nodes of synthesized programs *)
	let max_height = 
		if !Options.max_height > 0 then !Options.max_height 
		else (log (float_of_int !Options.max_size) /. log (2.0)) |> ceil |> int_of_float 
	in
	my_prerr_endline ("max height: " ^ (string_of_int max_height));
	(* (non-terminal * production rule) list *)
	(* let nt_rule_list =                                            *)
	(* 	BatMap.foldi (fun nt rules lst ->                           *)
	(* 		BatSet.fold (fun rule lst -> (nt, rule) :: lst) rules lst *)
	(* 	) grammar []                                                *)
	(* in                                                            *)
	let nt_rule_list = get_nt_rule_list grammar in
	let rec iter max_component_size (nt_to_sigs, nt_to_exprs, nt_sig_to_expr, size_to_nt_to_idxes) =
		(* clean up caches *)
		let _ = init () in
		let _ = 
			if max_component_size > !Options.max_size then 
				failwith (Printf.sprintf "No solution within size of %d. Consider increasing the max. size (use option \"-max_size\")" 
										!Options.max_size) 
		in 
  	let prev_size_nt_sig_to_expr = BatMap.cardinal nt_sig_to_expr in
		(** Component generation via Bottom-up enumeration *)
		let start = Sys.time () in 
		let (nt_to_sigs, size_to_nt_to_idxes, idx_to_sig) =
			(* exclude ite's *)
			(* when we add components, we don't have to add ite expressions as components; *)
			(* ite expressions will be explored by a specialized mechanism (decision tree learning) *)
			let nt_rule_list = exclude_ite_rules nt_rule_list in
  		Bottomup.get_sigs_of_size desired_sig spec nts size_to_nt_to_idxes 
				nt_rule_list grammar (max_component_size, max_component_size + 1) 
  	in 
		let nt_sig_to_expr_ref = ref nt_sig_to_expr in
		(* let nt_to_sigs_ref = ref nt_to_sigs in  *)
		let adapt_start = Sys.time () in 
		let nt_to_exprs = 
			BatMap.mapi (fun nt idxes -> 
				let exprs = BatSet.map (fun idx ->
					let expr = Bottomup.expr_of_idx idx in
					let expr_sig = try BatMap.find idx idx_to_sig with _ -> assert false in
					nt_sig_to_expr_ref := BatMap.add (nt, expr_sig) expr !nt_sig_to_expr_ref;
					(* nt_to_sigs_ref := BatMap.add nt (BatSet.add expr_sig (BatMap.find nt !nt_to_sigs_ref)) !nt_to_sigs_ref; *)
					(expr, max_component_size) 
				) idxes in
				BatSet.union exprs (try BatMap.find nt nt_to_exprs with _ -> assert false)
			) (BatMap.find max_component_size size_to_nt_to_idxes)
		in
		let nt_sig_to_expr = !nt_sig_to_expr_ref in
		let _ = adapt_time := !adapt_time +. (Sys.time() -. adapt_start) in
		(* let nt_to_sigs = !nt_to_sigs_ref in *)
		let _ = bu_time := !bu_time +. (Sys.time() -. start) in
		(* set current component size *)
		(* print_endline (string_of_map (fun (nt, sig') -> (string_of_rewrite nt) ^ " + " ^ (string_of_list string_of_const sig')) string_of_expr nt_sig_to_expr); *)
		
		let _ = curr_comp_size := max_component_size in
		let _ = num_components := (BatMap.cardinal nt_sig_to_expr) in
		(* print_endline (Printf.sprintf "max_component_size : %d - #components: %d" !curr_comp_size !num_components); *)
		my_prerr_endline (Printf.sprintf "max_component_size : %d - #components: %d" !curr_comp_size !num_components);
		(* if no new component is added, or *)
		(* current_comp_size does not reach the user-provided initial component size, *)
		(* then continue generating components *)		
		if (BatMap.cardinal nt_sig_to_expr) = prev_size_nt_sig_to_expr ||  
			 max_component_size < !Options.init_comp_size then
			iter (max_component_size + 1) (nt_to_sigs, nt_to_exprs, nt_sig_to_expr, size_to_nt_to_idxes)	 
		else 
		try
			(* prerr_endline (Printf.sprintf "************ iter %d ************" max_component_size);                                                                              *)
			(* prerr_endline (Printf.sprintf "************ nt -> exprs ************");                                                                                             *)
  		(* BatMap.iter (fun nt exprs ->                                                                                                                                        *)
  		(* 	prerr_endline (Printf.sprintf "%s -> %s" (Grammar.string_of_rewrite nt) (string_of_set (fun (e,i) -> Printf.sprintf "%s (%d)" (Exprs.string_of_expr e) i) exprs)) *)
  		(* ) nt_to_exprs;                                                                                                                                                      *)
			(* prerr_endline (Printf.sprintf "************ nt -> sigs ************");                                                                                              *)
			(* BatMap.iter (fun nt sigs ->                                                                                                                                         *)
  		(* 	prerr_endline (Printf.sprintf "%s -> %s" (Grammar.string_of_rewrite nt) (string_of_set string_of_sig sigs))                                             *)
  		(* ) nt_to_sigs;                                                                                                                                                       *)
			let sol =
      	let total_sigs =
      		BatMap.foldi (fun nt sigs total_sigs ->
      			BatSet.union sigs total_sigs
      		) nt_to_sigs BatSet.empty
      	in
				let total_exprs =
      		BatMap.foldi (fun (nt,_) expr total_exprs ->
      			BatSet.add expr total_exprs
      		) nt_sig_to_expr BatSet.empty
      	in
				assert (not (BatSet.is_empty total_sigs));
				(* partition sigs according to type *)
      	(* my_prerr_endline ("components: " ^ (string_of_set string_of_sig total_sigs)); *)
				my_prerr_endline ("components: " ^ (string_of_set Exprs.string_of_expr total_exprs));
      	let ((int_sigs, bv_sigs, string_sigs, bool_sigs) as total_sigs) = 
      		(BatSet.filter (fun sg -> (type_of_signature sg) = Int) total_sigs, 
      		 BatSet.filter (fun sg -> (type_of_signature sg) = BV) total_sigs,
      		 BatSet.filter (fun sg -> (type_of_signature sg) = String) total_sigs,
      		 BatSet.filter (fun sg -> (type_of_signature sg) = Bool) total_sigs)
      	in
      	my_prerr_endline ("Components are ready to be used: ");
				(* if only a single IO example is provided, ite cannot be the answer *)
				let nt_rule_list =
					if (List.length desired_sig) = 1 then exclude_ite_rules nt_rule_list
					else nt_rule_list 
  			in
				(** Composition via Top-down propagation *)
				let start = Sys.time () in
				let vsa =
					try  
						learn (max_height, !Options.max_size) (Grammar.start_nt, desired_sig) 
							(spec, nt_rule_list, total_sigs, nt_to_sigs, nt_sig_to_expr) 
					with VSAFound vsas -> Union vsas
					| exn -> failwith (Printexc.to_string exn) 
				in
				let _ = td_time := !td_time +. (Sys.time() -. start) in
      	my_prerr_endline ("VSA has been computed");
				my_prerr_endline (string_of_vsa vsa);
				(* prerr_endline (string_of_vsa vsa); *)
				choose_best_from_vsa vsa  
  		in
  		sol 
		with NoSolInVSA -> (* no solution found *) 
			iter (max_component_size + 1) (nt_to_sigs, nt_to_exprs, nt_sig_to_expr, size_to_nt_to_idxes)
	in
	try 
		iter 1 (nt_to_sigs, nt_to_exprs, nt_sig_to_expr, size_to_nt_to_idxes)
	with Generator.SolutionFound sol ->
	(* a solution is found while generating components *) 
		sol  
 
	