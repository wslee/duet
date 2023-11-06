open Exprs 
open Grammar 
open Vocab

type addr = int list (* position of a node in an AST *)

let rec get_holes addr rule =
	match rule with 
	| NTRewrite nt_id -> [(addr, rule)] 
	| ExprRewrite expr -> []
	| FuncRewrite (op, rewrites) ->
		List.flatten (List.mapi (fun i rewrite -> get_holes (addr@[i]) rewrite) rewrites)     
	
let plug rule instances =
	let rec plug_sub curr_addr rule instances =
		match rule with
		| NTRewrite nt ->
			(try List.assoc curr_addr instances with Not_found -> assert false) 
		| ExprRewrite expr -> expr
		| FuncRewrite (op, rewrites) ->
			let children : expr list =
				(BatList.mapi (fun i rewrite -> plug_sub (curr_addr@[i]) rewrite instances) rewrites)
			in
			Function (op, children, ret_type_of_op rule)
	in
	plug_sub [] rule instances
	
		
let rec expr_of_rewrite rewrite = 
	match rewrite with 
	| NTRewrite _ -> assert false
	| ExprRewrite expr -> expr  
	| FuncRewrite (op, rewrites) ->
		let ty = ret_type_of_op rewrite in  
		let exprs = List.map expr_of_rewrite rewrites in 
		Function (op, exprs, ty)  

exception SolutionFound of expr 

(* Helper functions *)
let add_signature nt signature nt_to_sigs =
	let sigs = try BatMap.find nt nt_to_sigs with _ -> BatSet.empty in  
	BatMap.add nt (BatSet.add signature sigs) nt_to_sigs

let add_expr nt (expr, target_size) nt_to_exprs = 
	let exprs = try BatMap.find nt nt_to_exprs with _ -> BatSet.empty in 
	BatMap.add nt (BatSet.add (expr, target_size) exprs) nt_to_exprs 

let get_components nt nt_to_exprs target_size =
	List.map fst 
  	(BatSet.elements (BatSet.filter (fun (e, sz) -> sz = target_size) (BatMap.find nt nt_to_exprs)))	 


(* ret type: int list list *)
(* e.g., sum{P_i} = 4 where i in {1,2} *)
(* [ [1; 3]; [3; 1]; [2; 2] ] *)
let rec get_size_partitions holes target_size nt_to_exprs =
	match holes with 
	| [] -> [[]] 
	| (_, nt) :: tl ->
		List.fold_left (fun partitions size ->
			let components = (get_components nt nt_to_exprs size) in
			if (List.length components) > 0 then	
				let rest_partitions = get_size_partitions tl (target_size - size) nt_to_exprs in
				(*[[]]*)
				let new_partitions =
					List.filter (fun partition -> 
						(List.length partition) = (List.length holes) && 
						(BatList.sum partition) = target_size
					) (List.map (fun partition -> size :: partition) rest_partitions) 
				in
				partitions @ new_partitions 
			else partitions
		) [] (BatList.range 0 `To target_size)	 
			
(* using components found so far, generate candidates of size `target_size' *)				
let grow nt rule (nt_to_sigs, nt_to_exprs, nt_sig_to_expr) desired_sig spec target_size =
	let holes : (addr * rewrite(* NTRewrite *)) list = get_holes [] rule in
	if (List.length holes) = 0 then (nt_to_sigs, nt_to_exprs, nt_sig_to_expr)
	else
	let rule_size = size_of_rewrite rule in  
	(* let _ = my_prerr_endline (Printf.sprintf "Applying rule: %s -> %s" (string_of_rewrite nt) (string_of_rewrite rule)) in *)
	let size_partitions = get_size_partitions holes (target_size - rule_size) nt_to_exprs in
	(* let _ = my_prerr_endline (string_of_list (fun part -> string_of_list string_of_int part) size_partitions) in *)
	let upper_bounds_list = 
		List.map (fun size_partition ->
			let _ = assert ((List.length size_partition) = (List.length holes)) in
			List.map 
				(fun ((_, nt), size) -> List.length (get_components nt nt_to_exprs size)) 
				(List.combine holes size_partition)
		) size_partitions 
	in   
	let generate_function : unit -> (addr * expr) list =
		let size_partition_index = ref 0 in 
		let init_indices = List.map (fun _ -> 0) holes in 
		let curr_indices = ref init_indices in 
		fun () ->
		try begin   
			let size_partition = List.nth size_partitions !size_partition_index in 
			let result = 
  			List.map2 (fun (index, size) (addr, nt) -> 
					(addr, List.nth (get_components nt nt_to_exprs size) index)
  			) (List.combine !curr_indices size_partition)  holes
			in
			(* increment indices *)
			let upper_bounds = List.nth upper_bounds_list !size_partition_index in
			let carry, next_indices = 
				List.fold_left (fun (carry, next_indices) (index, ub) ->
					let carry', index' = 
						if index + carry >= ub then (1, 0) 
						else (0, index + carry)
					in 
					(carry', next_indices@[index'])
				) (1, []) (List.combine !curr_indices upper_bounds)
			in 
			let next_indices = 
				if carry = 1 then
					let _ = incr size_partition_index in  
					init_indices
				else next_indices 
			in
			let _ = curr_indices := next_indices in
			result
		end  
		with _ -> raise BatEnum.No_more_elements
	in
	let generator = BatEnum.from generate_function in 
		
	(* Main Loop *)
	let nt_to_sigs_ref, nt_to_exprs_ref, nt_sig_to_expr_ref = 
		(ref nt_to_sigs, ref nt_to_exprs, ref nt_sig_to_expr) 
	in  
	try begin
		while true do
			let instances = BatEnum.get_exn generator in  
			let expr = plug rule instances in
			try
				let signature = compute_signature spec expr in
				let expr_sigs = (BatMap.find nt !nt_to_sigs_ref) in
				(* if (compare desired_sig signature) = 0 then *)
				(* 	raise (SolutionFound expr)                *)
				(* else                                        *)
				if not (BatSet.mem signature expr_sigs) then
					(* let _ = my_prerr_endline (Printf.sprintf "Generated: %s %s" (Exprs.string_of_expr expr) (string_of_signature signature)) in *)
					(* New candidiate found. Update *)
					let _ = nt_to_sigs_ref := add_signature nt signature !nt_to_sigs_ref in 
					let _ = nt_to_exprs_ref := add_expr nt (expr, size_of_expr expr) !nt_to_exprs_ref in
					let _ = nt_sig_to_expr_ref := BatMap.add (nt,signature) expr !nt_sig_to_expr_ref in  
					()
				else
					(* let _ = my_prerr_endline (Printf.sprintf "Removed as redundancy: %s" (Exprs.string_of_expr expr)) in *)
					()
			with UndefinedSemantics -> ()
		done; (* unreachable *)
		(!nt_to_sigs_ref, !nt_to_exprs_ref, !nt_sig_to_expr_ref)
	end
	with BatEnum.No_more_elements ->  
			(!nt_to_sigs_ref, !nt_to_exprs_ref, !nt_sig_to_expr_ref)


(* grammar: (rewrite, rewrite BatSet.t) BatMap.t *)
(* spec: ((const list) * const) list *)	
(* let enum_bu_search grammar spec =                                                                                                                                               *)
(* 	let nts = BatMap.foldi (fun nt rules s -> BatSet.add nt s) grammar BatSet.empty in                                                                                            *)
(* 	let nt_to_sigs : (rewrite, signature BatSet.t) BatMap.t =                                                                                                                     *)
(* 		BatSet.fold (fun nt m -> BatMap.add nt BatSet.empty m) nts BatMap.empty                                                                                                     *)
(* 	in                                                                                                                                                                            *)
(* 	let nt_to_exprs : (rewrite, (expr * int) BatSet.t) BatMap.t =                                                                                                                 *)
(* 		BatSet.fold (fun nt m -> BatMap.add nt BatSet.empty m) nts BatMap.empty                                                                                                     *)
(* 	in                                                                                                                                                                            *)
(* 	let nt_sig_to_expr : (rewrite * signature, expr) BatMap.t = BatMap.empty in                                                                                                   *)
(* 	let desired_sig = List.map (fun (inputs, output) -> output) spec in                                                                                                           *)
(* 	let nt_rule_list = get_nt_rule_list grammar in                                                                                                                                *)
(* 	(* process candidates of size 1 *)                                                                                                                                            *)
(* 	try                                                                                                                                                                           *)
(*   	let (nt_to_sigs, nt_to_exprs, nt_sig_to_expr) =                                                                                                                             *)
(*   		List.fold_left (fun (nt_to_sigs, nt_to_exprs, nt_sig_to_expr) (nt, rule) ->                                                                                               *)
(*   			let holes = get_holes [] rule in                                                                                                                                        *)
(*   			if (List.length holes) = 0 then                                                                                                                                         *)
(*   				let expr = (expr_of_rewrite rule) in                                                                                                                                  *)
(*   				let signature = compute_signature spec expr in                                                                                                                        *)
(* 					if (compare desired_sig signature) = 0 then raise (SolutionFound expr)                                                                                                *)
(*   				else (add_signature nt signature nt_to_sigs, add_expr nt (expr, 1) nt_to_exprs,                                                                                       *)
(* 								BatMap.add (nt, signature) expr nt_sig_to_expr)                                                                                                                 *)
(*   			else (nt_to_sigs, nt_to_exprs, nt_sig_to_expr)                                                                                                                          *)
(*   		) (nt_to_sigs, nt_to_exprs, nt_sig_to_expr) nt_rule_list                                                                                                                  *)
(*   	in                                                                                                                                                                          *)
(*   	let rec iter size (nt_to_sigs, nt_to_exprs, nt_sig_to_expr) =                                                                                                               *)
(* 			(if (size > !Options.max_size) then failwith (Printf.sprintf "No solution of size < %d !" !Options.max_size));                                                            *)
(*   		(* my_prerr_endline (Printf.sprintf "-- Size : %d --" size);                                                                                                           *) *)
(* 			(* my_prerr_endline ("-- # Components: --");                                                                                                                           *) *)
(* 			(* BatSet.iter (fun nt ->                                                                                                                                              *) *)
(* 			(* 	my_prerr_endline (Printf.sprintf "%s : %d" (string_of_rewrite nt) (BatSet.cardinal (BatMap.find nt nt_to_exprs)));                                                *) *)
(* 			(* 	List.iter (fun sz ->                                                                                                                                              *) *)
(* 			(* 		let components = (get_components nt nt_to_exprs sz) in                                                                                                          *) *)
(* 			(* 		if (List.length components) > 0 then                                                                                                                            *) *)
(* 			(* 			my_prerr_endline (string_of_list string_of_expr components)                                                                                                   *) *)
(* 			(* 	) (BatList.range 1 `To size);                                                                                                                                     *) *)
(* 			(* 	my_prerr_endline (string_of_map string_of_rewrite (fun sigs -> string_of_set string_of_signature sigs) nt_to_sigs);                                               *) *)
(* 			(* ) nts;                                                                                                                                                              *) *)
(* 			(* my_prerr_endline (Printf.sprintf "************ nt -> exprs ************");                                                                                          *) *)
(*   		(* BatMap.iter (fun nt exprs ->                                                                                                                                        *) *)
(*   		(* 	prerr_endline (Printf.sprintf "%s -> %s" (Grammar.string_of_rewrite nt) (string_of_set (fun (e,i) -> Printf.sprintf "%s (%d)" (Exprs.string_of_expr e) i) exprs)) *) *)
(*   		(* ) nt_to_exprs;                                                                                                                                                      *) *)
(*   		let nt_sig_to_expr' = nt_sig_to_expr in                                                                                                                                   *)
(* 			let (nt_to_sigs, nt_to_exprs, nt_sig_to_expr) =                                                                                                                           *)
(* 				List.fold_left (fun (nt_to_sigs, nt_to_exprs, nt_sig_to_expr) (nt, rule) ->                                                                                             *)
(* 					grow nt rule (nt_to_sigs, nt_to_exprs, nt_sig_to_expr) desired_sig spec size                                                                                          *)
(* 				) (nt_to_sigs, nt_to_exprs, nt_sig_to_expr) nt_rule_list                                                                                                                *)
(*   		in                                                                                                                                                                        *)
(* 			iter (size + 1) (nt_to_sigs, nt_to_exprs, nt_sig_to_expr)                                                                                                                 *)
(*   	in                                                                                                                                                                          *)
(* 		iter 2 (nt_to_sigs, nt_to_exprs, nt_sig_to_expr)                                                                                                                            *)
(* 	with SolutionFound sol -> sol                                                                                                                                                 *)
	