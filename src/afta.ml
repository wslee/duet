open Grammar
open Exprs
open Vocab
open Core_kernel
open AftaUtils


let dummy_state = (NTRewrite "", []) 

(* all states * final states * transitions *)
type t = (StateSet.t) * (StateSet.t) * (TransitionSet.t)

let empty_afta = (StateSet.empty, StateSet.empty, TransitionSet.empty) 

type hypergraph = (StateSet.t) * (EdgeSet.t)
	

let construct_hgraph (states, final_states, transitions) state2expr =
	(* add a dummy to states  *)
	let states = StateSet.add dummy_state states in 
	(* connect a dummy to all terminals *)
	let terminal_nodes = BatMap.foldi (fun k _ acc -> StateSet.add k acc) state2expr StateSet.empty in 
	let transitions =
		StateSet.fold (fun terminal_node transitions -> 
			TransitionSet.add ("", [dummy_state], terminal_node) transitions
		) terminal_nodes transitions 
	in 
	 
	let barc2op =
		TransitionSet.fold (fun (op, states, state) barc2op ->
			BatMap.add (states, state) op barc2op 
		) transitions BatMap.empty   
	in
	(* fs: node -> barc BatSet.t (outgoing edges) *)
	(* add dummy to terminal_nodes *)
	let fs = 
		StateSet.fold (fun terminal_node fs ->
			let fs_vals = try BatMap.find dummy_state fs with _ -> EdgeSet.empty in
			BatMap.add dummy_state (EdgeSet.add ([dummy_state], terminal_node) fs_vals) fs	 
		) terminal_nodes BatMap.empty  
	in
	let fs =
		TransitionSet.fold (fun (op, states, state) fs ->
			BatList.fold_left (fun fs state'  ->
				let fs_vals = try BatMap.find state' fs with _ -> EdgeSet.empty in 
				BatMap.add state' (EdgeSet.add (states, state) fs_vals) fs   
			) fs states   
		) transitions fs
	in  
	let nodes = states in 
	let edges = 
		TransitionSet.fold (fun (op, states, state) edges -> EdgeSet.add (states, state) edges)
			transitions EdgeSet.empty  
	in 
	((nodes, edges), barc2op, fs)
	
let rec get_f tails w = 
	if (List.length tails) = 0 then 0 (* root node *) 
	else BatList.max (BatList.map (fun tail -> try BatMap.find tail w with _ -> 0 (* failwith (string_of_states (BatSet.singleton tail)) *) ) tails) 

let compute_sbt	final_states ((nodes, edges), barc2op, fs) =
	let get_fs k = try BatMap.find k fs with _ -> EdgeSet.empty in
	let get_w m k = try BatMap.find k m with _ -> int_max in
	let get_k m k = try BatMap.find k m with _ -> 0 in
	(* pv *)
	let pv = ref BatMap.empty in  
	(* w *) 
	let w = ref BatMap.empty in (* node -> int *)
		let set_w n c = w := BatMap.add n c !w in
	(* k *)	     
	let k = ref BatMap.empty in (* edge -> int *)
		let set_k i c = k := BatMap.add i c !k in 
	let q = 
		Heap.Removable.create ~min_size:1024 
		~cmp:(fun (w1,_) (w2,_) -> w1 - w2) () 
	in
	let token_map = ref BatMap.empty in  	
		let pick_from_q () = 
			let (weight, node) as elem = 
				match Heap.Removable.pop q with
				| Some (weight, node) -> (weight, node)
				| None -> failwith "No solution!"  
			in
			elem
		in
		let add_q ((weight, node) as elem) =
			begin 
				if (BatMap.mem elem !token_map) then 
					let token = BatMap.find elem !token_map in  	
					let token = Heap.Removable.update q token elem in 
					let _ = token_map := BatMap.add elem token !token_map in 
					false 
				else 
					let token = Heap.Removable.add_removable q elem in 
					let _ = token_map := BatMap.add elem token !token_map in 
					true   
			end  
		in     
	(* initialization *)
	let _ = add_q (0, dummy_state) in
	let _ = set_w dummy_state 0 in
	(* tail -> head  |head| = 1 *)
	(* edge: (state list) * state *)
	while not (Heap.Removable.is_empty q) do
		let _,u = pick_from_q () in
		my_prerr_endline ("Chosen: " ^ (string_of_state u));
		EdgeSet.iter (fun ((tail_e_j, y) as e_j) ->
			my_prerr_endline ("Successor: " ^ (string_of_state y));
			let w_e_j = 1 in (* TODO *)
			set_k e_j ((get_k !k e_j) + 1);
			my_prerr_endline ("|tail| = " ^ (string_of_int (List.length tail_e_j)));
			my_prerr_endline ("|k_j| = " ^ (string_of_int (get_k !k e_j)));
			if (get_k !k e_j) = (StateSet.cardinal (StateSet.of_list tail_e_j)) then
			begin  
				let f = get_f tail_e_j !w in
				my_prerr_endline ("|w(y)| = " ^ (string_of_int (get_w !w y)));
				my_prerr_endline ("|w_e_j + f| = " ^ (string_of_int (w_e_j + f)));
				if (get_w !w y) > w_e_j + f then 
				begin 
					let w_y = (w_e_j + f) in  
					if (add_q (w_y, y)) then 
					begin 
						my_prerr_endline ("Pushed to queue: " ^ (string_of_state y));
						if (get_w !w y) < int_max then 
							EdgeSet.iter (fun e_h -> set_k e_h ((get_k !k e_h) - 1)) (get_fs y)
					end;	 
					set_w y w_y; 
					my_prerr_endline ("Pushed to pv: " ^ (string_of_state y));
					pv := BatMap.add y e_j !pv  	 
				end
  		end
		) (get_fs u) 		 
	done;
	(* let _ = assert (BatMap.mem (BatSet.choose final_states) !pv) in  *)
	!pv
 
let fun_apply_signature : string -> signature list -> signature 
= fun op values ->
	try 
		Exprs.fun_apply_signature op values 
	with
	| _ -> raise UndefinedSemantics 
	
(* var const 도 그냥 q_nt 로. 대신 state -> expr 매핑 필요. (나중에 expr_from_state에서 써야함) *) 
let apply_var_const_rule states nt_rule_list spec =
	BatList.fold_left (fun (states, state2expr) (nt, rule) ->
		match rule with
		| ExprRewrite expr ->
			let signature = (Exprs.compute_signature spec expr) in
			(StateSet.add (nt, signature) states, BatMap.add (nt, signature) expr state2expr)
		| _ -> (states, state2expr)
	) (states, BatMap.empty) nt_rule_list
	
exception SolutionFound of (StateSet.t) * (StateSet.t) * (TransitionSet.t)


let apply_prod_rule final_asig states transitions (nt, rule) spec = 
	(* let inputs_len = try List.length spec with _ -> failwith "No spec!" in *)
	let cartesian_time = ref 0.0 in 
	let func_time = ref 0.0 in
	let op = match rule with 
  	| FuncRewrite (op, _) -> op 
  	| _ -> failwith "apply_prod_rule" 
	in		  
	let children_nt_states_list =
		BatList.map (fun child_nt ->
			(StateSet.filter (fun (nt', _) ->
				(compare child_nt nt') = 0
			)
			states
			) |> StateSet.elements (* IMPORTANT: "states" not "new_states" *)   
		) (get_nts rule)   
	in
	let start = Sys.time() in 
	let children_nt_states_list = BatList.n_cartesian_product children_nt_states_list in
	(* prerr_endline (Printf.sprintf "# children_nt_states : %d" (BatList.length children_nt_states_list)); *)
	let _ = cartesian_time := (Sys.time() -. start) +. !cartesian_time in
	(* let _ = prerr_endline (Printf.sprintf "%.2f" !cartesian_time) in *)
	(* prerr_endline (string_of_rewrite rule); *)
	BatList.fold_left (fun (new_states, new_transitions) children_nt_states ->
		try 
			let start = Sys.time() in
  		let asig = fun_apply_signature op (BatList.map (fun (_,asg) -> asg) children_nt_states) in 
  		let _ = func_time := (Sys.time() -. start) +. !func_time in
  		(* let new_state = (nt, asig) in *)
  		(* let _ = prerr_endline ("performing " ^ op) in                                         *)
  		(* BatList.iter (fun state -> prerr_endline (string_of_state state)) children_nt_states; *)
  		let new_states, new_transitions = 
  			let new_state = (nt, asig) in
  			(* prerr_endline (string_of_state new_state);    *)
  			(StateSet.add new_state new_states,
  			 TransitionSet.add (op, children_nt_states, new_state) new_transitions)
  		in
  		if (BatList.for_all2 (fun x y -> (compare x y) = 0) final_asig asig) then
  			(* let _ = prerr_endline (Printf.sprintf "%.2f %.2f" !cartesian_time !func_time) in   *)
  			raise (SolutionFound(new_states, StateSet.singleton (nt, asig), new_transitions))
  		else  
  			(new_states, new_transitions)
		with UndefinedSemantics -> (new_states, new_transitions)	 
	) (states, transitions) children_nt_states_list
	
	
let compute_g final_asig (nt, asig) =
	if !Options.no_astar then (0, 0)
	else
  	let final_asig_ty = type_of_signature final_asig in
  	if (Pervasives.compare (type_of_signature asig) final_asig_ty) <> 0 then
  		(0, 0)
		else 
			let dists =
				BatList.map (fun (i,j) ->
					try 
					let dist = 
						match final_asig_ty with 
						| Int -> 
							let (i_value, j_value) = (get_int i, get_int j) in
							(1, (abs (i_value - j_value)))
						| BV -> 
							let (i_value, j_value) = (get_bv i, get_bv j) in
							let diff = 
  							let str1 = (BatBig_int.to_string_in_binary (BatBig_int.big_int_of_int64 i_value)) in
    						let str2 = (BatBig_int.to_string_in_binary (BatBig_int.big_int_of_int64 j_value)) in
    						BatString.edit_distance str1 str2
							in 
							(1, diff)
							(* let (i_value, j_value) = (get_bv i, get_bv j) in                       *)
							(* let diff = Int64.to_int_exn (Int64.abs (Int64.(-) i_value j_value)) in *)
							(* diff                                                                   *)
						| Bool -> 
							let (i_value, j_value) = (get_bool i, get_bool j) in
							if (i_value = j_value) then (0, 0) else (1, 0) 
						| String -> 
							let (i_value, j_value) = (get_string i, get_string j) in
							let diff = BatString.edit_distance i_value j_value in
							if (share_prefix i_value j_value) || (share_suffix i_value j_value) then (1, diff) 
							else (2, diff)  	
					in
					dist
					with _ -> (int_max, int_max)
				) (BatList.combine asig final_asig)
			in 
			BatList.max dists
		
(* Given a rule n -> (op n_1 ... n_m), states S, and a curr_state s *)
(* return [(n_1, sig_1), ... ,(n_m, sig_m)] including s *)
(* cond 1. each (n_i, sig_i) in S*)
(* cond 2. s in S *)				
let get_children_states_generator rule state_list curr_state = 
	let rec get_nts rewrite =
		match rewrite with 
		| FuncRewrite (op, rewrites) ->
			BatList.fold_left (fun acc rewrite' -> acc @ (get_nts rewrite')) [] rewrites
		| NTRewrite _ -> [rewrite] 
		| _ -> []   
	in
	(* [nt1, nt2, ..., nt_m] *)
	let nts = get_nts rule in
	(* [ [(nt1,sg11) ...], [(nt2,sg21) ...], ..., [(nt_m,sg_m1) ...] ] *)
	let states_list = 
		BatList.map (fun nt ->
			BatList.filter (fun (nt',_) -> (Pervasives.compare nt nt') = 0) state_list			  
		) nts 
	in
	(* [(i,j), ...] where nt_i = nt(curr_state), sg_ij = sig(curr_state) *) 
	let _, curr_state_positions = 
		BatList.fold_left (fun (i, acc) states ->
			try 
  			let j,_ = 
					BatList.findi (fun _ state -> (Pervasives.compare state curr_state) = 0) states 
				in  
  			(i + 1, acc @ [(i, j)])
			with _ -> (i + 1, acc)
		) (0, []) states_list 	 
	in
	let upper_bounds = BatList.map (fun states -> BatList.length states) states_list in
	let generate_function : unit -> state list =
		let curr_state_positions_index = ref 0 in 
		let init_indices = 
			BatList.make (BatList.length states_list) 0
			|> BatList.modify_at 0 (fun _ -> -1) 
		in 
		let curr_indices = ref init_indices in
		fun () ->
			if !curr_state_positions_index >= (BatList.length curr_state_positions) then 
				raise BatEnum.No_more_elements
			else 
				let curr_state_position : (int * int) = 
  				BatList.nth curr_state_positions !curr_state_positions_index 
  			in
  			(* increment indices *)
  			let carry, next_indices = 
  				BatList.fold_left (fun (carry, next_indices) (i, (index, ub)) ->
  					if i = (fst curr_state_position) then
  						 (carry, next_indices@[snd curr_state_position])
  					else 
    					let carry', index' = 
    						if index + carry >= ub then (1, 0) 
    						else (0, index + carry)
    					in 
    					(carry', next_indices@[index'])
  				) (1, [])
  				(BatList.combine
  					(BatList.range 0 `To ((BatList.length upper_bounds) - 1)) 
  					(BatList.combine !curr_indices upper_bounds)
  				)
  			in 
  			let _ = if carry = 1 then incr curr_state_positions_index in
  			let _ = curr_indices := next_indices in
  			let _, indices =
  				BatList.fold_left (fun (i, acc) index -> 
  					if (i = (fst curr_state_position)) then 
  						(i + 1, acc @ [(snd curr_state_position)])
  					else (i + 1, acc @ [index])
  				) (0, []) !curr_indices 
  			in 
  			(* states to be returned *)	
  			let result =
  				BatList.map (fun (index, state_list) -> 
  					BatList.nth state_list index 	 
  				) (BatList.combine indices states_list)
  			in
  			result
	in  
	let generator = BatEnum.from generate_function in
	generator 
	

let get_op_of_rule rule = 
	let op = match rule with 
  	| FuncRewrite (op, _) -> op 
  	| _ -> failwith "get_op_of_rule" 
	in
	op
													
let h_time = ref 0.0 
let apply_time = ref 0.0	
let astar_search final_sig spec nt_rule_list (states, transitions) =
	let curr_states = ref states in 
	let curr_transitions = ref transitions in 
	(* w (cost_so_far) *)
	let w = ref BatMap.empty in (* node -> int *)
    let set_w n c = w := BatMap.add n c !w in
		let get_w n = try BatMap.find n !w with _ -> int_max in
	(* priority queue *)
	let q = 
		Heap.Removable.create ~min_size:1024 
		~cmp:(fun ((f1,(g1,t1)),s1) ((f2,(g2,t2)),s2) ->
			let v = (f1 + g1) - (f2 + g2) in 
			if v = 0 then (t1 - t2) else v 
		) () 
	in
	let token_map = ref BatMap.empty in  	
		let pick_from_q () = 
			let (weight, node) as elem = 
				match Heap.Removable.pop q with
				| Some (weight, node) -> (weight, node)
				| None -> failwith "No solution!"  
			in
			elem
		in
		let add_q ((weight, node) as elem) =
			begin 
				if (BatMap.mem elem !token_map) then 
					let token = BatMap.find elem !token_map in  	
					let token = Heap.Removable.update q token elem in 
					token_map := BatMap.add elem token !token_map
				else 
					let token = Heap.Removable.add_removable q elem in 
					token_map := BatMap.add elem token !token_map  
			end  
		in     
	(* initialization *)
	StateSet.iter (fun state ->
		let h_next = compute_g final_sig state in
		add_q ((0, h_next), state)
	) states; 
	(* main loop *)
	while not (Heap.Removable.is_empty q) do
		let _ = prerr_endline (Printf.sprintf "# states: %d" (StateSet.cardinal !curr_states)) in	
		let ((c_f, (c_g, c_t)), ((n, c_sig) as curr_node)) = pick_from_q () in
		let _ = prerr_endline (Printf.sprintf "chosen: %s - cost %d" (string_of_state curr_node) (c_f + c_g)) in
		if (BatList.for_all2 (fun x y -> (compare x y) = 0) final_sig c_sig) then 
			raise (SolutionFound(!curr_states, (StateSet.singleton curr_node), !curr_transitions))
		else
		let iter_states = !curr_states in	 
		BatList.iter (fun (n0, rule) ->
			if (is_function_rule rule) then
			begin
				let op = get_op_of_rule rule in
				let generator = get_children_states_generator rule (StateSet.elements iter_states) curr_node in
				try 
				while true do 
  				let child_states = BatEnum.get_exn generator in
					try 
    				(* if (BatList.mem curr_node child_states) then *)
  					begin  
							(* let _ = prerr_endline (Printf.sprintf "(%s %s)" op (string_of_statelist child_states)) in *)
      				let child_sigs = BatList.map snd child_states in 
      				let sig' = fun_apply_signature op child_sigs in 
      				let s' = (n0, sig') in
							(* let _ = prerr_endline ("s': " ^(string_of_state s')) in *)
							if not (StateSet.mem s' !curr_states) then
							(* if not (TransitionSet.mem (op, child_states, s') !curr_transitions) then  *)
							begin
      					curr_states := StateSet.add s' !curr_states; 
								let _ = prerr_endline ("added: " ^(string_of_state s')) in
      					curr_transitions := TransitionSet.add (op, child_states, s') !curr_transitions; 
      					let g_next = compute_g final_sig s' in
      					let new_cost = (c_f + 1, g_next) in
								add_q (new_cost, s')
							end
  					end
					with UndefinedSemantics -> ()  
				done
				with BatEnum.No_more_elements -> ()
			end 
		) nt_rule_list 
	done


let rec get_f tails w = 
	if (List.length tails) = 0 then 0 (* root node *) 
	else BatList.max (BatList.map (fun tail -> try BatMap.find tail w with _ -> 0 (* failwith (string_of_states (BatSet.singleton tail)) *) ) tails) 

let astar_search_with_pv final_sig spec nt_rule_list init_states =
	let get_w m k = try BatMap.find k m with _ -> int_max in
	let get_k m k = try BatMap.find k m with _ -> 0 in
	(* pv *)
	let pv = ref BatMap.empty in  
	(* w *) 
	let w = ref BatMap.empty in (* node -> int *)
		let set_w n c = w := BatMap.add n c !w in
	(* k *)	     
	let k = ref BatMap.empty in (* edge -> int *)
		let set_k i c = k := BatMap.add i c !k in 
	(* Priority Queue *)
	let q = 
		Heap.Removable.create ~min_size:1024 
		~cmp:(fun (w1,_) (w2,_) -> w1 - w2) () 
	in
	let token_map = ref BatMap.empty in  	
		let pick_from_q () = 
			let (weight, node) as elem = 
				match Heap.Removable.pop q with
				| Some (weight, node) -> (weight, node)
				| None -> failwith "No solution!"  
			in
			elem
		in
		let add_q ((weight, node) as elem) =
			begin 
				if (BatMap.mem elem !token_map) then 
					let token = BatMap.find elem !token_map in  	
					let token = Heap.Removable.update q token elem in 
					let _ = token_map := BatMap.add elem token !token_map in 
					false 
				else 
					let token = Heap.Removable.add_removable q elem in 
					let _ = token_map := BatMap.add elem token !token_map in 
					true   
			end  
		in     
	let barc2op = BatMap.empty in 
	let states = ref init_states in
	let dummy_edges =
		StateSet.fold (fun s acc -> EdgeSet.add (create_edge [dummy_state] s) acc) init_states EdgeSet.empty  
	in  
	let fs = ref (BatMap.add dummy_state dummy_edges BatMap.empty) in 
	let get_fs curr_state =
		if (BatMap.mem curr_state !fs) then BatMap.find curr_state !fs
		else (* 중복 연산 많음 *)
		begin
			let edges = 
  			BatList.fold_left (fun acc (n0, rule) ->
  				if (is_function_rule rule) then
  					let generator = 
							let curr_w = get_w !w curr_state in 
							let states = StateSet.filter (fun s -> (get_w !w s) <= curr_w) !states |> StateSet.elements in   
							get_children_states_generator rule states curr_state 
						in
  					let op = get_op_of_rule rule in 
  					BatEnum.fold (fun acc child_states ->
							try 
								let child_sigs = BatList.map sig_of_state child_states in 
    						let sig' = fun_apply_signature op child_sigs in 
        				let s' = (n0, sig') in
								if (Pervasives.compare curr_state s') = 0 then acc
								else 
      						let edge = (create_edge child_states s') in 
      						EdgeSet.add edge acc 		 
							with UndefinedSemantics -> acc
  					) acc generator 
  				else acc 					
  			) EdgeSet.empty nt_rule_list
			in 
			let _ = fs := BatMap.add curr_state edges !fs in 
			edges 		
		end	 
	in
	
	(* initialization *)
	let _ = add_q (0, dummy_state) in
	let _ = set_w dummy_state 0 in
	(* tail -> head  |head| = 1 *)
	(* edge: (state list) * state *)
	try 
	while not (Heap.Removable.is_empty q) do
		let cost,u = pick_from_q () in
		my_prerr_endline (Printf.sprintf "Chosen: %s - %d (|states|: %d)" (string_of_state u) cost (StateSet.cardinal !states));
		EdgeSet.iter (fun ((tail_e_j, y) as e_j) ->
			my_prerr_endline (Printf.sprintf "{%s} -> %s" (string_of_statelist tail_e_j) (string_of_state y));
			let w_e_j = 1 in (* TODO *)
			(* set_k e_j ((get_k !k e_j) + 1);                                          *)
			(* my_prerr_endline ("|k_j| = " ^ (string_of_int (get_k !k e_j)));          *)
			(* if (get_k !k e_j) = (StateSet.cardinal (StateSet.of_list tail_e_j)) then *)
			begin  
				let f = get_f tail_e_j !w in
				(* my_prerr_endline ("|w(y)| = " ^ (string_of_int (get_w !w y))); *)
				if (get_w !w y) > w_e_j + f then 
				begin 
					my_prerr_endline ("|w_e_j + f| = " ^ (string_of_int (w_e_j + f)));
					pv := BatMap.add y e_j !pv;
					let _ = 
						if (BatList.for_all2 (fun x y -> (compare x y) = 0) final_sig (sig_of_state y)) then 
							raise (SolutionFound (StateSet.empty, StateSet.empty, TransitionSet.empty))
					in 
					let w_y = (w_e_j + f) in  
					if (add_q (w_y, y)) then 
					begin 
						states := StateSet.add y !states; 
						my_prerr_endline ("Pushed to queue: " ^ (string_of_state y));
						(* if (get_w !w y) < int_max then                                        *)
						(* 	EdgeSet.iter (fun e_h -> set_k e_h ((get_k !k e_h) - 1)) (get_fs y) *)
					end;	 
					set_w y w_y; 
					my_prerr_endline ("Pushed to pv: " ^ (string_of_state y));  	 
				end
  		end
		) (get_fs u)
	done;
	(* let _ = assert (BatMap.mem (BatSet.choose final_states) !pv) in  *)
	!pv						
	with SolutionFound _ -> !pv    








let filter_out asig final_asig = 
	let ty_asig = (type_of_signature asig) in
	let ty_final_asig = (type_of_signature final_asig) in
	if (Pervasives.compare ty_asig ty_final_asig) <> 0 then false 
	else
		match ty_asig with 
		| String ->
			BatList.exists2 (fun c1 c2 ->
				let v1 = get_string c1 in
				let v2 = get_string c2 in
				(String.length v1) > (String.length v2)     
			) asig final_asig    
		(* | BV ->                         *)
		(* 	BatList.exists2 (fun c1 c2 -> *)
		(* 		let v1 = get_bv c1 in       *)
		(* 		let v2 = get_bv c2 in       *)
		(* 		(Int64.(>) v1 v2)           *)
		(* 	) asig final_asig             *)
		| _ -> false   


let apply_prod_rule final_asig states transitions (nt, rule) spec = 
	(* let inputs_len = try List.length spec with _ -> failwith "No spec!" in *)
	let cartesian_time = ref 0.0 in 
	let func_time = ref 0.0 in
	let op = match rule with 
  	| FuncRewrite (op, _) -> op 
  	| _ -> failwith "apply_prod_rule" 
	in
	let rec get_nts rewrite =
		match rewrite with 
		| FuncRewrite (op, rewrites) ->
			BatList.fold_left (fun acc rewrite' -> acc @ (get_nts rewrite')) [] rewrites
		| NTRewrite _ -> [rewrite] 
		| _ -> []   
	in		  
	let children_nt_states_list =
		BatList.map (fun child_nt ->
			(StateSet.filter (fun (nt', _) ->
				(compare child_nt nt') = 0
			)
			states
			) |> StateSet.elements (* IMPORTANT: "states" not "new_states" *)   
		) (get_nts rule)   
	in
	let start = Sys.time() in 
	let children_nt_states_list = BatList.n_cartesian_product children_nt_states_list in
	(* prerr_endline (Printf.sprintf "# children_nt_states : %d" (BatList.length children_nt_states_list)); *)
	let _ = cartesian_time := (Sys.time() -. start) +. !cartesian_time in
	(* let _ = prerr_endline (Printf.sprintf "%.2f" !cartesian_time) in *)
	(* prerr_endline (string_of_rewrite rule); *)
	BatList.fold_left (fun (new_states, new_transitions) children_nt_states ->
		try 
			(* prerr_endline (string_of_list string_of_state children_nt_states); *)
			(* let left_child = (BatList.nth children_nt_states 0) in   *)
			(* let right_child = (BatList.nth children_nt_states 1) in  *)
  		(* let _ = prerr_endline (Printf.sprintf "%d %d" (BatSet.cardinal new_states) (BatSet.cardinal new_transitions)) in *)
  		
			(* if (Grammar.is_commutative_rule rule) then                                              *)
			(* 	let left_child = (BatList.nth children_nt_states 0) in                                *)
			(* 	let right_child = (BatList.nth children_nt_states 1) in                               *)
			(* 	if (Pervasives.compare left_child right_child) > 0 then (new_states, new_transitions) *)
			(* else                                                                                    *)
			let start = Sys.time() in
  		let asig = fun_apply_signature op (BatList.map (fun (_,asg) -> asg) children_nt_states) in
			if (filter_out asig final_asig) then
				(* let _ = prerr_endline (Printf.sprintf "=== filtered out: %s ===" (string_of_sig asig)) in  *)
				(new_states, new_transitions)	  
			else  
    		let _ = func_time := (Sys.time() -. start) +. !func_time in
    		(* let new_state = (nt, asig) in *)
    		(* let _ = prerr_endline ("performing " ^ op) in                                         *)
    		(* BatList.iter (fun state -> prerr_endline (string_of_state state)) children_nt_states; *)
    		let new_states, new_transitions = 
    			let new_state = (nt, asig) in
    			(* prerr_endline (string_of_state new_state);    *)
    			(StateSet.add new_state new_states,
    			 TransitionSet.add (op, children_nt_states, new_state) new_transitions)
    		in
    		if (BatList.for_all2 (fun x y -> (compare x y) = 0) final_asig asig) then
    			(* let _ = prerr_endline (Printf.sprintf "%.2f %.2f" !cartesian_time !func_time) in   *)
    			raise (SolutionFound(new_states, StateSet.singleton (nt, asig), new_transitions))
    		else  
    			(new_states, new_transitions)
		with UndefinedSemantics -> (new_states, new_transitions)	 
	) (states, transitions) children_nt_states_list


let compute_h spec new_modulus hmap inputs_len (states, transitions) final_asig ops =
	if !Options.no_astar then (0, dummy_state, hmap)
	else
	let final_asig_ty = type_of_signature final_asig in  
	let h_value, closest_state =
  	StateSet.fold (fun ((nt, asig) as state) (h_value, closest_state) ->
			if (Pervasives.compare (type_of_signature asig) final_asig_ty) <> 0 then 
				(h_value, closest_state) 
			else    
  		let dists =
				BatList.map (fun (i,j) ->
					try 
					let diff = 
						match final_asig_ty with 
						| Int -> 
							let (i_value, j_value) = (get_int i, get_int j) in
							(abs (i_value - j_value))
						| BV ->
							(* let (i_value, j_value) = (get_bv i, get_bv j) in                                     *)
							(* let str1 = (BatBig_int.to_string_in_binary (BatBig_int.big_int_of_int64 i_value)) in *)
  						(* let str2 = (BatBig_int.to_string_in_binary (BatBig_int.big_int_of_int64 j_value)) in *)
  						(* BatString.edit_distance str1 str2                                                    *)
							let (i_value, j_value) = (get_bv i, get_bv j) in
							let diff = Int64.to_int_exn (Int64.abs (Int64.(-) i_value j_value)) in
							diff
						| Bool -> 
							let (i_value, j_value) = (get_bool i, get_bool j) in
							if (i_value = j_value) then 0 else 1 
						| String -> 
							let (i_value, j_value) = (get_string i, get_string j) in
							let diff = BatString.edit_distance i_value j_value in 
							(* let _ = prerr_endline (Printf.sprintf "%s - %s = %d" i_value j_value diff) in  *)
							diff
					in
					diff
					with _ -> int_max
				) (BatList.combine asig final_asig)
			in 
			let dist = BatList.sum dists in
			let dist = if dist < 0 then int_max else dist in 
  		if (dist < h_value) then (dist, state) else (h_value, closest_state)   
  	) states (int_max, dummy_state)  	
	in
	(h_value, closest_state, hmap)
					
	
let h_time = ref 0.0 
let apply_time = ref 0.0	
let astar_search_nodefta final_asig spec nt_rule_list (states, transitions) =
	let new_modulus = !Options.modulus_astar in 
	let inputs_len = List.length spec in 
	let start_node = (states, transitions) in
	let ops = 
		list_fold (fun (nt, rule) ops ->
			match rule with 
			| FuncRewrite (op, _) -> BatSet.add op ops 
			| _ -> ops 
		) nt_rule_list BatSet.empty 
	in
	let hmap = ref BatMap.empty in 
	(* w (cost_so_far) *) 
	let w = ref BatMap.empty in (* node -> int *)
		let set_w n c = w := BatMap.add n c !w in 
	(* q *)
	let q = 
		Heap.Removable.create ~min_size:1024 
		~cmp:(fun (w1,(s1,_)) (w2,(s2,_)) ->
			if (w1 = w2) then (StateSet.cardinal s1) - (StateSet.cardinal s2)
			else w1 - w2 
		) () 
	in
	let token_map = ref BatMap.empty in  	
		let pick_from_q () = 
			let (weight, node) as elem = 
				match Heap.Removable.pop q with
				| Some (weight, node) -> (weight, node)
				| None -> failwith "No solution!"  
			in
			elem
		in
		let add_q ((weight, node) as elem) =
			begin 
				if (BatMap.mem elem !token_map) then 
					let token = BatMap.find elem !token_map in  	
					let token = Heap.Removable.update q token elem in 
					token_map := BatMap.add elem token !token_map
				else 
					let token = Heap.Removable.add_removable q elem in 
					token_map := BatMap.add elem token !token_map  
			end  
		in     
	(* initialization *)
	let _ = add_q (0, start_node) in
	let _ = set_w start_node 0 in
	while not (Heap.Removable.is_empty q) do	
		let (w_cur, ((states, transitions) as curr_node)) = pick_from_q () in
		let _ = prerr_endline (Printf.sprintf "# states: %d - cost : %d" (StateSet.cardinal states) w_cur) in
		(* let _ = prerr_endline (string_of_stateset states) in *)
		BatList.iter (fun (nt, rule) ->
			if (is_function_rule rule) then
			begin  
				let start = Sys.time() in  
  			let ((states', transitions') as next_node) = 
    			apply_prod_rule final_asig states transitions (nt, rule) spec
    		in
				let _ = apply_time := !apply_time +. (Sys.time() -. start) in  
				if not (StateSet.subset states' states) then
				begin  
					let start = Sys.time() in
					(* let _ = prerr_endline "computing h..." in   *)
  				let (h_next, closest_state, hmap') = 
						compute_h spec new_modulus !hmap inputs_len (states', transitions') final_asig ops 
					in
  				(* let _ = prerr_endline (Printf.sprintf "computing h: %d" h_next) in       *)
					(* let _ = prerr_endline ("closest: " ^ (string_of_state closest_state)) in *)
					let _ = h_time := !h_time +. (Sys.time() -. start) in
					hmap := hmap';  
					(* let new_cost = (StateSet.cardinal states') + h_next in *)
					let new_cost = w_cur + 1 + h_next in
					(* if (new_cost < !Options.max_size) then *)
					add_q (new_cost, next_node)
				end
			end 
		) nt_rule_list 
	done
		   

let compute_afta grammar spec =
	let nt_rule_list =
		BatMap.foldi (fun nt rules lst ->
			BatSet.fold (fun rule lst -> (nt, rule) :: lst) rules lst
		) grammar []
	in
	let final_asig  = BatList.map snd spec in
	let (states, final_states, transitions) = empty_afta in 
	let (states, state2expr) = apply_var_const_rule states nt_rule_list spec in
	let (states, final_states, transitions) =
		try
			(* let _ = astar_search_with_pv final_asig spec nt_rule_list states in *)
			(* let _ = astar_search final_asig spec nt_rule_list (states, transitions) in *)
			let _ = astar_search_nodefta final_asig spec nt_rule_list (states, transitions) in 
			(states, StateSet.empty, transitions)
		with SolutionFound(states, final_states, transitions) ->
			let _ = prerr_endline (Printf.sprintf "%.2f %.2f" !h_time !apply_time) in
			(states, final_states, transitions)
	in
	let afta = (states, final_states, transitions) in 
	(afta, state2expr) 


(* state -> expr *)
(* pv : node -> edge (preds, node) *)
let rec expr_from_state barc2op pv state2expr ((nt, _) as state) = 
	if (BatMap.mem state state2expr) then 
		BatMap.find state state2expr
	else 
		try
  		let (preds,_) as barc = BatMap.find state pv in 
  		let op = try BatMap.find barc barc2op with _ -> assert false in
  		let children_exprs = BatList.map (expr_from_state barc2op pv state2expr) preds in   
  	(*	Function (op, children_exprs, ret_type_of_op op) *)
		failwith "XXX"
		with _ ->
			failwith (string_of_state state)
																
let synthesis (macro_instantiator, target_function_name, grammar, forall_var_map, spec) =
	let _ = prerr_endline ("Constructing AFTA...") in 
	let start = Sys.time() in  
	let ((_, final_states, _) as afta), state2expr = compute_afta grammar spec in
	let _ = prerr_endline (Printf.sprintf "Constructing AFTA completed in %.2f sec" (Sys.time() -. start)) in  
	(* let _ = print_afta afta in *)
 	let _ = 
		if (StateSet.cardinal final_states) = 0 then failwith "No solution exists!"
		else if (StateSet.cardinal final_states) > 1 then failwith "something's wrong with the final states" 
	in 
	let _ = prerr_endline ("Constructing hyper graph...") in
	let start = Sys.time() in
	let (hgraph, barc2op, fs) = construct_hgraph afta state2expr in
	let _ = prerr_endline (Printf.sprintf "Constructing hyper graph completed in %.2f sec" (Sys.time() -. start)) in 
	let _ = prerr_endline ("Finding the minimum b-path...") in
	let start = Sys.time() in
	let pv : (state, edge) BatMap.t = compute_sbt final_states (hgraph, barc2op, fs) in
	let sol = expr_from_state barc2op pv state2expr (StateSet.choose final_states) in
	let _ = prerr_endline (Printf.sprintf "Finding the minimum b-path completed in %.2f sec" (Sys.time() -. start)) in
	let _ = BatList.iter (fun const -> prerr_endline (Exprs.string_of_const const)) (Exprs.compute_signature spec sol) in
	sol
	
