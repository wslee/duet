open Vocab
open Exprs
open BidirectionalUtils

let replace_theta = 3 

let get_longest_common_prefix str1 str2 = 
	let len = min (String.length str1) (String.length str2) in 
	BatList.fold_left (fun (diff, prefix) i ->
		let char1 = (String.get str1 i) in 
		let char2 = (String.get str2 i) in  
		if (not diff) && char1 = char2 then (diff, prefix ^ (BatString.of_char char1))
		else ((not diff), prefix)    
	) (false, "") (BatList.range 0 `To (len - 1)) |> snd 


let replace_cache = ref BatMap.empty

(* Minimum of three integers. This function is deliberately
 * not polymorphic because (1) we only need to compare integers 
 * and (2) the OCaml compilers do not perform type specialization 
 * for user-defined functions. *)
let minimum (x:int) y z =
  let m' (a:int) b = if a < b then a else b in
    m' (m' x y) z

(* Matrix initialization. *)
let init_matrix n m =
  let init_col = Array.init m in
  Array.init n (function
    | 0 -> init_col (function j -> j)
    | i -> init_col (function 0 -> i | _ -> 0)
  )

(* Computes the Levenshtein distance between two unistring.
 * If you want to run it faster, add the -unsafe option when
 * compiling or use Array.unsafe_* functions (but be carefull 
 * with these well-named unsafe features). *)
let align x y =
	let x = BatString.to_list x |> Array.of_list in 
	let y = BatString.to_list y |> Array.of_list in
  match Array.length x, Array.length y with
    | 0, n -> ([], [], n)
    | m, 0 -> ([], [], m)
    | m, n ->
       let matrix = init_matrix (m + 1) (n + 1) in
			 let ptr = init_matrix (m + 1) (n + 1) in
         for i = 1 to m do
           let s = matrix.(i) and t = matrix.(i - 1) in
             for j = 1 to n do
               let cost = abs (compare x.(i - 1) y.(j - 1)) in
							 let del = (t.(j) + 1) in 
							 let ins = (s.(j - 1) + 1) in 
							 let sub = (t.(j - 1) + cost(* * 2*)) in
							 let min_value = minimum del ins sub in 
							 let dir = 
								 if min_value = sub then 2 (*DIAG*) 
								 else if min_value = del then 1 (*DOWN*) 
								 else 0 (*LEFT*) 
							 in 
							 (s.(j) <- min_value);
							 ptr.(i).(j) <- dir 
             done
         done;
        let rec align_aux i j (x_lst, y_lst) =
					(* let _ = prerr_endline (Printf.sprintf "i: %d  j: %d" i j ) in            *)
					(* let _ = prerr_endline (Printf.sprintf "m[i][j] = %d" matrix.(i).(j) ) in *)
					(* let _ = prerr_endline (Printf.sprintf "ptr[i][j] = %d" ptr.(i).(j) ) in  *)
					let x_str = Some x.(i - 1) in
					let y_str = Some y.(j - 1) in
					if (i = 1) && (j = 1) then (x_str :: x_lst, y_str :: y_lst)
					else
						let dir =
							if (i < j) && (i = 1) then 0
							else if (i > j) && (j = 1) then 1 
							else ptr.(i).(j) 
						in 
						match dir with
						| 0 (*LEFT*) -> align_aux i (j - 1) (None :: x_lst, y_str :: y_lst)
						| 1 (*DOWN*) -> align_aux (i - 1) j (x_str :: x_lst, None :: y_lst)
						| 2 (*DIAG*) -> align_aux (i - 1) (j - 1) (x_str :: x_lst, y_str :: y_lst)
						| _ -> assert false   	 
				in
				(* prerr_endline (Printf.sprintf "edit distance: %d" matrix.(m).(n)); *)
				let aligned_src, aligned_dst = align_aux m n ([], []) in 
				(aligned_src, aligned_dst, matrix.(m).(n)) 	

(* This function takes two strings, align them, *)
(* and return a list of pairs (src_substr, dst_substr). *)
let get_replacement_pairs src_str dst_str =
	if (BatMap.mem (src_str, dst_str) !replace_cache) then 
		BatMap.find (src_str, dst_str) !replace_cache
	else 
		let result = 
  		let (aligned_src, aligned_dst, edit_distance) = align src_str dst_str in 
  		if (List.length aligned_src) * (List.length aligned_dst) = 0 
				 || (edit_distance > ((min (String.length src_str) (String.length dst_str)) / replace_theta))
			then []
    	else
    		let _ = assert ((List.length aligned_src) = (List.length aligned_dst)) in
    		(* if src_str = "aaa", dst_str = "bbb", diff_ranges = [] *)
    		(* i.e., if the entire string should be replaced, no pairs are returned. *)
    		let _, _(*diff_range*), diff_ranges = 
      		List.fold_left (fun (i, range, ranges) (src_char_opt, dst_char_opt) ->
      			if src_char_opt = dst_char_opt then (i + 1, [], ranges @ [range]) 
    				else (i + 1, range @ [i], ranges) 
      		) (0, [], []) (List.combine aligned_src aligned_dst)     	
    		in
    		let diff_ranges = List.filter (fun x -> (List.length x) > 0) (diff_ranges (*@ [diff_range]*)) in
    		let subst_pairs =  
      		List.map (fun range ->
      			let string_of_charoptlst x = 
          		List.fold_left (fun acc i -> 
          			match (List.nth x i) with 
          			| Some c -> acc ^ (String.make 1 c)
          			| None -> acc
          		) "" range
          	in 
      			let src_substr = string_of_charoptlst aligned_src in  
        		let dst_substr = string_of_charoptlst aligned_dst in
      			(src_substr, dst_substr)
      		) diff_ranges
    		in
    		let replaced = 
      		List.fold_left (fun acc (src_substr, dst_substr) ->
      			(Str.replace_first (Str.regexp_string src_substr) dst_substr acc)
      		) src_str subst_pairs
    		in 
    		if (BatString.equal replaced dst_str) then subst_pairs 
    		else [] 
		in
		let _ = replace_cache := BatMap.add (src_str, dst_str) result !replace_cache in 
		result   


(** STRING theory **)
let witness available_height nt_sigs (int_sigs, bv_sigs, string_sigs, bool_sigs) rule output_sig arg_sigs =
	let op = Grammar.op_of_rule rule in	
	if (String.compare op "str.len") = 0 then
		if (type_of_signature output_sig) <> Int then assert false
		else
			BatSet.filter (fun arg0_sig ->
				BatList.for_all (fun (arg0_const, output_const) ->
					((String.length (get_string arg0_const)) = (get_int output_const))
				) (BatList.combine arg0_sig output_sig)
			) nt_sigs
	else if (String.compare op "str.to.int") = 0 then
		if (type_of_signature output_sig) <> Int then assert false
		else
			(* BatSet.filter (fun arg0_sig ->                            *)
			(* 	BatList.for_all (fun (arg0_const, output_const) ->      *)
			(* 		let arg0_v = get_string arg0_const in                 *)
			(* 		let output_v = get_int output_const in                *)
			(* 		try (int_of_string arg0_v) = output_v with _ -> false *)
			(* 	) (BatList.combine arg0_sig output_sig)                 *)
			(* ) string_sigs                                             *)
			try
				BatSet.singleton
					(List.map (fun output_const -> CString (string_of_int (get_int output_const))) output_sig)
			with _ -> BatSet.empty
	else if (String.compare op "int.to.str") = 0 then
		if (type_of_signature output_sig) <> String then assert false
		else
			BatSet.filter (fun arg0_sig ->
				BatList.for_all (fun (arg0_const, output_const) ->
					let arg0_v = get_int arg0_const in
					let output_v = get_string output_const in
					try arg0_v = (int_of_string output_v) with _ -> false
				) (BatList.combine arg0_sig output_sig)
			) nt_sigs
			(* try                                                                                            *)
			(* 	BatSet.singleton                                                                             *)
			(* 		(List.map (fun output_const -> CInt (int_of_string (get_string output_const))) output_sig) *)
			(* with _ -> BatSet.empty                                                                         *)
	else if (String.compare op "str.at") = 0 then
		if (type_of_signature output_sig) <> String then assert false  
		(* if the output sring is not a character, no inputs *)
		else if not (BatList.for_all (fun const -> (String.length (get_string const)) = 1) output_sig) then BatSet.empty 
		else 
  		if (BatList.length arg_sigs) = 0 then
  			BatSet.filter (fun arg0_sig ->
  				BatList.for_all (fun (arg0_const, output_const) ->
  					let arg0_v = get_string arg0_const in 
  					let output_v = get_string output_const in
  					(BatString.exists arg0_v output_v) && 
						((String.length arg0_v) * (String.length output_v) > 0)   	 
  				) (BatList.combine arg0_sig output_sig)
  			) nt_sigs
  		else
				let arg0_sig = List.nth arg_sigs 0 in 
				BatList.fold_left (fun acc (arg0_const, output_const) ->
					let arg0_v = get_string arg0_const in 
					let output_v = get_string output_const in
					let index = try BatString.find arg0_v output_v with _ -> assert false in
					(* let _ =                                                                               *)
					(* 		prerr_endline (Printf.sprintf "str.at \"%s\" %d = \"%s\"" arg0_v index output_v)  *)
					(* in                                                                                    *)
					(* let indices =                                                  *)
  				(* 	BatString.fold_lefti (fun indices i c ->                     *)
  				(* 		if (String.compare (BatString.make 1 c) output_v) = 0 then *)
					(* 			(CInt i) :: indices                                      *)
  				(* 		else indices                                               *)
  				(* 	) [] arg0_v                                                  *)
					(* in                                                             *)
					(* acc @ [indices] *)
					acc @ [CInt index]
				) [] (BatList.combine arg0_sig output_sig)
				|> BatSet.singleton
				(* |> BatList.n_cartesian_product |> list2set *)
	else if (String.compare op "str.++") = 0 then
		if (type_of_signature output_sig) <> String then assert false
		else if (BatList.length arg_sigs) = 0 then
			BatSet.fold (fun arg0_sig acc ->
				let sg = 
  				BatList.fold_left (fun sg (arg0_const, output_const) ->
  					let arg0_v = get_string arg0_const in 
  					let output_v = get_string output_const in
						if (String.length arg0_v) * (String.length output_v) > 0 then
							let longest_prefix = get_longest_common_prefix arg0_v output_v in
							if (String.length longest_prefix) > 0 && 
							   (String.length output_v) > (String.length longest_prefix) then 
								sg @ [CString longest_prefix]
							else sg  
						else sg     	 
  				) [] (BatList.combine arg0_sig output_sig)
				in
				if (List.length sg) = (List.length output_sig) then BatSet.add sg acc
				else acc 
			) nt_sigs BatSet.empty 
			
			(* BatSet.filter (fun arg0_sig ->                                 *)
			(* 	BatList.for_all (fun (arg0_const, output_const) ->           *)
			(* 		let arg0_v = get_string arg0_const in                      *)
			(* 		let output_v = get_string output_const in                  *)
			(* 		(BatString.starts_with output_v arg0_v) &&                 *)
			(* 		(BatString.length arg0_v) < (BatString.length output_v) && *)
			(* 		(BatString.length arg0_v) > 0    	                        *)
			(* 	) (BatList.combine arg0_sig output_sig)                      *)
			(* ) string_sigs                                                  *)
		else
			let arg0_sig = List.nth arg_sigs 0 in
			let arg1_sig = 
  			BatList.fold_left (fun acc (arg0_const, output_const) ->
  				let arg0_v = get_string arg0_const in
  				let output_v = get_string output_const in
					let arg0_v_len = (BatString.length arg0_v) in  
					let output_v_len = (BatString.length output_v) in 
  				if (BatString.starts_with output_v arg0_v) && output_v_len > arg0_v_len then
							acc @ [CString (BatString.sub output_v arg0_v_len (output_v_len - arg0_v_len))]  
					else acc  
  			) [] (BatList.combine arg0_sig output_sig)
			in
			if (List.length arg1_sig) = (List.length output_sig) then 
				BatSet.singleton arg1_sig 
			else BatSet.empty 
	else if (String.compare op "str.contains") = 0 ||
					(String.compare op "str.prefixof") = 0 || 
					(String.compare op "str.suffixof") = 0 
				then
		let _ = assert ((type_of_signature output_sig) = Bool) in 
		if (BatList.length arg_sigs) = 0 then nt_sigs
		else
			let arg0_sig = List.nth arg_sigs 0 in
			let arg1_sig =
				BatSet.filter (fun arg1_sig ->
					let sg = (fun_apply_signature op [arg0_sig; arg1_sig]) in
					List.for_all2 (fun const output_const ->
						(is_abstract_bool output_const) || (* for learn_ite *)
						(Pervasives.compare const output_const) = 0
					) sg output_sig
				) nt_sigs 
			in
			arg1_sig
	else if (String.compare op "str.indexof") = 0 then
		(* str.indexof s t i : location of t in s after i *)
		if (type_of_signature output_sig) <> Int then assert false
		(* if output = -1, skip *)
		else if (BatList.for_all (fun const -> (get_int const) = -1) output_sig) then 
			BatSet.empty
		else if (BatList.length arg_sigs) = 0 then
			BatSet.filter (fun sg -> 
				(* length of s should be > output *)
				(* str.indexof "abcd" "bc" 0 = 1 *) 
				(BatList.for_all (fun (const, output_const) ->
					let output_v = get_int output_const in 
					let str = get_string const in  
					(String.length str) > output_v 
				) (BatList.combine sg output_sig))		
			) nt_sigs 
		else if (BatList.length arg_sigs) = 1 then
			(* s should contain t *)
			let arg0_sig = List.nth arg_sigs 0 in
			let arg1_sig =
				BatSet.filter (fun arg1_sig ->
					BatList.for_all (fun ((arg0_const, arg1_const), output_const) ->
						let arg0_v = get_string arg0_const in 
						let arg1_v = get_string arg1_const in
						let output_v = get_int output_const in 
						try (String.length arg1_v) > 0 && (BatString.find arg0_v arg1_v) = output_v with _ -> false     
					) (BatList.combine (BatList.combine arg0_sig arg1_sig) output_sig)   
				) nt_sigs 
			in
			arg1_sig	
		else 	
			(* str.indexof s t i = output *)
			let arg0_sig = List.nth arg_sigs 0 in
			let arg1_sig = List.nth arg_sigs 1 in
			BatSet.filter (fun arg2_sig ->
				BatList.for_all (fun ((arg0_const, arg1_const), (arg2_const, output_const)) ->
					let arg0_v = get_string arg0_const in 
					let arg1_v = get_string arg1_const in
					let arg2_v = get_int arg2_const in
					let output_v = get_int output_const in 
					try 
						(BatString.find_from arg0_v arg2_v arg1_v) = output_v
					with _ -> false 
				) (BatList.combine (BatList.combine arg0_sig arg1_sig) (BatList.combine arg2_sig output_sig))   
			) nt_sigs 
				
			(* BatList.fold_left (fun acc ((arg0_const, arg1_const), output_const) ->                            *)
			(* 	let arg0_v = get_string arg0_const in                                                           *)
			(* 	let arg1_v = get_string arg1_const in                                                           *)
			(* 	let output_v = get_int output_const in                                                          *)
			(* 	let indices =                                                                                   *)
			(* 		BatList.fold_left (fun acc index ->                                                           *)
			(* 			try                                                                                         *)
			(* 				(* let _ = prerr_endline (Printf.sprintf "find %s %d %s" arg0_v index arg1_v) in  *)      *)
  		(* 				if (BatList.length acc) = 0 && (BatString.find_from arg0_v index arg1_v) = output_v then  *)
  		(* 					(CInt index) :: acc                                                                     *)
  		(* 				else acc                                                                                  *)
			(* 			with _ -> acc    	                                                                         *)
			(* 		) [] (BatList.range 0 `To ((String.length arg0_v) - (String.length arg1_v)))                  *)
			(* 	in                                                                                              *)
			(* 	acc @ [indices]                                                                                 *)
			(* ) [] (BatList.combine (BatList.combine arg0_sig arg1_sig) output_sig)                             *)
			(* |> BatList.n_cartesian_product |> list2set                                                        *)
	else if (String.compare op "str.replace") = 0 then
		(* str.replace s t1 t2 = s' *)
		if (type_of_signature output_sig) <> String then assert false
		else if (BatList.length arg_sigs) = 0 then
			BatSet.fold (fun sg acc ->
				try 
  				let sg' = 
  					List.map (fun (const, output_const) ->
  						let output_v = get_string output_const in 
  						let str = get_string const in 
  						let subst_pairs = get_replacement_pairs str output_v in 
  						if (List.length subst_pairs) = 0 then failwith "replace_0"
  						else 	     
								let subst_pairs_wo_last = 
									BatList.take ((List.length subst_pairs) - 1) subst_pairs 
								in
								let replaced =  
    							List.fold_left (fun acc (src_substr, dst_substr) ->
              			(Str.replace_first (Str.regexp_string src_substr) dst_substr acc)
              		) str subst_pairs_wo_last 
  						 	in 
								CString replaced
  					) (List.combine sg output_sig) 
  				in
  				BatSet.add sg' acc
				with Failure _ -> acc 
			) nt_sigs BatSet.empty 
			
			(* BatSet.filter (fun sg ->                                              *)
			(* 	(BatList.for_all (fun (const, output_const) ->                      *)
			(* 		let output_v = get_string output_const in                         *)
			(* 		let str = get_string const in                                     *)
			(* 		if (String.compare str output_v) = 0 ||                           *)
			(* 			 (String.length output_v) * (String.length str) = 0 then false  *)
			(* 		else                                                              *)
			(* 			(* true *)                                                      *)
  		(* 			List.length (get_replacement_pairs str output_v) > 0            *)
			(* 	) (BatList.combine sg output_sig)                                   *)
			(* 	)                                                                   *)
			(* ) string_sigs                                                         *)
		else if (BatList.length arg_sigs) = 1 then
			let arg0_sig = List.nth arg_sigs 0 in
			let arg1_sig =
				(List.fold_left (fun acc (arg0_const, output_const) ->
					let subst_pairs = 
						get_replacement_pairs (get_string arg0_const) (get_string output_const) 
					in 
					let _ = assert ((List.length subst_pairs) = 1) in
					let (src_substr, dst_substr) = BatList.hd subst_pairs in 
					acc @ [CString src_substr] 
				) [] (BatList.combine arg0_sig output_sig)
				) 
				|> BatSet.singleton   
				
				(* BatList.fold_left (fun acc (arg0_const, output_const) ->          *)
				(* 	let arg0_v = get_string arg0_const in                           *)
				(* 	let output_v = get_string output_const in                       *)
				(* 	let pairs = get_replacement_pairs arg0_v output_v in            *)
				(* 	acc @ [(List.map (fun (from_str,_) -> CString from_str) pairs)] *)
				(* ) [] (BatList.combine arg0_sig output_sig)                        *)
				(* |> BatList.n_cartesian_product |> list2set                        *)
				
				 
				(* BatSet.filter (fun arg1_sig ->                             *)
				(* 	BatList.for_all (fun (arg0_const, arg1_const) ->         *)
				(* 		let arg0_v = get_string arg0_const in                  *)
				(* 		let arg1_v = get_string arg1_const in                  *)
				(* 		(BatString.exists arg0_v arg1_v) &&                    *)
				(* 		(String.length arg0_v) * (String.length arg1_v) > 0 && *)
				(* 		(String.compare arg0_v arg1_v) <> 0                    *)
				(* 	) (BatList.combine arg0_sig arg1_sig)                    *)
				(* ) string_sigs                                              *)
			in
			arg1_sig		
		else 
			let arg0_sig = List.nth arg_sigs 0 in
			let arg1_sig = List.nth arg_sigs 1 in
			let arg2_sig =
				List.fold_left (fun acc ((arg0_const, arg1_const), output_const) ->
					let subst_pairs = 
						get_replacement_pairs (get_string arg0_const) (get_string output_const) 
					in 
					let _ = assert ((List.length subst_pairs) = 1) in
					let (src_substr, dst_substr) = BatList.hd subst_pairs in
					let _ = assert (BatString.equal (get_string arg1_const) src_substr) in  
					acc @ [CString dst_substr] 
				) [] 
				(BatList.combine (BatList.combine arg0_sig arg1_sig) output_sig) 
				|> BatSet.singleton   
				
				(* try                                                                                    *)
				(* BatList.fold_left (fun acc ((arg0_const, arg1_const), output_const) ->                 *)
				(* 	let arg0_v = get_string arg0_const in                                                *)
				(* 	let arg1_v = get_string arg1_const in                                                *)
				(* 	let output_v = get_string output_const in                                            *)
				(* 	(* let pairs = get_replacement_pairs arg0_v output_v in *)                           *)
					 
  			(* 		let to_str =                                                                       *)
				(* 			get_replacement arg0_v arg1_v output_v                                           *)
  			(* 			(* (List.find (fun (from_str, _) -> (BatString.equal from_str arg1_v)) pairs) *) *)
  			(* 			(* |> snd                                                                     *) *)
  			(* 		in                                                                                 *)
  			(* 		acc @ [CString to_str]                                                             *)
					
				(* ) [] (BatList.combine (BatList.combine arg0_sig arg1_sig) output_sig)                  *)
				(* |> BatSet.singleton                                                                    *)
				(* with Not_found -> BatSet.empty                                                         *)
				 
				
				(* BatSet.filter (fun arg2_sig ->                                                 *)
				(* 	BatList.for_all2 (fun ((arg0_const, arg1_const), arg2_const) output_const -> *)
				(* 		let arg0_v = get_string arg0_const in                                      *)
				(* 		let arg1_v = get_string arg1_const in                                      *)
				(* 		let arg2_v = get_string arg2_const in                                      *)
				(* 		let output_v = get_string output_const in                                  *)
				(* 		(String.compare output_v                                                   *)
				(* 			(snd(BatString.replace ~str:arg0_v ~sub:arg1_v ~by:arg2_v))              *)
				(* 		) = 0                                                                      *)
				(* 	) (BatList.combine (BatList.combine arg0_sig arg1_sig) arg2_sig) output_sig  *)
				(* ) string_sigs                                                                  *)
			in
			arg2_sig
	else if (String.compare op "str.substr") = 0 then
		if (type_of_signature output_sig) <> String then assert false
		else if (BatList.length arg_sigs) = 0 then
			BatSet.filter (fun sg -> 
				(BatList.for_all (fun (const, output_const) ->
					let output_v = get_string output_const in 
					let str = get_string const in  
					(BatString.exists str output_v)  
				) (BatList.combine sg output_sig))		
			) nt_sigs 
		else if (BatList.length arg_sigs) = 1 then
			let arg0_sig = List.nth arg_sigs 0 in
			let arg1_sig = 
  			BatList.fold_left (fun acc (arg0_const, output_const) ->
  				try 
  				let arg0_v = get_string arg0_const in 
  				let output_v = get_string output_const in
  				let start_index = BatString.find arg0_v output_v in   
  					(* BatString.find_all arg0_v output_v |> BatList.of_enum *)
  				acc @ [CInt start_index]
					with _ -> acc 
  				(* acc @ [BatList.map (fun x -> CInt x) start_indices]  *)
  			) [] (BatList.combine arg0_sig output_sig) 
			in 
			if (List.length arg1_sig) = (List.length output_sig) then 
				BatSet.singleton arg1_sig
			else BatSet.empty  
			(* |> BatList.n_cartesian_product |> list2set		 *)
		else
			let arg0_sig = List.nth arg_sigs 0 in
			let arg1_sig = List.nth arg_sigs 1 in
			(* all integers >= output_v_len *)
			BatSet.filter (fun arg2_sig -> 
				(BatList.for_all2 (fun (arg0_const, arg1_const) (arg2_const, output_const) ->
					let arg0_v = get_string arg0_const in
					let arg1_v = get_int arg1_const in
					let arg2_v = get_int arg2_const in
					let arg2_v = min ((String.length arg0_v) - arg1_v) arg2_v in
					let output_v = get_string output_const in
					try 
						BatString.equal (BatString.sub arg0_v arg1_v arg2_v) output_v
					with _ -> false 	  
				) (BatList.combine arg0_sig arg1_sig) (BatList.combine arg2_sig output_sig))		
			) nt_sigs
			|> BatSet.add   
			(* output_v_len *)
			(BatList.map (fun output_const ->
				let output_v = get_string output_const in
				CInt (String.length output_v)
			) output_sig) 
	else 
		failwith (Printf.sprintf "unsupported op: %s" op)