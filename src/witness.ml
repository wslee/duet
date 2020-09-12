open Vocab
open Exprs
open BidirectionalUtils

exception WitnessFailure

type bvop = BVSHL | BVSHR | BVASHR
let bvshift_cache : ((Int64.t * Int64.t * bvop), Int64.t) BatMap.t ref = ref BatMap.empty 

let check_ratio v1 v2 = 
	(* |v1| / |v2| < \theta *) 
	(Int64.to_float (Int64.abs v1)) /. (Int64.to_float (Int64.abs v2)) < !Options.theta

let bv_distance bv1 bv2 = 
	match (bv1, bv2) with 
	| CBV v1, CBV v2 -> 
		Int64.abs (Int64.sub (Int64.abs v1) (Int64.abs v2))
	| _ -> assert false

let check_dist_time = ref 0. 
(* true if dist(sig1, sigs) < dist(sig2, sigs) *)
let check_distance sig1 sig2 sigs =
	(* if true then true else *)
	let start = Sys.time() in 
	let get_sig_dist sg =
		BatSet.fold (fun comp_sg sig_dist ->
			let sig_dist' = 
				List.map2 bv_distance sg comp_sg
			in 
			if (List.for_all2 (fun x y -> (Int64.compare x y) < 0) sig_dist' sig_dist) then 
				sig_dist'
			else sig_dist
		) sigs (BatList.make (List.length sg) Int64.max_int) 
	in  
	let sig1_dist = get_sig_dist sig1 in 
	let sig2_dist = get_sig_dist sig2 in
	let _ = check_dist_time := !check_dist_time +. (Sys.time() -. start) in  
	List.for_all2 (fun x y -> (Int64.compare x y) < 0) sig1_dist sig2_dist   
	  
		
let check_bv_range sigs_lst = 
	BatList.for_all (fun sg ->
		if (type_of_signature sg) <> BV then true 
		else 
  		BatList.for_all (fun const ->
  			let bv = get_bv const in 
  			(Int64.compare bv Int64.max_int) < 0 &&
  			(Int64.compare Int64.min_int bv) < 0 
  		) sg 	
	) sigs_lst  
	 
let int64_to_string_in_binary bv =
	let bv_bigint = 
		if (Int64.compare bv Int64.zero) < 0 then 
			BatBig_int.add (BatBig_int.shift_left_big_int (BatBig_int.one) 63) (BatBig_int.big_int_of_int64 bv)	
		else (BatBig_int.big_int_of_int64 bv)
	in  
	let str = BatBig_int.to_string_in_binary bv_bigint in 
	try 
		(BatString.make (63 - (String.length str)) '0') ^ str
	with _ -> failwith (Printf.sprintf "%s %s" (Int64.to_string bv) str )  	 
	
let bitcount int64 =
	0
	(* let str = (int64_to_string_in_binary int64) in *)
	(* BatString.count_string str "1"                 *)
	 	

let get_longest_common_prefix str1 str2 = 
	let len = min (String.length str1) (String.length str2) in 
	BatList.fold_left (fun (diff, prefix) i ->
		let char1 = (String.get str1 i) in 
		let char2 = (String.get str2 i) in  
		if (not diff) && char1 = char2 then (diff, prefix ^ (BatString.of_char char1))
		else ((not diff), prefix)    
	) (false, "") (BatList.range 0 `To (len - 1)) |> snd 


let get_all_substrings str =
  let len = String.length str in 
  List.fold_left (fun acc i -> 
  	List.fold_left (fun acc sub_len -> 
  		BatSet.add (BatString.sub str i sub_len) acc 
  	) acc (BatList.range 0 `To (len - i))
  ) BatSet.empty (BatList.range 0 `To (len - 1))

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
				 || (edit_distance > ((min (String.length src_str) (String.length dst_str)) / 3))
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

(* let get_replacement orig_str orig_substr dest_str =                                              *)
(* 	if (BatMap.mem (orig_str, orig_substr, dest_str) !replace_cache) then                          *)
(* 		BatMap.find (orig_str, orig_substr, dest_str) !replace_cache                                 *)
(* 	else                                                                                           *)
(* 	let dest_substrs = get_all_substrings dest_str in                                              *)
(* 	let result =                                                                                   *)
(*   	BatSet.filter (fun dest_substr ->                                                            *)
(*   		let replaced =                                                                             *)
(*   			Str.replace_first (Str.regexp_string orig_substr) dest_substr orig_str                   *)
(*   		in                                                                                         *)
(*   		(BatString.equal replaced dest_str)	                                                      *)
(*   	) dest_substrs |> BatSet.choose                                                              *)
(* 	in                                                                                             *)
(* 	let _ = replace_cache := BatMap.add (orig_str, orig_substr, dest_str) result !replace_cache in *)
(* 	result                                                                                         *)
	
(* let get_replacement_pairs orig_str dest_str =                                                    *)
(* 	(* if (BatMap.mem (orig_str, dest_str) !replace_cache) then *)                                 *)
(* 	(* 	BatMap.find (orig_str, dest_str) !replace_cache        *)                                 *)
(* 	(* else                                                     *)                                 *)
(*   	let orig_substrs = get_all_substrings orig_str in                                            *)
(*   	let dest_substrs = get_all_substrings dest_str in                                            *)
(*   	let result =                                                                                 *)
(*     	BatSet.fold (fun orig_substr acc ->                                                        *)
(*     		BatSet.fold (fun dest_substr acc ->                                                      *)
(*   				let replaced =                                                                         *)
(*   					Str.replace_first (Str.regexp_string orig_substr) dest_substr orig_str               *)
(*   				in                                                                                     *)
(*   				if (BatString.equal replaced dest_str) &&                                              *)
(*   				   (not (BatString.equal orig_substr orig_str)) then                                   *)
(*   					BatSet.add (orig_substr, dest_substr) acc                                            *)
(*   				else acc                                                                               *)
(*     		) dest_substrs acc                                                                       *)
(*     	) orig_substrs BatSet.empty                                                                *)
(* 			|> BatSet.elements                                                                         *)
(* 			|> List.sort (fun (f,t) (f',t') ->                                                         *)
(* 				((String.length f) + (String.length t)) - ((String.length f') + (String.length t'))      *)
(* 				)                                                                                        *)
(* 			|> (fun x -> try [List.hd x] with _ -> x)                                                  *)
(*   	in                                                                                           *)
(*   	(* let _ = replace_cache := BatMap.add (orig_str, dest_str) result !replace_cache in *)      *)
(* 		result                                                                                       *)
	
	
	(* let _ = assert ((String.compare orig_str dest_str) <> 0) in                                                              *)
	(* let orig_len = String.length orig_str in                                                                                 *)
	(* let dest_len = String.length dest_str in                                                                                 *)
	(* let _ = assert ((orig_len * dest_len) > 0) in                                                                            *)
	(* let get_longest_prefix s1 s2 =                                                                                           *)
	(* 	let s1_len = (String.length s1) in                                                                                     *)
	(* 	BatList.fold_left (fun acc i ->                                                                                        *)
	(* 		let s1_prefix = BatString.slice ~first:0 ~last:i s1 in                                                               *)
	(* 		if (BatString.starts_with s2 s1_prefix) then s1_prefix                                                               *)
	(* 		else acc                                                                                                             *)
	(* 	) "" (BatList.range 1 `To s1_len)                                                                                      *)
	(* in                                                                                                                       *)
	(* let get_longest_suffix s1 s2 =                                                                                           *)
	(* 	let s1_len = (String.length s1) in                                                                                     *)
	(* 	BatList.fold_left (fun acc i ->                                                                                        *)
	(* 		let s1_suffix = BatString.slice ~first:i s1 in                                                                       *)
	(* 		if (BatString.ends_with s2 s1_suffix) then s1_suffix                                                                 *)
	(* 		else acc                                                                                                             *)
	(* 	) "" (BatList.range (s1_len - 1) `Downto 0)                                                                            *)
	(* in                                                                                                                       *)
	(* let prefix = get_longest_prefix orig_str dest_str in                                                                     *)
	(* let suffix = get_longest_suffix orig_str dest_str in                                                                     *)
	(* (* "Soybean Farming" *)                                                                                                  *)
	(* (* "SoybeanSoybean Farming" *)                                                                                           *)
	(* (* "" -> "Soybean" *)                                                                                                    *)
	(* (* I hate bananasI love apples *)                                                                                        *)
	(* (* I hate bananas *)                                                                                                     *)
	(* (* love *)                                                                                                               *)
	(* (* lov  *)                                                                                                               *)
	(* (* prefix: lov *)                                                                                                        *)
	(* (* suffix: *)                                                                                                            *)
	(* (* from_idx_orig = 3 *)                                                                                                  *)
	(* (* to_idx_orig = 4 *)                                                                                                    *)
	(* (* from_idx_dest = 3 *)                                                                                                  *)
	(* (* to_idx_dest   = 3 *)                                                                                                  *)
	(* let from_idx_orig = (String.length prefix) in                                                                            *)
	(* let to_idx_orig = orig_len - (String.length suffix) in                                                                   *)
	(* let from_idx_dest = (String.length prefix) in                                                                            *)
	(* let to_idx_dest = dest_len - (String.length suffix) in                                                                   *)
	(* let from_str = BatString.slice ~first:from_idx_orig ~last:to_idx_orig orig_str in                                        *)
	(* let to_str = BatString.slice ~first:from_idx_dest ~last:to_idx_dest dest_str in                                          *)
	(* if (from_idx_orig >= to_idx_orig)                                                                                        *)
	(*   (* || (from_idx_dest >= to_idx_dest)      *)                                                                           *)
	(*   (* || (BatString.exists from_str prefix)  *)                                                                           *)
	(* 	|| (BatString.exists prefix from_str)                                                                                  *)
	(* then (orig_str, dest_str)                                                                                                *)
	(* else                                                                                                                     *)
	(* (* if from_str = "", it is equal to string concatenation. so no need to do str.replace *)                                *)
	(* (* if (String.length from_str) = 0 || (BatString.exists prefix from_str)  *)                                             *)
	(* (* then (orig_str, dest_str)                                              *)                                             *)
	(* (* else                                                                   *)                                             *)
	(* begin                                                                                                                    *)
  (* 	prerr_endline (                                                                                                        *)
  (* 		Printf.sprintf "%d %d %d %d"                                                                                         *)
  (* 										from_idx_orig to_idx_orig from_idx_dest to_idx_dest                                                  *)
  (* 	);                                                                                                                     *)
  (* 	prerr_endline (                                                                                                        *)
  (* 		Printf.sprintf "\"%s\" ==> \"%s\" pre:\"%s\" suf:\"%s\" (\"%s\" -> \"%s\")"                                          *)
  (* 										orig_str dest_str prefix suffix from_str to_str                                                      *)
  (* 	);                                                                                                                     *)
  (* 	let _ =                                                                                                                *)
  (* 		if not (BatString.equal (Str.replace_first (Str.regexp_string from_str) to_str orig_str) dest_str) then              *)
  (* 			let _ = prerr_endline (Printf.sprintf "\"%s\" -> \"%s\" : \"%s\" -> \"%s\"" orig_str dest_str from_str to_str) in  *)
  (* 			assert false                                                                                                       *)
  (* 	in                                                                                                                     *)
  (* 	(from_str, to_str)                                                                                                     *)
	(* end                                                                                                                      *)
	
let get_ret_type_sig (int_sigs, bv_sigs, string_sigs, bool_sigs) rule = 
	let nts = Grammar.get_nts rule in
	let nt_ty = Grammar.type_of_nt (BatList.nth nts 1) in
	(match nt_ty with 
	| Int -> int_sigs
	| BV -> bv_sigs
	| String -> string_sigs
	| Bool -> bool_sigs)
		 
(* nt 에 대한 값 유추 *)
(* signature set -> string -> 
   signature (output) -> signature list (prev args) -> signature set (possible curr args) *)
(* 원칙: unconstrained arg 만 total_sigs 로 부터. *)
let witness nt_sigs (int_sigs, bv_sigs, string_sigs, bool_sigs) rule output_sig arg_sigs =
	let op = Grammar.op_of_rule rule in  
	(** Theory agnostic *)
	if (String.compare op "=") = 0 then
		if (type_of_signature output_sig) <> Bool then assert false
		else
		if (BatList.length arg_sigs) = 0 then nt_sigs
		else 
			let arg0_sig = List.nth arg_sigs 0 in
			BatSet.filter (fun arg1_sig ->
				BatList.for_all2 (fun (arg0_const, arg1_const) output_const ->
					(is_abstract_bool output_const) || (* for learn_ite *)
					(let output_v = get_concrete_bool output_const in
					 ((Pervasives.compare arg0_const arg1_const) = 0) = output_v)
				) (BatList.combine arg0_sig arg1_sig) output_sig 
			) nt_sigs
	else if (String.compare op "<") = 0 then
		if (type_of_signature output_sig) <> Bool then assert false
		else
		if (BatList.length arg_sigs) = 0 then nt_sigs
		else 
			let arg0_sig = List.nth arg_sigs 0 in
			BatSet.filter (fun arg1_sig ->
				BatList.for_all2 (fun (arg0_const, arg1_const) output_const ->
					(is_abstract_bool output_const) || (* for learn_ite *)
					(let output_v = get_concrete_bool output_const in
					 ((Pervasives.compare arg0_const arg1_const) < 0) = output_v)   
				) (BatList.combine arg0_sig arg1_sig) output_sig 
			) nt_sigs		
	else if (String.compare op ">") = 0 then
		if (type_of_signature output_sig) <> Bool then assert false
		else
		if (BatList.length arg_sigs) = 0 then nt_sigs
		else 
			let arg0_sig = List.nth arg_sigs 0 in
			BatSet.filter (fun arg1_sig ->
				BatList.for_all2 (fun (arg0_const, arg1_const) output_const ->
					(is_abstract_bool output_const) || (* for learn_ite *)
					(let output_v = get_concrete_bool output_const in
					 ((Pervasives.compare arg0_const arg1_const) > 0) = output_v)   
				) (BatList.combine arg0_sig arg1_sig) output_sig 
			) nt_sigs
	else if (String.compare op "<=") = 0 then
		if (type_of_signature output_sig) <> Bool then assert false
		else
		if (BatList.length arg_sigs) = 0 then nt_sigs
		else 
			let arg0_sig = List.nth arg_sigs 0 in
			BatSet.filter (fun arg1_sig ->
				BatList.for_all2 (fun (arg0_const, arg1_const) output_const ->
					(is_abstract_bool output_const) || (* for learn_ite *)
					(let output_v = get_concrete_bool output_const in
					 ((Pervasives.compare arg0_const arg1_const) <= 0) = output_v)   
				) (BatList.combine arg0_sig arg1_sig) output_sig 
			) nt_sigs
	else if (String.compare op "ite") = 0 then
		(* should have been handled by learn_ite *) 
		assert false 
	(** Propositional theory *)
	else if (String.compare op "and") = 0 then
		if (type_of_signature output_sig) <> Bool then assert false
		else
		if (BatList.length arg_sigs) = 0 then
			BatSet.filter (fun arg0_sig ->
				BatList.for_all (fun (arg0_const, output_const) ->
					(is_abstract_bool output_const) || 
					(let arg0_v = get_concrete_bool arg0_const in
					 let output_v = get_concrete_bool output_const in
					 ((not (output_v = true)) || (arg0_v = true)))
				) (BatList.combine arg0_sig output_sig)
			) nt_sigs
		else
			let arg0_sig = List.nth arg_sigs 0 in
			BatSet.filter (fun arg1_sig ->
				BatList.for_all2 (fun (arg0_const, arg1_const) output_const ->
					(is_abstract_bool output_const) ||
					(let arg0_v = get_concrete_bool arg0_const in
					 let arg1_v = get_concrete_bool arg1_const in
					 let output_v = get_concrete_bool output_const in
					 (arg0_v && arg1_v) = output_v)
				) (BatList.combine arg0_sig arg1_sig) output_sig
			) nt_sigs
	else if (String.compare op "or") = 0 then
		if (type_of_signature output_sig) <> Bool then assert false
		else
		if (BatList.length arg_sigs) = 0 then
			BatSet.filter (fun arg0_sig ->
				BatList.for_all (fun (arg0_const, output_const) ->
					(is_abstract_bool output_const) ||
					(let arg0_v = get_concrete_bool arg0_const in
					 let output_v = get_concrete_bool output_const in
					 ((not (output_v = false)) || (arg0_v = false)))
				) (BatList.combine arg0_sig output_sig)
			) nt_sigs
		else
			let arg0_sig = List.nth arg_sigs 0 in
			BatSet.filter (fun arg1_sig ->
				BatList.for_all2 (fun (arg0_const, arg1_const) output_const ->
					(is_abstract_bool output_const) ||
					(let arg0_v = get_concrete_bool arg0_const in
					 let arg1_v = get_concrete_bool arg1_const in
					 let output_v = get_concrete_bool output_const in
					 (arg0_v || arg1_v) = output_v)
				) (BatList.combine arg0_sig arg1_sig) output_sig
			) nt_sigs
	else if (String.compare op "xor") = 0 then
		if (type_of_signature output_sig) <> Bool then assert false
		else
		if (BatList.length arg_sigs) = 0 then 
			BatSet.filter (fun arg0_sig ->
				let arg1_sig = fun_apply_signature "xor" [arg0_sig; output_sig] in 
				BatSet.mem arg1_sig bool_sigs
			) nt_sigs
		else
			let arg0_sig = List.nth arg_sigs 0 in
			BatSet.filter (fun arg1_sig ->
				BatList.for_all2 (fun (arg0_const, arg1_const) output_const ->
					(is_abstract_bool output_const) || 
					(let arg0_v = get_concrete_bool arg0_const in
					 let arg1_v = get_concrete_bool arg1_const in
					 let output_v = get_concrete_bool output_const in
					 (arg0_v <> arg1_v) = output_v)
				) (BatList.combine arg0_sig arg1_sig) output_sig
			) nt_sigs
			(* let arg0_sig = List.nth arg_sigs 0 in *)
			(* BatList.fold_left (fun acc (arg0_const, output_const) ->       *)
			(* 	let arg0_v = get_bool arg0_const in                          *)
			(* 	let output_v = get_bool output_const in                      *)
			(* 	acc @ [CBool (arg0_v <> output_v)]                           *)
			(* ) [] (BatList.combine arg0_sig output_sig) |> BatSet.singleton *)
	else if (String.compare op "not") = 0 then
		if (type_of_signature output_sig) <> Bool then assert false
		else
			BatSet.filter (fun arg0_sig ->
				BatList.for_all (fun (arg0_const, output_const) ->
					(is_abstract_bool output_const) ||  
					(let arg0_v = get_concrete_bool arg0_const in
					 let output_v = get_concrete_bool output_const in
					 (not arg0_v) = output_v)
				) (BatList.combine arg0_sig output_sig)
			) nt_sigs
			(* BatList.fold_left (fun acc output_const -> *)
			(* 	let output_v = get_bool output_const in  *)
			(* 	acc @ [(CBool (not output_v))]           *)
			(* ) [] output_sig |> BatSet.singleton        *)
	(** STRING theory **)
	else if (String.compare op "str.len") = 0 then
		if (type_of_signature output_sig) <> Int then assert false
		else
			BatSet.filter (fun arg0_sig ->
				BatList.for_all (fun (arg0_const, output_const) ->
					((String.length (get_string arg0_const)) = (get_int output_const))
				) (BatList.combine arg0_sig output_sig)
			) string_sigs
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
			) int_sigs
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
  			) string_sigs
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
			) string_sigs BatSet.empty 
			
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
		(* if (type_of_signature output_sig) <> Bool then assert false *)
		(* else                                                        *)
		if (BatList.length arg_sigs) = 0 then string_sigs
		else
			let arg0_sig = List.nth arg_sigs 0 in
			let arg1_sig =
				BatSet.filter (fun arg1_sig ->
					let sg = (fun_apply_signature op [arg0_sig; arg1_sig]) in
					List.for_all2 (fun const output_const ->
						(is_abstract_bool output_const) || (* for learn_ite *)
						(Pervasives.compare const output_const) = 0
					) sg output_sig
				) string_sigs 
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
			) string_sigs 
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
				) string_sigs 
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
			) int_sigs 
				
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
			) string_sigs BatSet.empty 
			
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
			) string_sigs 
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
			) int_sigs
			|> BatSet.add   
			(* output_v_len *)
			(BatList.map (fun output_const ->
				let output_v = get_string output_const in
				CInt (String.length output_v)
			) output_sig) 
			
	(** BV theory **)  
	(* else if (not (check_bv_range (output_sig::arg_sigs))) then BatSet.empty  *)
	else if (String.compare op "bvadd") = 0 then
		if (type_of_signature output_sig) <> BV then assert false
		else if (BatList.length arg_sigs) = 0 then
			BatSet.filter (fun arg0_sig ->
				let arg1_sig = fun_apply_signature "bvsub" [output_sig; arg0_sig] in
				BatSet.mem arg1_sig bv_sigs
			) bv_sigs
			(* BatSet.filter (fun arg0_sig ->                                  *)
			(* 	BatList.for_all (fun (arg0_const, output_const) ->            *)
			(* 		let arg0_v = get_bv arg0_const in                           *)
			(* 		let output_v = get_bv output_const in                       *)
			(* 		let arg1_v = (Int64.sub output_v arg0_v) in                 *)
			(* 		(* to prevent from generating the same sub problem *)       *)
			(* 		(Int64.compare (Int64.abs arg1_v) (Int64.abs output_v)) < 0 *)
			(* 		(* (not (Int64.equal output_v Int64.zero)) *)               *)
			(* 	) (BatList.combine arg0_sig output_sig)                       *)
			(* )                                                               *)
			(* bv_sigs                                                         *)
		else
			let arg0_sig = List.nth arg_sigs 0 in
			let arg1_sig =
  			BatSet.filter (fun arg1_sig ->
  				BatList.for_all2 (fun (arg0_const, arg1_const) output_const ->
  					let arg0_v = get_bv arg0_const in
  					let arg1_v = get_bv arg1_const in
  					let output_v = get_bv output_const in
  					(Int64.equal (Int64.add arg0_v arg1_v) output_v)
  				) (BatList.combine arg0_sig arg1_sig) output_sig
  			) bv_sigs
			in
			arg1_sig
			(* if not (BatSet.is_empty arg1_sig) then arg1_sig                    *)
			(* else                                                               *)
				
				(* let arg1_sig =                                             *)
    		(* 	BatList.fold_left (fun acc (arg0_const, output_const) -> *)
    		(* 		let arg0_v = get_bv arg0_const in                      *)
    		(* 		let output_v = get_bv output_const in                  *)
    		(* 		let arg1_v = (Int64.sub output_v arg0_v) in            *)
  			(* 		acc @ [(CBV arg1_v)]                                   *)
    		(* 	) [] (BatList.combine arg0_sig output_sig)               *)
				(* in                                                         *)
				(* (* if (check_distance arg1_sig output_sig bv_sigs) then *) *)
				(* 	BatSet.singleton arg1_sig                                *)
				(* (* else           *)                                       *)
				(* (* 	BatSet.empty *)                                       *)
				
	else if (String.compare op "bvsub") = 0 then
		if (type_of_signature output_sig) <> BV then assert false
		else if (BatList.length arg_sigs) = 0 then
			BatSet.filter (fun arg0_sig ->
				let arg1_sig = fun_apply_signature "bvsub" [arg0_sig; output_sig] in 
				BatSet.mem arg1_sig bv_sigs
			) bv_sigs
			(* BatSet.filter (fun arg0_sig ->                       *)
			(* 	BatList.for_all (fun (arg0_const, output_const) -> *)
			(* 		let arg0_v = get_bv arg0_const in                *)
			(* 		let output_v = get_bv output_const in            *)
			(* 		(* let arg1_v = Int64.sub arg0_v output_v in  *) *)
			(* 		(not (Int64.equal output_v Int64.zero))          *)
			(* 	) (BatList.combine arg0_sig output_sig)            *)
			(* ) bv_sigs                                            *)
		else
			let arg0_sig = List.nth arg_sigs 0 in
			let arg1_sig =
  			BatSet.filter (fun arg1_sig ->
  				BatList.for_all2 (fun (arg0_const, arg1_const) output_const ->
  					let arg0_v = get_bv arg0_const in
  					let arg1_v = get_bv arg1_const in
  					let output_v = get_bv output_const in
  					(Int64.equal (Int64.sub arg0_v arg1_v) output_v)
  				) (BatList.combine arg0_sig arg1_sig) output_sig
  			) bv_sigs
			in
			arg1_sig
			(* if not (BatSet.is_empty arg1_sig) then arg1_sig              *)
			(* else                                                         *)
			(* 	let arg1_sig =                                             *)
    	(* 		BatList.fold_left (fun acc (arg0_const, output_const) -> *)
    	(* 			let arg0_v = get_bv arg0_const in                      *)
    	(* 			let output_v = get_bv output_const in                  *)
    	(* 			let arg1_v = (Int64.sub arg0_v output_v) in            *)
  		(* 			acc @ [(CBV arg1_v)]                                   *)
    	(* 		) [] (BatList.combine arg0_sig output_sig)               *)
			(* 	in                                                         *)
			(* 	if (check_distance arg1_sig output_sig bv_sigs) then	     *)
			(* 		BatSet.singleton arg1_sig                                *)
			(* 	else                                                       *)
			(* 		BatSet.empty                                             *)
	else if (String.compare op "bvneg") = 0 then
		if (type_of_signature output_sig) <> BV then assert false
		else 
			let arg1_sigs =
    		BatSet.filter (fun arg0_sig ->
    			BatList.for_all (fun (arg0_const, output_const) ->
    				let arg0_v = get_bv arg0_const in
    				let output_v = get_bv output_const in
    				(Int64.equal (Int64.neg arg0_v) output_v)
    			) (BatList.combine arg0_sig output_sig)
    		) bv_sigs
			in
			arg1_sigs
			(* if not (BatSet.is_empty arg1_sigs) then arg1_sigs        *)
			(* else                                                     *)
			(* 	let arg1_sig =                                         *)
  		(* 		BatList.fold_left (fun acc output_const ->           *)
    	(* 			let output_v = get_bv output_const in              *)
    	(* 			acc @ [(CBV (Int64.neg output_v))]                 *)
    	(* 		) [] output_sig                                      *)
			(* 	in                                                     *)
			(* 	if (check_distance arg1_sig output_sig bv_sigs) then	 *)
			(* 		BatSet.singleton arg1_sig                            *)
			(* 	else                                                   *)
			(* 		BatSet.empty                                         *)
	else if (String.compare op "bvnot") = 0 then
		if (type_of_signature output_sig) <> BV then assert false
		else 
			let arg1_sigs =
  			BatSet.filter (fun arg0_sig ->
  				BatList.for_all (fun (arg0_const, output_const) ->
  					let arg0_v = get_bv arg0_const in
  					let output_v = get_bv output_const in
  					(Int64.equal (Int64.lognot arg0_v) output_v)
  				) (BatList.combine arg0_sig output_sig)
  			) bv_sigs
			in
			arg1_sigs
			(* if not (BatSet.is_empty arg1_sigs) then arg1_sigs      *)
			(* else                                                   *)
			(* 	let arg1_sig =                                       *)
    	(* 		BatList.fold_left (fun acc output_const ->         *)
    	(* 			let output_v = get_bv output_const in            *)
    	(* 			acc @ [(CBV (Int64.lognot output_v))]            *)
    	(* 		) [] output_sig                                    *)
			(* 	in                                                   *)
			(* 	if (check_distance arg1_sig output_sig bv_sigs) then *)
			(* 		BatSet.singleton arg1_sig                          *)
			(* 	else                                                 *)
			(* 		BatSet.empty                                       *)
	else if (String.compare op "bvmul") = 0 then
		if (type_of_signature output_sig) <> BV then assert false
		else if (BatList.length arg_sigs) = 0 then
			BatSet.filter (fun arg0_sig ->
				BatList.for_all (fun (arg0_const, output_const) ->
					let arg0_v = get_bv arg0_const in
					let output_v = get_bv output_const in 
					(* arg0 * arg1 = output *)
					(* to prevent from generating the same sub problem *)
					(not (Int64.equal arg0_v Int64.zero)) && (* 0 * ... = output_v *)
					(not (Int64.equal arg0_v Int64.one)) && (* 1 * output_v = output_v *)
					(not (Int64.equal output_v Int64.zero)) &&  (* ... * 0 = 0 *)
					(Int64.equal (Int64.rem output_v arg0_v) Int64.zero) &&  (* output | arg0 *)
					(Int64.compare (Int64.abs arg0_v) (Int64.abs output_v)) < 0 && (* |arg0| < |output| *)
					(Int64.compare (Int64.div output_v arg0_v) (Int64.abs output_v)) < 0 && (* |arg1| < |output| *)
					(check_ratio (Int64.div output_v arg0_v) output_v) 
				) (BatList.combine arg0_sig output_sig)
			) bv_sigs
		(* else                                                               *)
		(* 	let arg0_sig = List.nth arg_sigs 0 in                            *)
		(* 	BatSet.filter (fun arg1_sig ->                                   *)
		(* 		BatList.for_all2 (fun (arg0_const, arg1_const) output_const -> *)
		(* 			let arg0_v = get_bv arg0_const in                            *)
		(* 			let arg1_v = get_bv arg1_const in                            *)
		(* 			let output_v = get_bv output_const in                        *)
		(* 			(Int64.equal (Int64.mul arg0_v arg1_v) output_v) &&          *)
		(* 			(bitcount arg0_v) <= (bitcount output_v) &&                  *)
		(* 			(bitcount arg1_v) <= (bitcount output_v)                     *)
		(* 		) (BatList.combine arg0_sig arg1_sig) output_sig               *)
		(* 	) bv_sigs                                                        *)
		else
			let arg0_sig = List.nth arg_sigs 0 in
			BatList.fold_left (fun acc (arg0_const, output_const) ->
				let arg0_v = get_bv arg0_const in
				let output_v = get_bv output_const in
				let _ = assert (not (Int64.equal arg0_v Int64.zero)) in
				let arg1_v = Int64.div output_v arg0_v in
				acc @ [(CBV arg1_v)]
			) [] (BatList.combine arg0_sig output_sig) |> BatSet.singleton
	else if (String.compare op "bvsdiv") = 0 then
		if (type_of_signature output_sig) <> BV then assert false
		else if (BatList.length arg_sigs) = 0 then
			(* a / b = c    a = bc + k  (k < b)    (a - k) / c = b   가능한 b가 너무 많음. *)
			(* 현재 i번째 예제를 다루고 있다고 하면, i번째 bv값을 모두 뒤져서 a / b = c 가 되는 b가 있는지 확인. *)
			(* worst: |C| * |C| => |C| * |E| * |C| * |C| *)
			(* expected: |C| * |C| => |C| * |E|  C ~ 10000, E ~ 1000 *)
			(* arg0 / arg1 = output  <=> arg0 = arg1 * output + k (|k| < |arg1|)*)
			(* arg1에 대한 조건 추출후, 그 조건을 만족하는 arg1 찾기를 |C| 보다 더 빨리하는 방법? *)
			(* k = arg0 - arg1 * output *)
			BatSet.filter (fun arg0_sig ->
				BatList.for_all (fun (arg0_const, output_const) ->
					let arg0_v = get_bv arg0_const in
					let output_v = get_bv output_const in
					(* if (Int64.equal Int64.zero output_v) then false *)
					(* else                                            *)
					(* arg0_v / arg1_v = output_v *)
					(* output_v = arg1_v * arg0_v + k, |k| < |arg1_v| *)
					(Int64.compare (Int64.abs output_v) (Int64.abs arg0_v)) <= 0
					(* let arg1_v = Int64.div arg0_v output_v in            *)
					(* let k = Int64.rem arg0_v output_v in                 *)
					(* (not (Int64.equal Int64.zero output_v))              *)
					(* (Int64.compare (Int64.abs k) (Int64.abs arg1_v)) < 0 *)
				) (BatList.combine arg0_sig output_sig)
			) bv_sigs
		else 
			let arg0_sig = List.nth arg_sigs 0 in
			let arg1_sig = 
  			BatSet.filter (fun arg1_sig ->
  				BatList.for_all2 (fun (arg0_const, arg1_const) output_const ->
  					let arg0_v = get_bv arg0_const in
  					let arg1_v = get_bv arg0_const in
  					let output_v = get_bv output_const in
  					(not (Int64.equal arg1_v Int64.zero)) && 
  					(Int64.equal (Int64.div arg0_v arg1_v) output_v)
  				) (BatList.combine arg0_sig arg1_sig) output_sig
  			) bv_sigs
			in 
			arg1_sig
			(* if (not (BatSet.is_empty arg1_sig)) then arg1_sig                                                                               *)
			(* else                                                                                                                            *)
			(* 	let arg1_sig =                                                                                                                *)
    	(* 		BatList.fold_left (fun acc (arg0_const, output_const) ->                                                                    *)
    	(* 			let arg0_v = get_bv arg0_const in                                                                                         *)
    	(* 			let output_v = get_bv output_const in                                                                                     *)
  		(* 			(* arg0_v / arg1_v = output_v *)                                                                                          *)
  		(* 			(* arg0_v = arg1_v * output_v + k (|k| < |arg1_v|) *)                                                                     *)
    	(* 			let arg1_v = Int64.div arg0_v output_v in                                                                                 *)
    	(* 			let _ = assert (not (Int64.equal Int64.zero output_v)) in                                                                 *)
    	(* 			let k = Int64.rem arg0_v output_v in                                                                                      *)
    	(* 			let _ = if (Int64.equal Int64.zero arg1_v) then                                                                           *)
			(* 				failwith (Printf.sprintf "%s / %s = %s" (Int64.to_string arg0_v) (Int64.to_string arg1_v) (Int64.to_string output_v) )  *)
			(* 			in                                                                                                                        *)
    	(* 			acc @ [(CBV arg1_v)]                                                                                                      *)
    	(* 		) [] (BatList.combine arg0_sig output_sig)                                                                                  *)
			(* 	in                                                                                                                            *)
			(* 	if (check_distance arg1_sig output_sig bv_sigs) then	                                                                        *)
			(* 		BatSet.singleton arg1_sig                                                                                                   *)
			(* 	else                                                                                                                          *)
			(* 		BatSet.empty                                                                                                                *)
	else if (String.compare op "bvudiv") = 0 then
		if (type_of_signature output_sig) <> BV then assert false
		else if (BatList.length arg_sigs) = 0 then bv_sigs
			(* BatSet.filter (fun arg0_sig ->                                   *)
			(* 	BatList.for_all (fun (arg0_const, output_const) ->             *)
			(* 		let arg0_v = get_bv arg0_const in                            *)
			(* 		let output_v = get_bv output_const in                        *)
			(* 		(* if (Int64.equal Int64.zero output_v) then false *)        *)
			(* 		(* else                                            *)        *)
			(* 		(* arg0_v / arg1_v = output_v *)                             *)
			(* 		(* output_v = arg1_v * arg0_v + k, |k| < |arg1_v| *)         *)
			(* 		(Int64.compare (Int64.abs output_v) (Int64.abs arg0_v)) <= 0 *)
			(* 		(* let arg1_v = Int64.unsigned_div arg0_v output_v in   *)   *)
			(* 		(* let k = Int64.unsigned_rem arg0_v output_v in        *)   *)
			(* 		(* (not (Int64.equal Int64.zero output_v)) &&           *)   *)
			(* 		(* (check_ratio arg1_v output_v) &&                     *)   *)
			(* 		(* (Int64.compare (Int64.abs k) (Int64.abs arg1_v)) < 0 *)   *)
			(* 	) (BatList.combine arg0_sig output_sig)                        *)
			(* ) bv_sigs                                                        *)
		else 
			let arg0_sig = List.nth arg_sigs 0 in
			BatSet.filter (fun arg1_sig ->
				BatList.for_all2 (fun (arg0_const, arg1_const) output_const ->
					let arg0_v = get_bv arg0_const in
					let arg1_v = get_bv arg0_const in
					let output_v = get_bv output_const in
					(not (Int64.equal Int64.zero arg1_v)) && 
					(Int64.equal (Int64.unsigned_div arg0_v arg1_v) output_v)
				) (BatList.combine arg0_sig arg1_sig) output_sig
			) bv_sigs
			(* BatList.fold_left (fun acc (arg0_const, output_const) ->                                                                                                                    *)
			(* 	let arg0_v = get_bv arg0_const in                                                                                                                                         *)
			(* 	let output_v = get_bv output_const in                                                                                                                                     *)
			(* 	let _ = assert (not (Int64.equal Int64.zero output_v)) in                                                                                                                 *)
			(* 	let arg1_v = Int64.unsigned_div arg0_v output_v in                                                                                                                        *)
			(* 	let k = Int64.unsigned_rem arg0_v output_v in                                                                                                                             *)
			(* 	let _ = if (Int64.equal Int64.zero arg1_v) then failwith (Printf.sprintf "%s / %s = %s" (Int64.to_string arg0_v) (Int64.to_string arg1_v) (Int64.to_string output_v) ) in *)
			(* 	acc @ [(CBV arg1_v)]                                                                                                                                                      *)
			(* ) [] (BatList.combine arg0_sig output_sig) |> BatSet.singleton                                                                                                              *)
	else if (String.compare op "bvsrem") = 0 then
		if (type_of_signature output_sig) <> BV then assert false
		else if (BatList.length arg_sigs) = 0 then
			BatSet.filter (fun arg0_sig ->
				BatList.for_all (fun (arg0_const, output_const)  ->
					let arg0_v = get_bv arg0_const in
					let output_v = get_bv output_const in
					(Int64.compare (Int64.abs output_v) (Int64.abs arg0_v)) <= 0 
				) (BatList.combine arg0_sig output_sig) 
			) bv_sigs
			(* (* a % b = c  <= a = bq + c, |c| < |b| 가능한 b가 많음. *)                                                            *)
			(* BatSet.filter (fun arg0_sig ->                                                                      *)
			(* 	BatList.for_all (fun (arg0_const, output_const) ->                                                *)
			(* 		let arg0_v = get_bv arg0_const in                                                               *)
			(* 		let output_v = get_bv output_const in                                                           *)
			(* 		if (Int64.equal Int64.zero (Int64.sub arg0_v output_v)) ||                                      *)
			(* 			 (Int64.equal Int64.zero arg0_v) then false                                                   *)
			(* 		else                                                                                            *)
			(* 		let arg1_v =                                                                                    *)
			(* 			let factor1, factor2 = Factorization.factorize (Int64.sub arg0_v output_v) in                 *)
			(* 			let bigger_factor =                                                                           *)
			(* 				if (Int64.compare (Int64.abs factor1) (Int64.abs factor2)) < 0 then factor2 else factor1    *)
			(* 			in                                                                                            *)
			(* 			if (Int64.compare (Int64.abs output_v) (Int64.abs bigger_factor)) < 0 then Some bigger_factor *)
			(* 			else None                                                                                     *)
			(* 		in                                                                                              *)
			(* 		arg1_v <> None                                                                                  *)
			(* 	) (BatList.combine arg0_sig output_sig)                                                           *)
			(* ) bv_sigs                                                                                           *)
		else 
			(* let arg0_sig = List.nth arg_sigs 0 in                                                                                          *)
			(* BatList.fold_left (fun acc (arg0_const, output_const) ->                                                                       *)
			(* 	let arg0_v = get_bv arg0_const in                                                                                            *)
			(* 	let output_v = get_bv output_const in                                                                                        *)
			(* 	let arg1_v =                                                                                                                 *)
			(* 		let factor1, factor2 = Factorization.factorize (Int64.sub arg0_v output_v) in                                              *)
			(* 		let bigger_factor =                                                                                                        *)
			(* 			if (Int64.compare (Int64.abs factor1) (Int64.abs factor2)) < 0 then factor2 else factor1                                 *)
			(* 		in                                                                                                                         *)
			(* 		let _ = assert ((Int64.compare (Int64.abs output_v) (Int64.abs bigger_factor)) < 0) in                                     *)
			(* 		bigger_factor                                                                                                              *)
			(* 	in                                                                                                                           *)
			(* 	let _ =                                                                                                                      *)
			(* 		if not (Int64.equal (Int64.rem arg0_v arg1_v) output_v) then                                                               *)
			(* 			failwith (Printf.sprintf "%s mod %s != %s" (Int64.to_string arg0_v) (Int64.to_string arg1_v) (Int64.to_string output_v)) *)
			(* 	in                                                                                                                           *)
			(* 	acc @ [(CBV arg1_v)]                                                                                                         *)
			(* ) [] (BatList.combine arg0_sig output_sig) |> BatSet.singleton                                                                 *)
			let arg0_sig = List.nth arg_sigs 0 in
			BatSet.filter (fun arg1_sig ->
				BatList.for_all2 (fun (arg0_const, arg1_const) output_const ->
					let arg0_v = get_bv arg0_const in
					let arg1_v = get_bv arg1_const in
					let output_v = get_bv output_const in
					(not (Int64.equal arg1_v Int64.zero)) &&
					(Int64.equal (Int64.rem arg0_v arg1_v) output_v)
				) (BatList.combine arg0_sig arg1_sig) output_sig
			) bv_sigs
	else if (String.compare op "bvurem") = 0 then
		if (type_of_signature output_sig) <> BV then assert false
		else if (BatList.length arg_sigs) = 0 then bv_sigs
			(* BatSet.filter (fun arg0_sig ->                                     *)
			(* 	BatList.for_all (fun (arg0_const, output_const) ->               *)
			(* 		let arg0_v = get_bv arg0_const in                              *)
			(* 		let output_v = get_bv output_const in                          *)
			(* 		(* to prevent from generating the same sub problem *)          *)
			(* 		(Int64.compare (Int64.abs arg0_v) (Int64.abs output_v)) > 0 && *)
			(* 		(not (Int64.equal arg0_v Int64.zero))                          *)
			(* 	) (BatList.combine arg0_sig output_sig)                          *)
			(* ) bv_sigs                                                          *)
		else 
			let arg0_sig = List.nth arg_sigs 0 in
			BatSet.filter (fun arg1_sig -> 
				BatList.for_all2 (fun (arg0_const, arg1_const) output_const ->
					let arg0_v = get_bv arg0_const in
					let arg1_v = get_bv arg1_const in
					let output_v = get_bv output_const in
					(not (Int64.equal arg1_v Int64.zero)) && 
					(Int64.equal (Int64.unsigned_rem arg0_v arg1_v) output_v)
				) (BatList.combine arg0_sig arg1_sig) output_sig
			) bv_sigs
	else if (String.compare op "bvand") = 0 then
		if (type_of_signature output_sig) <> BV then assert false
		else if (BatList.length arg_sigs) = 0 then
			BatSet.filter (fun arg0_sig ->
				BatList.for_all (fun (arg0_const, output_const) ->
					let arg0_v = get_bv arg0_const in
					let output_v = get_bv output_const in
					let arg0_v_str = int64_to_string_in_binary arg0_v in
					let output_v_str = int64_to_string_in_binary output_v in
					BatList.fold_left (fun acc (arg0_v_c, output_v_c) ->
						((not (output_v_c = '1')) || (arg0_v_c = '1')) && acc   			  
					) true
					(BatList.combine (BatString.to_list arg0_v_str) (BatString.to_list output_v_str))
				) (BatList.combine arg0_sig output_sig)
			) bv_sigs
		else
			let arg0_sig = List.nth arg_sigs 0 in
			BatSet.filter (fun arg1_sig ->
				BatList.for_all2 (fun (arg0_const, arg1_const) output_const ->
					let arg0_v = get_bv arg0_const in
					let arg1_v = get_bv arg1_const in
					let output_v = get_bv output_const in
					Int64.equal (Int64.logand arg0_v arg1_v) output_v
				) (BatList.combine arg0_sig arg1_sig) output_sig
			) bv_sigs
	else if (String.compare op "bvor") = 0 then
		if (type_of_signature output_sig) <> BV then assert false
		else if (BatList.length arg_sigs) = 0 then
			BatSet.filter (fun arg0_sig ->
				BatList.for_all (fun (arg0_const, output_const) ->
					let arg0_v = get_bv arg0_const in
					let output_v = get_bv output_const in
					let arg0_v_str = try int64_to_string_in_binary arg0_v with _ -> failwith (Int64.to_string arg0_v) in
					let output_v_str = try int64_to_string_in_binary output_v with _ -> failwith (Int64.to_string arg0_v) in
					BatList.fold_left (fun acc (arg0_v_c, output_v_c) ->
						((not (output_v_c = '0')) || (arg0_v_c = '0')) && acc   			  
					) true
					(BatList.combine (BatString.to_list arg0_v_str) (BatString.to_list output_v_str))
				) (BatList.combine arg0_sig output_sig)
			) bv_sigs
		else
			let arg0_sig = List.nth arg_sigs 0 in
			BatSet.filter (fun arg1_sig ->
				BatList.for_all2 (fun (arg0_const, arg1_const) output_const ->
					let arg0_v = get_bv arg0_const in
					let arg1_v = get_bv arg1_const in
					let output_v = get_bv output_const in
					Int64.equal (Int64.logor arg0_v arg1_v) output_v &&
					(bitcount arg0_v) <= (bitcount output_v) && 
					(bitcount arg1_v) <= (bitcount output_v)		
				) (BatList.combine arg0_sig arg1_sig) output_sig
			) bv_sigs
	else if (String.compare op "bvxor") = 0 then
		if (type_of_signature output_sig) <> BV then assert false
		else if (BatList.length arg_sigs) = 0 then 
			BatSet.filter (fun arg0_sig ->
				let arg1_sig = fun_apply_signature "bvxor" [arg0_sig; output_sig] in 
				BatSet.mem arg1_sig bv_sigs
			) bv_sigs
		else
			let arg0_sig = List.nth arg_sigs 0 in
			let arg1_sigs = 
  			BatSet.filter (fun arg1_sig ->
  				BatList.for_all2 (fun (arg0_const, arg1_const) output_const ->
  					let arg0_v = get_bv arg0_const in
  					let arg1_v = get_bv arg1_const in
  					let output_v = get_bv output_const in
  					Int64.equal (Int64.logxor arg0_v arg1_v) output_v 
  				) (BatList.combine arg0_sig arg1_sig) output_sig
  			) bv_sigs
			in 
			(* arg1_sigs *)
			if not (BatSet.is_empty arg1_sigs) then arg1_sigs
			else
			let arg0_sig = List.nth arg_sigs 0 in
			BatList.fold_left (fun acc (arg0_const, output_const) ->
				let arg0_v = get_bv arg0_const in
				let output_v = get_bv output_const in
				acc @ [CBV (Int64.logxor arg0_v output_v)]
			) [] (BatList.combine arg0_sig output_sig) |> BatSet.singleton
	else if (String.compare op "bvashr") = 0 then
		if (type_of_signature output_sig) <> BV then assert false
		else if (BatList.length arg_sigs) = 0 then 
			(* let arg0_sigs =                                                                       *)
  		(* 	BatSet.fold (fun arg1_sig acc ->                                                    *)
  		(* 		try                                                                               *)
    	(* 			let arg0_sig =                                                                  *)
      (* 				BatList.map (fun (arg1_const, output_const) ->                                *)
      (* 					let arg1_v = get_bv arg1_const |> Int64.to_int in                           *)
      (*   				let output_v = get_bv output_const in                                       *)
      (*   				let arg0_v = Int64.shift_left output_v arg1_v in                            *)
      (*   				if (Int64.equal output_v (Int64.shift_right arg0_v arg1_v)) then            *)
      (*   					CBV (arg0_v)                                                              *)
      (*   				else failwith "bvashr_Arg0"                                                 *)
      (* 				)	(BatList.combine arg1_sig output_sig)                                      *)
    	(* 			in                                                                              *)
    	(* 			BatSet.add arg0_sig acc  	                                                     *)
  		(* 		with _ -> acc                                                                     *)
  		(* 	) bv_sigs BatSet.empty                                                              *)
			(* in                                                                                    *)
			(* BatSet.filter (fun arg0_sig -> check_distance arg0_sig output_sig bv_sigs) arg0_sigs  *)
			BatSet.filter (fun arg0_sig ->
				BatList.for_all (fun (arg0_const, output_const) ->
					let arg0_v = get_bv arg0_const in
					let output_v = get_bv output_const in
					BatList.exists (fun i ->
						(Int64.equal output_v (Int64.shift_right arg0_v i)) &&
						(Int64.compare (Int64.mul output_v arg0_v) Int64.zero) <> 0
					) (BatList.range 1 `To 63)
				) (BatList.combine arg0_sig output_sig)
			) bv_sigs
			(* BatList.fold_left (fun acc i ->                                         *)
			(* 	try                                                                   *)
  		(* 		let arg0_sig =                                                      *)
  		(* 			BatList.map (fun output_const ->                                  *)
  		(* 				let output_v = get_bv output_const in                           *)
  		(* 				let arg0_v = (Int64.shift_left output_v i) in                   *)
  		(* 				if (Int64.compare output_v (Int64.shift_right arg0_v i)) = 0 && *)
  		(* 					 (not (Int64.equal Int64.zero arg0_v)) then                   *)
  		(* 						(CBV arg0_v)                                                *)
    	(* 				else failwith "bvashr_arg0"                                     *)
  		(* 			) output_sig                                                      *)
  		(* 		in                                                                  *)
  		(* 		BatSet.add arg0_sig acc                                             *)
			(* 	with _ -> acc                                                         *)
			(* ) BatSet.empty (BatList.range 1 `To 63)                                 *)
		else  
			let arg0_sig = List.nth arg_sigs 0 in
			BatSet.filter (fun arg1_sig ->
				BatList.for_all2 (fun (arg0_const, arg1_const) output_const ->
					let arg0_v = get_bv arg0_const in
					let arg1_v = Int64.to_int (get_bv arg1_const) in
					let output_v = get_bv output_const in
					Int64.equal (Int64.shift_right arg0_v arg1_v) output_v
				) (BatList.combine arg0_sig arg1_sig) output_sig
			) bv_sigs
			(* let arg0_sig = List.nth arg_sigs 0 in                                                                                                                                                                                                                                                      *)
			(* BatList.fold_left (fun acc (arg0_const, output_const) ->                                                                                                                                                                                                                                   *)
			(* 	let arg0_v = get_bv arg0_const in                                                                                                                                                                                                                                                        *)
			(* 	let output_v = get_bv output_const in                                                                                                                                                                                                                                                    *)
			(* 	let rec iter i =                                                                                                                                                                                                                                                                         *)
			(* 		if (i >= 64) then Int64.of_int i                                                                                                                                                                                                                                                       *)
			(* 		else if (Int64.equal output_v (Int64.shift_right arg0_v i)) then                                                                                                                                                                                                                       *)
			(* 			Int64.of_int i                                                                                                                                                                                                                                                                       *)
			(* 		else iter (i + 1)                                                                                                                                                                                                                                                                      *)
			(* 	in                                                                                                                                                                                                                                                                                       *)
			(* 	let arg1_v = iter 0 in                                                                                                                                                                                                                                                                   *)
			(* 	(* let i = Int64.to_float (Int64.div arg0_v output_v) in                                                                                                                                                                                                                              *) *)
			(* 	(* let arg1_v = Int64.of_float ((log i) /. (log 2.0)) in                                                                                                                                                                                                                              *) *)
			(* 	let _ = if not ((Int64.to_int arg1_v) >= 0 && (Int64.to_int arg1_v) <= 63) then                                                                                                                                                                                                          *)
			(* 		failwith (Printf.sprintf "bvashr %s %s %s %s %s" (Int64.to_string arg1_v) (int64_to_string_in_binary arg0_v) (int64_to_string_in_binary output_v) (Int64.to_string arg0_v) (Int64.to_string output_v)) in                                                                              *)
			(* 	acc @ [CBV (arg1_v)]                                                                                                                                                                                                                                                                     *)
			(* ) [] (BatList.combine arg0_sig output_sig) |> BatSet.singleton                                                                                                                                                                                                                             *)
	else if (String.compare op "bvlshr") = 0 then
		if (type_of_signature output_sig) <> BV then assert false
		else if (BatList.length arg_sigs) = 0 then 
			(* let arg0_sigs =                                                                      *)
  		(* 	BatSet.fold (fun arg1_sig acc ->                                                   *)
  		(* 		try                                                                              *)
    	(* 			let arg0_sig =                                                                 *)
      (* 				BatList.map (fun (arg1_const, output_const) ->                               *)
      (* 					let arg1_v = get_bv arg1_const |> Int64.to_int in                          *)
      (*   				let output_v = get_bv output_const in                                      *)
      (*   				let arg0_v = Int64.shift_left output_v arg1_v in                           *)
      (*   				if (Int64.equal output_v (Int64.shift_right_logical arg0_v arg1_v)) then   *)
      (*   					CBV (arg0_v)                                                             *)
      (*   				else failwith "bvlshr_Arg0"                                                *)
      (* 				)	(BatList.combine arg1_sig output_sig)                                     *)
    	(* 			in                                                                             *)
    	(* 			BatSet.add arg0_sig acc  	                                                    *)
  		(* 		with _ -> acc                                                                    *)
  		(* 	) bv_sigs BatSet.empty                                                             *)
			(* in                                                                                   *)
			(* BatSet.filter (fun arg0_sig -> check_distance arg0_sig output_sig bv_sigs) arg0_sigs *)
			BatSet.filter (fun arg0_sig ->
				BatList.for_all (fun (arg0_const, output_const) ->
					let arg0_v = get_bv arg0_const in
					let output_v = get_bv output_const in
					BatList.exists (fun i ->
						(Int64.equal output_v (Int64.shift_right_logical arg0_v i)) 
						(* &&                                                          *)
						(* (Int64.compare (Int64.mul output_v arg0_v) Int64.zero) <> 0 *)
					) (BatList.range 1 `To 63)
				) (BatList.combine arg0_sig output_sig)
			) bv_sigs
			(* BatList.fold_left (fun acc i ->                                               *)
			(* 	try                                                                         *)
  		(* 		let arg0_sig =                                                            *)
  		(* 			BatList.map (fun output_const ->                                        *)
  		(* 				let output_v = get_bv output_const in                                 *)
  		(* 				let arg0_v = (Int64.shift_left output_v i) in                         *)
  		(* 				if (Int64.compare output_v (Int64.shift_right_logical arg0_v i)) = 0  *)
			(* 					 (* &&                                     *)                       *)
  		(* 					 (* (not (Int64.equal Int64.zero arg0_v))  *)                       *)
			(* 					then                                                                *)
  		(* 						(CBV arg0_v)                                                      *)
    	(* 				else failwith "bvlshr_arg0"                                           *)
  		(* 			) output_sig                                                            *)
  		(* 		in                                                                        *)
  		(* 		BatSet.add arg0_sig acc                                                   *)
			(* 	with _ -> acc                                                               *)
			(* ) BatSet.empty (BatList.range 1 `To 63)                                       *)
		else
			let arg0_sig = List.nth arg_sigs 0 in
			BatSet.filter (fun arg1_sig ->
				BatList.for_all2 (fun (arg0_const, arg1_const) output_const ->
					let arg0_v = get_bv arg0_const in
					let arg1_v = Int64.to_int (get_bv arg1_const) in
					let output_v = get_bv output_const in
					Int64.equal (Int64.shift_right_logical arg0_v arg1_v) output_v
				) (BatList.combine arg0_sig arg1_sig) output_sig
			) bv_sigs
			  
			(* let arg0_sig = List.nth arg_sigs 0 in                                                                                                                                                                                                                                                      *)
			(* BatList.fold_left (fun acc (arg0_const, output_const) ->                                                                                                                                                                                                                                   *)
			(* 	let arg0_v = get_bv arg0_const in                                                                                                                                                                                                                                                        *)
			(* 	let output_v = get_bv output_const in                                                                                                                                                                                                                                                    *)
			(* 	let rec iter i =                                                                                                                                                                                                                                                                         *)
			(* 		if i > 64 then Int64.of_int i                                                                                                                                                                                                                                                          *)
			(* 		else if (Int64.equal output_v (Int64.shift_right_logical arg0_v i)) then                                                                                                                                                                                                               *)
			(* 			Int64.of_int i                                                                                                                                                                                                                                                                       *)
			(* 		else iter (i + 1)                                                                                                                                                                                                                                                                      *)
			(* 	in                                                                                                                                                                                                                                                                                       *)
			(* 	let arg1_v = iter 0 in                                                                                                                                                                                                                                                                   *)
			(* 	(* let i = Int64.to_float (Int64.div arg0_v output_v) in                                                                                                                                                                                                                              *) *)
			(* 	(* let arg1_v = Int64.of_float ((log i) /. (log 2.0)) in                                                                                                                                                                                                                              *) *)
			(* 	let _ = if not ((Int64.to_int arg1_v) >= 0 && (Int64.to_int arg1_v) <= 63) then                                                                                                                                                                                                          *)
			(* 		failwith (Printf.sprintf "bvlshr %s %s %s %s %s" (Int64.to_string arg1_v) (int64_to_string_in_binary arg0_v) (int64_to_string_in_binary output_v) (Int64.to_string arg0_v) (Int64.to_string output_v)) in                                                                              *)
			(* 	acc @ [CBV (arg1_v)]                                                                                                                                                                                                                                                                     *)
			(* ) [] (BatList.combine arg0_sig output_sig) |> BatSet.singleton                                                                                                                                                                                                                             *)
			
	else if (String.compare op "bvshl") = 0 then
		if (type_of_signature output_sig) <> BV then assert false
		else if (BatList.length arg_sigs) = 0 then 
			(* let arg0_sigs =                                                                      *)
  		(* 	BatSet.fold (fun arg1_sig acc ->                                                   *)
  		(* 		try                                                                              *)
    	(* 			let arg0_sig =                                                                 *)
      (* 				BatList.map (fun (arg1_const, output_const) ->                               *)
      (* 					let arg1_v = get_bv arg1_const |> Int64.to_int in                          *)
      (*   				let output_v = get_bv output_const in                                      *)
      (*   				let arg0_v = Int64.shift_right output_v arg1_v in                          *)
			(* 					let arg0_v' = Int64.shift_right_logical output_v arg1_v in                 *)
      (*   				if (Int64.equal output_v (Int64.shift_left arg0_v arg1_v)) then            *)
      (*   					CBV (arg0_v)                                                             *)
      (*   				else if (Int64.equal output_v (Int64.shift_left arg0_v' arg1_v)) then      *)
			(* 						CBV (arg0_v')                                                            *)
			(* 					else failwith "bvshl_Arg0"                                                 *)
      (* 				)	(BatList.combine arg1_sig output_sig)                                     *)
    	(* 			in                                                                             *)
    	(* 			BatSet.add arg0_sig acc  	                                                    *)
  		(* 		with _ -> acc                                                                    *)
  		(* 	) bv_sigs BatSet.empty                                                             *)
			(* in                                                                                   *)
			(* BatSet.filter (fun arg0_sig -> check_distance arg0_sig output_sig bv_sigs) arg0_sigs *)
			
			(* BatSet.filter (fun arg0_sig ->                                    *)
			(* 	BatList.for_all (fun (arg0_const, output_const) ->              *)
			(* 		let arg0_v = get_bv arg0_const in                             *)
			(* 		let output_v = get_bv output_const in                         *)
			(* 		BatList.exists (fun i ->                                      *)
			(* 			(Int64.equal output_v (Int64.shift_left arg0_v i)) &&       *)
			(* 			(Int64.compare (Int64.mul output_v arg0_v) Int64.zero) <> 0 *)
			(* 		) (BatList.range 1 `To 63)                                    *)
			(* 	) (BatList.combine arg0_sig output_sig)                         *)
			(* )                                                                 *)
			bv_sigs
			
			(* BatList.fold_left (fun acc i ->                                         *)
			(* 	try                                                                   *)
  		(* 		let arg0_sig =                                                      *)
  		(* 			BatList.map (fun output_const ->                                  *)
  		(* 				let output_v = get_bv output_const in                           *)
			(* 				let arg0_v = (Int64.shift_right output_v i) in                  *)
  		(* 				if (Int64.compare output_v (Int64.shift_left arg0_v i)) = 0  && *)
			(* 					 (not (Int64.equal Int64.zero arg0_v)) then                   *)
			(* 						(CBV arg0_v)                                                *)
  		(* 				else failwith "bvshl_arg0"                                      *)
  		(* 			) output_sig                                                      *)
  		(* 		in                                                                  *)
  		(* 		BatSet.add arg0_sig acc                                             *)
			(* 	with _ -> acc                                                         *)
			(* ) BatSet.empty (BatList.range 1 `To 63)                                 *)
		else
			let arg0_sig = List.nth arg_sigs 0 in
			BatSet.filter (fun arg1_sig ->
				BatList.for_all2 (fun (arg0_const, arg1_const) output_const ->
					let arg0_v = get_bv arg0_const in
					let arg1_v = Int64.to_int (get_bv arg1_const) in
					let output_v = get_bv output_const in
					Int64.equal (Int64.shift_left arg0_v arg1_v) output_v
				) (BatList.combine arg0_sig arg1_sig) output_sig
			) bv_sigs
			
			(* let arg0_sig = List.nth arg_sigs 0 in                                                                                                                                                                        *)
			(* BatList.fold_left (fun acc (arg0_const, output_const) ->                                                                                                                                                     *)
			(* 	let arg0_v = get_bv arg0_const in                                                                                                                                                                          *)
			(* 	let output_v = get_bv output_const in                                                                                                                                                                      *)
			(* 	let rec iter i =                                                                                                                                                                                           *)
			(* 		if (i >= 64) then failwith "bvshl"                                                                                                                                                                       *)
			(* 		else if (Int64.equal output_v (Int64.shift_left arg0_v i)) then                                                                                                                                          *)
			(* 			Int64.of_int i                                                                                                                                                                                         *)
			(* 		else iter (i + 1)                                                                                                                                                                                        *)
			(* 	in                                                                                                                                                                                                         *)
			(* 	let arg1_v = iter 0 in                                                                                                                                                                                     *)
			(* 	(* let i = Int64.to_float (Int64.div output_v arg0_v) in *)                                                                                                                                                *)
			(* 	(* let arg1_v = Int64.of_float ((log i) /. (log 2.0)) in *)                                                                                                                                                *)
			(* 	let _ = if not ((Int64.to_int arg1_v) >= 0 && (Int64.to_int arg1_v) <= 63) then                                                                                                                            *)
			(* 		failwith (Printf.sprintf "bvshl %s %s %s %s %s" (Int64.to_string arg1_v) (int64_to_string_in_binary arg0_v) (int64_to_string_in_binary output_v) (Int64.to_string arg0_v) (Int64.to_string output_v)) in *)
			(* 	acc @ [CBV (arg1_v)]                                                                                                                                                                                       *)
			(* ) [] (BatList.combine arg0_sig output_sig) |> BatSet.singleton                                                                                                                                               *)
	(** LIA theory **)
	else if (String.compare op "+") = 0 then
		if (type_of_signature output_sig) <> Int then assert false
		else if (BatList.length arg_sigs) = 0 then
			BatSet.filter (fun arg0_sig ->
				BatList.for_all (fun (arg0_const, output_const) -> 
					let arg0_v = get_int arg0_const in
					let output_v = get_int output_const in
					(abs (output_v - arg0_v)) < (abs output_v)
					(* to prevent from generating the same sub problem *)
					(* ((abs arg0_v) < (abs output_v)) && (arg0_v <> 0) *)
				) (BatList.combine arg0_sig output_sig) 
			) int_sigs
		else 
			let arg0_sig = List.nth arg_sigs 0 in
			BatList.fold_left (fun acc (arg0_const, output_const) ->
				let arg0_v = get_int arg0_const in 
				let output_v = get_int output_const in
				acc @ [(CInt (output_v - arg0_v))]       	 
			) [] (BatList.combine arg0_sig output_sig) |> BatSet.singleton
	else if (String.compare op "-") = 0 then
		if (type_of_signature output_sig) <> Int then assert false
		else if (BatList.length arg_sigs) = 0 then 
			BatSet.filter (fun arg0_sig ->
				BatList.for_all (fun (arg0_const, output_const) ->
					let arg0_v = get_int arg0_const in
					let output_v = get_int output_const in
					(* to prevent from generating the same sub problem *)
					(abs (arg0_v - output_v)) < (abs output_v)
					(* (arg0_v > output_v)  *)
				) (BatList.combine arg0_sig output_sig) 
			) int_sigs
		else 
			let arg0_sig = List.nth arg_sigs 0 in
			BatList.fold_left (fun acc (arg0_const, output_const) ->
				let arg0_v = get_int arg0_const in 
				let output_v = get_int output_const in
				acc @ [(CInt (arg0_v - output_v))]        	 
			) [] (BatList.combine arg0_sig output_sig) |> BatSet.singleton
	(* else if (String.compare op "*") = 0 then *)
	(* else if (String.compare op "/") = 0 then *)
	(* else if (String.compare op "%") = 0 then *)
	
	else assert false				 		
		 
