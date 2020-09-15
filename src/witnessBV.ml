open Vocab
open Exprs
open BidirectionalUtils

(* |given_desired| * (theta ^ available_height) < 1 *)
(* <=> theta ^ available_height < 1 / |given_desired| *)
(* <=> available_height log_2 theta < - log_2 |given_desired| *)
(* <=> log_2 theta < - log_2 |given_desired| / available_height *)
(* <=> theta < 2 ^ (- log_2 |given_desired| / available_height) *)
(* we set theta s.t. |new_desired| / |given_desired| < theta *)
let check_ratio available_height given_desired new_desired =
	let _ = assert (available_height > 0) in 
	let theta = 2.0 ** ((-1. *. (log (Int64.to_float (Int64.abs given_desired)) /. log 2.)) /. (float_of_int available_height)) in 
	(Int64.to_float (Int64.abs new_desired)) < theta *. (Int64.to_float (Int64.abs given_desired)) 	

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
	

(** BV theory **)  
let witness available_height nt_sigs (int_sigs, bv_sigs, string_sigs, bool_sigs) rule output_sig arg_sigs =
	let op = Grammar.op_of_rule rule in
	if (String.compare op "bvadd") = 0 then
		if (BatList.length arg_sigs) = 0 then
			BatSet.filter (fun arg0_sig ->
				let arg1_sig = fun_apply_signature "bvsub" [output_sig; arg0_sig] in
				BatSet.mem arg1_sig bv_sigs
			) nt_sigs
			(* BatSet.filter (fun arg0_sig ->                                  *)
			(* 	BatList.for_all (fun (arg0_const, output_const) ->            *)
			(* 		let arg0_v = get_bv arg0_const in                           *)
			(* 		let output_v = get_bv output_const in                       *)
			(* 		let arg1_v = (Int64.sub output_v arg0_v) in                 *)
			(* 		(* to prevent from generating the same sub problem *)       *)
			(* 		(Int64.compare (Int64.abs arg1_v) (Int64.abs output_v)) < 0 *)
			(* 	) (BatList.combine arg0_sig output_sig)                       *)
			(* )                                                               *)
			(* nt_sigs                                                         *)
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
  			) nt_sigs
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
		if (BatList.length arg_sigs) = 0 then
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
  			) nt_sigs
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
		let arg0_sigs = 
		BatSet.filter (fun arg0_sig ->
			BatList.for_all (fun (arg0_const, output_const) ->
				let arg0_v = get_bv arg0_const in
				let output_v = get_bv output_const in
				(Int64.equal (Int64.neg arg0_v) output_v)
			) (BatList.combine arg0_sig output_sig)
		) nt_sigs
		in 
		arg0_sigs 
			(* if not (BatSet.is_empty arg0_sigs) then arg0_sigs        *)
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
		let arg0_sigs = 
  		BatSet.filter (fun arg0_sig ->
  			BatList.for_all (fun (arg0_const, output_const) ->
  				let arg0_v = get_bv arg0_const in
  				let output_v = get_bv output_const in
  				(Int64.equal (Int64.lognot arg0_v) output_v)
  			) (BatList.combine arg0_sig output_sig)
  		) nt_sigs
		in
		arg0_sigs
			(* if not (BatSet.is_empty arg0_sigs) then arg0_sigs      *)
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
		if (BatList.length arg_sigs) = 0 then
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
					(Int64.compare (Int64.div output_v arg0_v) (Int64.abs output_v)) < 0 (* |arg1| < |output| *)
					(* (check_ratio (Int64.div output_v arg0_v) output_v)  *)
				) (BatList.combine arg0_sig output_sig)
			) nt_sigs
		(* else                                                               *)
		(* 	let arg0_sig = List.nth arg_sigs 0 in                            *)
		(* 	BatSet.filter (fun arg1_sig ->                                   *)
		(* 		BatList.for_all2 (fun (arg0_const, arg1_const) output_const -> *)
		(* 			let arg0_v = get_bv arg0_const in                            *)
		(* 			let arg1_v = get_bv arg1_const in                            *)
		(* 			let output_v = get_bv output_const in                        *)
		(* 			(Int64.equal (Int64.mul arg0_v arg1_v) output_v)           *)
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
			) nt_sigs
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
  			) nt_sigs
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
		if (BatList.length arg_sigs) = 0 then nt_sigs
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
			) nt_sigs
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
		if (BatList.length arg_sigs) = 0 then
			BatSet.filter (fun arg0_sig ->
				BatList.for_all (fun (arg0_const, output_const)  ->
					let arg0_v = get_bv arg0_const in
					let output_v = get_bv output_const in
					(Int64.compare (Int64.abs output_v) (Int64.abs arg0_v)) <= 0 
				) (BatList.combine arg0_sig output_sig) 
			) nt_sigs
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
			) nt_sigs
	else if (String.compare op "bvurem") = 0 then
		if (BatList.length arg_sigs) = 0 then nt_sigs
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
			) nt_sigs
	else if (String.compare op "bvand") = 0 then
		if (BatList.length arg_sigs) = 0 then
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
			) nt_sigs
		else
			let arg0_sig = List.nth arg_sigs 0 in
			BatSet.filter (fun arg1_sig ->
				BatList.for_all2 (fun (arg0_const, arg1_const) output_const ->
					let arg0_v = get_bv arg0_const in
					let arg1_v = get_bv arg1_const in
					let output_v = get_bv output_const in
					Int64.equal (Int64.logand arg0_v arg1_v) output_v
				) (BatList.combine arg0_sig arg1_sig) output_sig
			) nt_sigs
	else if (String.compare op "bvor") = 0 then
		if (BatList.length arg_sigs) = 0 then
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
			) nt_sigs
		else
			let arg0_sig = List.nth arg_sigs 0 in
			BatSet.filter (fun arg1_sig ->
				BatList.for_all2 (fun (arg0_const, arg1_const) output_const ->
					let arg0_v = get_bv arg0_const in
					let arg1_v = get_bv arg1_const in
					let output_v = get_bv output_const in
					Int64.equal (Int64.logor arg0_v arg1_v) output_v
				) (BatList.combine arg0_sig arg1_sig) output_sig
			) nt_sigs
	else if (String.compare op "bvxor") = 0 then
		if (BatList.length arg_sigs) = 0 then 
			BatSet.filter (fun arg0_sig ->
				let arg1_sig = fun_apply_signature "bvxor" [arg0_sig; output_sig] in 
				BatSet.mem arg1_sig bv_sigs
			) nt_sigs
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
  			) nt_sigs
			in 
			arg1_sigs
			(* if not (BatSet.is_empty arg1_sigs) then arg1_sigs              *)
			(* else                                                           *)
			(* let arg0_sig = List.nth arg_sigs 0 in                          *)
			(* BatList.fold_left (fun acc (arg0_const, output_const) ->       *)
			(* 	let arg0_v = get_bv arg0_const in                            *)
			(* 	let output_v = get_bv output_const in                        *)
			(* 	acc @ [CBV (Int64.logxor arg0_v output_v)]                   *)
			(* ) [] (BatList.combine arg0_sig output_sig) |> BatSet.singleton *)
	else if (String.compare op "bvashr") = 0 then
		if (BatList.length arg_sigs) = 0 then 
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
					) (BatList.range 0 `To 63)
				) (BatList.combine arg0_sig output_sig)
			) nt_sigs
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
			) nt_sigs
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
		if (BatList.length arg_sigs) = 0 then 
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
						(Int64.equal output_v (Int64.shift_right_logical arg0_v i)) &&
						(Int64.compare (Int64.mul output_v arg0_v) Int64.zero) <> 0
					) (BatList.range 0 `To 63)
				) (BatList.combine arg0_sig output_sig)
			) nt_sigs
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
			) nt_sigs
			  
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
		if (BatList.length arg_sigs) = 0 then 
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
			
			BatSet.filter (fun arg0_sig ->
				BatList.for_all (fun (arg0_const, output_const) ->
					let arg0_v = get_bv arg0_const in
					let output_v = get_bv output_const in
					BatList.exists (fun i ->
						(Int64.equal output_v (Int64.shift_left arg0_v i)) &&
						(Int64.compare (Int64.mul output_v arg0_v) Int64.zero) <> 0
					) (BatList.range 0 `To 63)
				) (BatList.combine arg0_sig output_sig)
			) nt_sigs
			
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
			) nt_sigs
			
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
	else 
		failwith (Printf.sprintf "unsupported op: %s" op)