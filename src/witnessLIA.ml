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
	let theta = 2.0 ** ((-1. *. (log (float_of_int (abs given_desired)) /. log 2.)) /. (float_of_int available_height)) in
	(float_of_int (abs new_desired)) < theta *. (float_of_int (abs given_desired))


(** LIA theory **)
let witness available_height nt_sigs (int_sigs, bv_sigs, string_sigs, bool_sigs) rule output_sig arg_sigs =
	let op = Grammar.op_of_rule rule in
	if (String.compare op "<") = 0 then
		let _ = assert ((type_of_signature output_sig) = Bool) in
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
		let _ = assert ((type_of_signature output_sig) = Bool) in
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
		let _ = assert ((type_of_signature output_sig) = Bool) in
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
	else if (String.compare op ">=") = 0 then
		let _ = assert ((type_of_signature output_sig) = Bool) in
		if (BatList.length arg_sigs) = 0 then nt_sigs
		else 
			let arg0_sig = List.nth arg_sigs 0 in
			BatSet.filter (fun arg1_sig ->
				BatList.for_all2 (fun (arg0_const, arg1_const) output_const ->
					(is_abstract_bool output_const) || (* for learn_ite *)
					(let output_v = get_concrete_bool output_const in
					 ((Pervasives.compare arg0_const arg1_const) >= 0) = output_v)   
				) (BatList.combine arg0_sig arg1_sig) output_sig 
			) nt_sigs
	else if (String.compare op "+") = 0 then
		let _ = assert ((type_of_signature output_sig) = Int) in
		if (BatList.length arg_sigs) = 0 then
			BatSet.filter (fun arg0_sig ->
				BatList.for_all (fun (arg0_const, output_const) -> 
					let arg0_v = get_int arg0_const in
					let output_v = get_int output_const in
					let arg1_v = output_v - arg0_v in 
					check_ratio available_height output_v arg1_v
					(* (abs arg1_v) < (abs output_v) *)
				) (BatList.combine arg0_sig output_sig) 
			) nt_sigs
		else 
			let arg0_sig = List.nth arg_sigs 0 in
			BatList.fold_left (fun acc (arg0_const, output_const) ->
				let arg0_v = get_int arg0_const in 
				let output_v = get_int output_const in
				acc @ [(CInt (output_v - arg0_v))]       	 
			) [] (BatList.combine arg0_sig output_sig) |> BatSet.singleton
	else if (String.compare op "-") = 0 then
		let _ = assert ((type_of_signature output_sig) = Int) in
		if (BatList.length arg_sigs) = 0 then 
			BatSet.filter (fun arg0_sig ->
				BatList.for_all (fun (arg0_const, output_const) ->
					let arg0_v = get_int arg0_const in
					let output_v = get_int output_const in
					let arg1_v = arg0_v - output_v in
					check_ratio available_height output_v arg1_v
					(* (abs arg1_v) < (abs output_v) *)
					(* (arg0_v > output_v) *)
				) (BatList.combine arg0_sig output_sig) 
			) nt_sigs
		else 
			let arg0_sig = List.nth arg_sigs 0 in
			BatList.fold_left (fun acc (arg0_const, output_const) ->
				let arg0_v = get_int arg0_const in 
				let output_v = get_int output_const in
				acc @ [(CInt (arg0_v - output_v))]        	 
			) [] (BatList.combine arg0_sig output_sig) |> BatSet.singleton
	else if (String.compare op "*") = 0 then
		let _ = assert ((type_of_signature output_sig) = Int) in
		if (BatList.length arg_sigs) = 0 then
			BatSet.filter (fun arg0_sig ->
				BatList.for_all (fun (arg0_const, output_const) ->
					let arg0_v = get_int arg0_const in
					let output_v = get_int output_const in 
					(* arg0 * arg1 = output *)
					(* to prevent from generating the same sub problem *)
					((abs arg0_v) > 1) && (output_v <> 0) &&  (* ... * 0 = 0 *)
					(output_v mod arg0_v = 0) &&  (* output | arg0 *)
					((abs arg0_v) < (abs output_v)) && (* |arg0| < |output| *)
					((output_v / arg0_v) < (abs output_v)) (* |arg1| < |output| *)
				) (BatList.combine arg0_sig output_sig)
			) nt_sigs
		else
			let arg0_sig = List.nth arg_sigs 0 in
			BatList.fold_left (fun acc (arg0_const, output_const) ->
				let arg0_v = get_int arg0_const in
				let output_v = get_int output_const in
				let _ = assert (arg0_v <> 0) in
				let arg1_v = output_v / arg0_v in
				acc @ [(CInt arg1_v)]
			) [] (BatList.combine arg0_sig output_sig) |> BatSet.singleton
	else if (String.compare op "/") = 0 then
		let _ = assert ((type_of_signature output_sig) = Int) in
		if (BatList.length arg_sigs) = 0 then
			(* a / b = c    a = bc + k  (k < b)    (a - k) / c = b   가능한 b가 너무 많음. *)
			(* 현재 i번째 예제를 다루고 있다고 하면, i번째 bv값을 모두 뒤져서 a / b = c 가 되는 b가 있는지 확인. *)
			(* arg0 / arg1 = output  <=> arg0 = arg1 * output + k (|k| < |arg1|)*)
			(* arg1에 대한 조건 추출후, 그 조건을 만족하는 arg1 찾기를 |C| 보다 더 빨리하는 방법? *)
			(* k = arg0 - arg1 * output *)
			BatSet.filter (fun arg0_sig ->
				BatList.for_all (fun (arg0_const, output_const) ->
					let arg0_v = get_int arg0_const in
					let output_v = get_int output_const in
					(* arg0_v / arg1_v = output_v *)
					(* output_v = arg1_v * arg0_v + k, |k| < |arg1_v| *)
					(abs output_v) <= (abs arg0_v)
				) (BatList.combine arg0_sig output_sig)
			) nt_sigs
		else 
			let arg0_sig = List.nth arg_sigs 0 in
			let arg1_sig = 
  			BatSet.filter (fun arg1_sig ->
  				BatList.for_all2 (fun (arg0_const, arg1_const) output_const ->
  					let arg0_v = get_int arg0_const in
  					let arg1_v = get_int arg0_const in
  					let output_v = get_int output_const in
  					(arg1_v <> 0) && 
  					((arg0_v / arg1_v) = output_v)
  				) (BatList.combine arg0_sig arg1_sig) output_sig
  			) nt_sigs
			in 
			arg1_sig
	else if (String.compare op "%") = 0 then
		let _ = assert ((type_of_signature output_sig) = Int) in
		if (BatList.length arg_sigs) = 0 then
			BatSet.filter (fun arg0_sig ->
				BatList.for_all (fun (arg0_const, output_const)  ->
					let arg0_v = get_int arg0_const in
					let output_v = get_int output_const in
					(abs output_v) <= (abs arg0_v) 
				) (BatList.combine arg0_sig output_sig) 
			) nt_sigs
		else 
			let arg0_sig = List.nth arg_sigs 0 in
			BatSet.filter (fun arg1_sig ->
				BatList.for_all2 (fun (arg0_const, arg1_const) output_const ->
					let arg0_v = get_int arg0_const in
					let arg1_v = get_int arg1_const in
					let output_v = get_int output_const in
					(arg1_v <> 0) &&
					((arg0_v mod arg1_v) = output_v)
				) (BatList.combine arg0_sig arg1_sig) output_sig
			) nt_sigs
	else 
		failwith (Printf.sprintf "unsupported op: %s" op)