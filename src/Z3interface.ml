open Sexplib
open Vocab
open Exprs

let z3_solver_path = "z3"
let temp_smt_file = "tmp.smt"
let temp_result_file = "tmp.out"

let rec string_of_sexp sexp = 
	match sexp with
	| Sexp.List sexps -> "["^ (string_of_sexps sexps) ^ "]"
	| Sexp.Atom s -> (*"A:" ^ s*) (Sexp.to_string sexp)
and string_of_sexps sexps = 
	(BatList.fold_left (fun acc sexp -> acc ^ " " ^ (string_of_sexp sexp)) "" sexps)

let int_of_sexp sexp = 
	match sexp with 
	| Sexp.List sexps -> (* e.g., (- 1) -> List [Atom "-"; Atom "1"] *)
		let str = 
			BatList.fold_left (fun acc sexp -> acc ^ (string_of_sexp sexp)) "" sexps
		in
		(try Some (int_of_string str) with _ -> None)    
	| Sexp.Atom s -> try Some (int_of_string s) with _ -> None 
	
let filter_sexps_for tag sexps = 
	BatList.fold_left (fun acc sexp ->
		match sexp with 
		| Sexp.List sexps' -> 
			if (BatList.length sexps') > 0 && 
				 (BatString.equal (Sexp.to_string (BatList.hd sexps')) tag) then 
				 acc @ [(BatList.remove_at 0 sexps')] 
			else acc 
		| _ -> acc  
	) [] sexps
	
let sexp_to_const sexp = 
	match int_of_sexp sexp with 
	| Some n -> CInt n
	| None -> 
  	let str = Sexp.to_string sexp in 
  	if (BatString.equal str "true") then CBool (Concrete true)
  	else if (BatString.equal str "false") then CBool (Concrete false)
  	else if (BatString.starts_with str "#x") then
  		CBV (Int64.of_string ("0" ^ (BatString.lchop ~n:1 str)))
  	else if (BatString.starts_with str "#u") then 
  		CBV (Int64.of_string ("0" ^ (BatString.lchop ~n:1 str)))		
  	else if (str.[0] = '\"') then
  		CString (BatString.replace_chars (function '\"' -> "" | ';' -> "" | c -> BatString.make 1 c) str)
  	else
			failwith (Printf.sprintf "error : sexp_to_const: %s\n" str)
		
(* 
sat
(model 
  (define-fun num () (_ BitVec 64)
    #x083126ea6f1a0223)
  (define-fun den () (_ BitVec 64)
    #xffffffffffff8000)
)
*)		
let readSMTResult file =
	Random.self_init(); 
	let lines = read_lines file in
	assert (not (BatList.is_empty lines));
	if (BatString.equal "unsat" (BatList.hd lines)) then None    
	else 
		let lines = BatList.tl lines in 
  	let file' = file ^ "_" ^ (string_of_int (Random.int 1000)) in
  	let lines = 
  		BatList.map (fun line -> 
  			BatString.fold_left (fun (opened, acc) c ->
  				if (c = '\"') then
  					if not opened then 
  						(true, acc ^ (BatString.of_char c) ^ ";")
  					else  
  						(false, acc ^ (BatString.of_char c))
  				else 
  					(opened, acc ^ (BatString.of_char c))
  			) (false, "") line |> snd 
  		) lines 
  	in  
  	let _ = write_lines lines file' in  
  	let sexps = Sexp.load_sexps file' in
  	let _ = Unix.unlink file' in
		try
			(* [ *)
			(*   [ *)
			(*     [ define-fun arg_1 [] [ _ BitVec 64] #x8000000000000000] *)
			(*     [ define-fun arg_0 [] [ _ BitVec 64] #x8000000000000000]*)
			(*   ] *)
			(* ] *)
			(* let _ = prerr_endline (string_of_sexp (Sexp.List sexps)) in  *)
  		let sexps =
				match (BatList.hd sexps) with 
				| Sexp.List lst -> lst 
				| _ -> assert false 
			in
			(* let _ = prerr_endline (string_of_sexp (Sexp.List sexps)) in *)
  		let maps = filter_sexps_for "define-fun" sexps in 
  		Some 
    		(BatList.fold_left  
    			(fun acc map ->
  					let lv_str = string_of_sexp (BatList.nth map 0) in 
  					let const = sexp_to_const (BatList.nth map 3) in
						BatMap.add lv_str const acc  
  				) BatMap.empty maps 
    		)
		with _ ->
			let err_id = Random.int 65532 in 
			let err_filename = Printf.sprintf "err_%d_%s" err_id temp_smt_file in 
			let _ = Sys.rename temp_smt_file err_filename in
			failwith (Printf.sprintf "WARNING: Errors in the SMT formula! (see %s)\n" err_filename) 
				
let solve smt_str =
	let _ = write_lines [smt_str] temp_smt_file in 
  let result = Sys.command (z3_solver_path ^ " -smt2 " ^ temp_smt_file ^
                       "  > " ^ temp_result_file ) in
  if (result = 127) then 
		failwith "Failed to run Z3. Check out if Z3 is on the working path."
	else 	 
		readSMTResult temp_result_file
