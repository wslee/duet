open Sexplib
open Exprs
open Grammar 
open Vocab

(* input : file name *)
(* output : 6-tuple
  macro_instantiator    : BatMap [String -> Expr]
  -> user function
  target_function_name  : String
  -> target function name
  args_map              : BatMap [String -> expr.Param(int, exprtype)]
  -> function argument
  grammar               : BatMap [NTRewrite -> BatSet[Rewrite]]
  ->  production rule
  forall_var_map        : BatMap [String -> expr.Var(String, exprtype)] (reference)
  ->  user variable
  spec                  : Specification
  ->  constraint
  (Grammer.nt_type_map : BatMap [NTRewirte -> exprtype])
*)
let parse file =
  Random.self_init(); 
	let lines = read_lines file in
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
	let _ = Unix.unlink file'
;;