open Sexplib
open Vocab
open Exprs
open Z3
open BidirectionalUtils

let sexp_to_const sexp = 
	let str = Sexp.to_string sexp in 
	if (String.compare str "true") = 0 then (CBool (Concrete true))
	else if (String.compare str "false") = 0 then (CBool (Concrete false))
	else if (BatString.starts_with str "#x") then 
		(CBV (Int64.of_string ("0" ^ (BatString.lchop ~n:1 str))))
	else if (BatString.starts_with str "#u") then 
		(CBV (Int64.of_string ("0" ^ (BatString.lchop ~n:1 str))))		
	else if (str.[0] = '\"') then
		(* let _ = prerr_endline str in *)
		(CString (BatString.replace_chars (function '\"' -> "" | ';' -> "" | c -> BatString.make 1 c) str))
	else 
		try (CInt (int_of_string str)) with _ -> (CString str)
		
		
exception UnknownModel

(* oracle expr with a given function name and quantified variables  *)
let oracle_expr = ref (Const (CInt 0))
(* oracle expr only with sygus builtins and parameter variables  *)
let oracle_expr_resolved = ref (Const (CInt 0))
let forall_var_map : (string, Exprs.expr) BatMap.t ref =
	(* name -> Param int *) 
	ref BatMap.empty

(* spec for programming-by-example *)
type t = ((const list) * const) list  

let empty_spec = []

let add_io_spec (inputs, output) spec = 
	if (List.mem (inputs, output) spec) then spec 
	else 
		spec @ [(inputs, output)]
	(* ((inputs, output) :: spec)  *)

let string_of_io_spec spec = 
	string_of_list (fun (inputs, output) ->
		Printf.sprintf "i:%s -> o:%s"
		(string_of_list string_of_const inputs) 
		(string_of_const output) 
	) spec 

let abstract_bv_spec spec =
	let abstract_bv const =
		let bv = get_bv const in
		CBV (Int64.rem bv 1024L)    
	in  
	if (type_of_signature (fst (List.hd spec))) <> BV then spec 
	else 
		List.map (fun (inputs, output) ->
			(List.map abstract_bv inputs, abstract_bv output)  
		) spec  
		

let verify sol spec = 
	(* no oracle - pbe *)
	if (Pervasives.compare !oracle_expr (Const (CInt 0))) = 0 then None
	else
		let ctx = Z3.mk_context  [("model", "true"); ("proof", "false")] in
		let params = Exprs.get_params !oracle_expr_resolved in
		let params_str =
  		(BatSet.fold (fun param acc -> 
  			Printf.sprintf "%s\n(declare-const %s %s)" 
					acc 
  				(string_of_expr param) 
  				(string_of_type ~z3:true (type_of_expr param))
  		 ) params "") 
  	in   
		let str =
			(* (declare-const arg_i ) *)
			(* (assert (not (= oracle ...) (synth_fun ...)))  *)
			(* (assert (and (bvslt arg_0 #x00000000000000FF) (bvslt arg_1 #x00000000000000FF)))\n(assert (and (bvslt (bvneg arg_0) #x00000000000000FF) (bvslt (bvneg arg_1) #x00000000000000FF))) *)
			Printf.sprintf "%s\n(assert (not (= %s %s)))" 
				params_str 
				(Exprs.string_of_expr !oracle_expr_resolved)
				(Exprs.string_of_expr sol)  
		in
		my_prerr_endline str;
	  let exprSMT = Z3.SMT.parse_smtlib2_string ctx str [] [] [] [] in
		let sat = Z3.AST.ASTVector.to_expr_list exprSMT in
  	let solver = (Z3.Solver.mk_solver ctx None) in
  	(Z3.Solver.add solver sat) ;
    let q = (Z3.Solver.check solver []) in
    match q with
    | UNSATISFIABLE -> None
    | UNKNOWN -> raise UnknownModel
    | SATISFIABLE ->
			let m = (Z3.Solver.get_model solver) in
			(match m with
			| None -> assert false
			| Some m -> 
				(* let _ = prerr_endline (Z3.Model.to_string m) in  *)
				let decls = (Z3.Model.get_decls m) in
				let cex_input : Exprs.const list = 
					let m = 
    				List.fold_left (fun acc decl ->
    					let symbol = Z3.FuncDecl.get_name decl in
    					let value : Exprs.const = 
      					let exp_opt = Z3.Model.get_const_interp m decl in 
      					match exp_opt with 
      					| None -> raise UnknownModel
      					| Some expr ->
									sexp_to_const (Sexp.Atom (Z3.Expr.to_string expr))
    					in
  						(* let _ = prerr_endline (Printf.sprintf "%s -> %s" (Z3.Symbol.to_string symbol) (string_of_bool value)) in  *)
    					BatMap.add (Z3.Symbol.to_string symbol) value acc
    				) BatMap.empty decls 
					in 
					let param_ids = 
						List.map 
							(fun i -> Exprs.string_of_expr (Exprs.Param (i, Bool))) 
							(BatList.range 0 `To ((BatMap.cardinal m) - 1))
					in   
					List.map (fun x -> try BatMap.find x m with _ -> assert false) param_ids 
				in
				let sol_output = 
					Exprs.compute_signature [(cex_input, CInt 0)] sol
					|> List.hd
				in
				let cex_output = 
					Exprs.compute_signature [(cex_input, CInt 0)] !oracle_expr_resolved
					|> List.hd
				in
				my_prerr_endline (Printf.sprintf "sol:%s   oracle:%s" (string_of_const sol_output) (string_of_const cex_output));
				my_prerr_endline (Printf.sprintf "cex : %s" (string_of_io_spec [(cex_input, cex_output)]));
				let _ = assert ((Pervasives.compare sol_output cex_output) <> 0) in
				Some (cex_input, cex_output)
			)
		 
let add_trivial_examples grammar spec =
	let _ = assert (Exprs.is_function_expr !oracle_expr) in
	let _ = assert (Exprs.is_function_expr !oracle_expr_resolved) in 
	let trivial_sol = 
		Exprs.Const (Exprs.get_trivial_value (Grammar.type_of_nt Grammar.start_nt))
		(* List.find (fun (nt, r) ->                                                 *)
		(* 	(Grammar.NTNode.equal Grammar.start_nt nt) && (Grammar.is_param_rule r) *)
		(* ) (Grammar.get_nt_rule_list grammar) |> snd |> Grammar.expr_of_rewrite    *)
	in
	match (verify trivial_sol spec) with 
	| None -> raise (Generator.SolutionFound trivial_sol)  
	| Some cex -> 
		let _ = assert (not (List.mem cex spec)) in  
		(cex :: spec)
	(* let inputs =                                                                     *)
	(* 	let children = get_children !oracle_expr in                                    *)
	(* 	List.map (fun e -> Exprs.get_trivial_value (Exprs.type_of_expr e)) children    *)
	(* in                                                                               *)
	(* let output =                                                                     *)
	(* 	Exprs.compute_signature [(inputs, CInt 0)] !oracle_expr_resolved               *)
	(* in                                                                               *)
	(* ((inputs, List.hd output) :: spec) *)

		 
