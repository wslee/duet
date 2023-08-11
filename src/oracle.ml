open Sexplib
open Vocab
open Exprs
open Z3

let sexp_to_const sexp = 
	let str = Sexp.to_string sexp in 
	if (String.compare str "true") = 0 then Const (CBool (Concrete true))
	else if (String.compare str "false") = 0 then Const (CBool (Concrete false))
	else if (BatString.starts_with str "#x") then 
		Const (CBV (Int64.of_string ("0" ^ (BatString.lchop ~n:1 str))))
	else if (BatString.starts_with str "#u") then 
		Const (CBV (Int64.of_string ("0" ^ (BatString.lchop ~n:1 str))))		
	else if (str.[0] = '\"') then
		(* let _ = prerr_endline str in *)
		Const (CString (BatString.replace_chars (function '\"' -> "" | ';' -> "" | c -> BatString.make 1 c) str))
	else 
		try Const (CInt (int_of_string str)) with _ -> Const (CString str)
;;

let oracle_expr = ref (Const (CInt 0)) (* name of oracle function -> (f arg0 arg1 ... argN) *) 
let oracle_expr_resolved = ref (Const (CInt 0)) (* body of oracle function -> ex. (+ arg0 arg1) *)

let verify (sol : Exprs.expr) (spec : Specification.t) : ((Exprs.const list * Exprs.const) option) = 
  (* returns None if there is no counter-examples *)
  if !oracle_expr = (Const (CInt 0)) then None
  else
    let ctx = Z3.mk_context  [("model", "true"); ("proof", "false")] in (* model : true -> make counter-example *)
		let params = Exprs.get_params !oracle_expr_resolved in
		let params_str =
  		(BatSet.fold (fun param acc -> 
  			Printf.sprintf "%s\n(declare-const %s %s)" acc (string_of_expr param) (string_of_type ~z3:true (type_of_expr param))
  		) params "") 
  	in  
    let str = 
      Printf.sprintf "%s\n(assert (not (= %s %s)))" 
				params_str (Exprs.string_of_expr !oracle_expr_resolved) (Exprs.string_of_expr sol)
		in
    let exprSMT = Z3.SMT.parse_smtlib2_string ctx str [] [] [] [] in (* Z3.AST.ASTVector.ast_vector *)
		let sat = Z3.AST.ASTVector.to_expr_list exprSMT in (* Z3.Expr.expr list *)
  	let solver = (Z3.Solver.mk_solver ctx None) in (* Z3.Solver.solver *)
  	(Z3.Solver.add solver sat);
    let q = (Z3.Solver.check solver []) in (* ZMT.Solver.status *)
    match q with
    | UNSATISFIABLE -> None
    | UNKNOWN -> assert false
    | SATISFIABLE -> 
      let model_opt = Z3.Solver.get_model solver in
      match model_opt with
      | None -> assert false
      | Some model ->
        (* ex. (define-fun arg_0 () Bool false) (define-fun arg_2 () Bool true) (define-fun arg_1 () Bool false) *)
        let decls = Z3.Model.get_decls model in (* vs. get_func_decls - only function delcarations *)
        let name2expr = BatList.fold_right (fun decl acc -> 
          let name = Z3.Symbol.to_string (Z3.FuncDecl.get_name decl) in
          let interp_opt = Z3.Model.get_const_interp model decl in
          match interp_opt with
          | None -> assert false
          | Some interp -> 
            BatMap.add name interp acc (* name_symbol -> arg_0 | interp -> false *)
        ) decls BatMap.empty in
        let cex_input = BatList.map (fun param ->
          let name = string_of_expr param in
          let expr = BatMap.find name name2expr in (* how is it possible? -> exprSMT got string-of-expr *)
          let const_expr = sexp_to_const (Sexp.Atom (Z3.Expr.to_string expr)) in
          match const_expr with
          | Const c -> c
          | _ -> assert false
        ) (BatSet.to_list params) in
        let cex_output = BatList.hd (compute_signature [(cex_input, CInt 0)] !oracle_expr_resolved) in
        Some (cex_input, cex_output)
;;

let init grammar spec =
  let nts = BatMap.foldi (fun nt rules arr -> (nt::arr)) grammar [] in
  let start_nt = BatList.hd nts in
  let trivial_sol = Const (get_trivial_value (BatMap.find start_nt !Grammar.nt_type_map)) in
  let cex = verify trivial_sol spec in
  match cex with
  | None -> spec
  | Some s -> (s::spec)
;;