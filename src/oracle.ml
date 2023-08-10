open Sexplib
open Vocab
open Exprs
open Z3


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
          let name = Z3.Model.to_string (Z3.FuncDecl.get_name decl) in
          let interp_opt = Z3.Model.get_const_interp model decl in
          match interp_opt with
          | None -> assert false
          | Some interp -> 
            BatMap.add name interp acc (* name_symbol -> arg_0 | interp -> false *)
        ) decls BatMap.empty in
        let cex_input = BatList.map (fun param ->
          let name = string_of_expr param in
          let expr = BatMap.find name name2expr in (* how is it possible? -> exprSMT got string-of-expr *)
          sexp_to_const (Sexp.Atom (Z3.Expr.to_string expr))
        ) params in
        let cex_output = BatList.hd (compute_signature [(cex_input, CInt 0)] !oracle_expr_resolved) in
        Some (cex_input, cex_output)
;;