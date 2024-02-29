open Sexplib
open Exprs
open Grammar 
open Vocab

(* Sexp.t =   *)
(* |	Sexp.Atom of string  *)
(* |	Sexp.List of t list  *)

let rec string_of_sexp sexp = 
	match sexp with
	| Sexp.List sexps -> "L["^(BatList.fold_left (fun acc sexp -> acc ^ " " ^ (string_of_sexp sexp)) "" sexps) ^ "]"
	| Sexp.Atom s -> "A:" ^ (*s*) (Sexp.to_string sexp)


(* return: (Sexp.t list) set (without the first atom) *)
let filter_sexps_for tag sexps = 
	BatList.fold_left (fun acc sexp ->
		match sexp with 
		| Sexp.List sexps' -> 
			if (BatList.length sexps') > 0 && 
				 (String.compare (Sexp.to_string (BatList.hd sexps')) tag) = 0 then 
				 (* BatSet.add (BatList.remove_at 0 sexps')  acc *)
				 acc @ [(BatList.remove_at 0 sexps')] 
			else acc 
		| _ -> acc  
	) [] (*BatSet.empty*) sexps

let sexp_to_type sexp = 
	match sexp with 
	| Sexp.List _ (* BitVec [bit-width] *) -> BV 
	| Sexp.Atom s -> 
		if (String.compare s "Int") = 0 then Int
		else if (String.compare s "String") = 0 then String
		else if (String.compare s "Bool") = 0 then Bool
		else failwith ("Unknown type: " ^ s) 

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
	
let rec sexp_to_expr sexp args_map = 
	match sexp with 
	| Sexp.List sexps' ->
		let _ = assert ((BatList.length sexps') >= 1) in  
		let op = Sexp.to_string (BatList.nth sexps' 0) in
		let sexps' = (BatList.remove_at 0 sexps') in 
		let children = 
			BatList.map (fun sexp' -> sexp_to_expr sexp' args_map) sexps'
		in  
		let expr_ty = 
			try Grammar.ret_type_of_op (Grammar.FuncRewrite (op, []))
			(* TODO : macro *)
			with _ -> type_of_nt (Grammar.start_nt) (* maybe target-function *)
		in 
		Function (op, children, expr_ty)
	| Sexp.Atom s ->
		let id = (Sexp.to_string sexp) in 
		if (BatMap.mem id args_map) then 
			BatMap.find id args_map 
		else sexp_to_const sexp 

let rec sexp_to_rule nts sexp args_map = 
	match sexp with 
	| Sexp.List sexps' ->
		let _ = assert ((BatList.length sexps') >= 1) in  
		let op = Sexp.to_string (BatList.nth sexps' 0) in
		let sexps' = (BatList.remove_at 0 sexps') in 
		let children = 
			BatList.map (fun sexp' -> sexp_to_rule nts sexp' args_map) sexps'
		in  
		FuncRewrite (op, children)
	| Sexp.Atom s ->
		let id = (Sexp.to_string sexp) in
		if (BatSet.mem (NTRewrite id) nts) then NTRewrite id
		else if (BatMap.mem id args_map) then ExprRewrite (BatMap.find id args_map) 
		else ExprRewrite (sexp_to_const sexp)
											 
(* id -> Exprs.Param *)
let get_args_map args_data = 
	let args_map =
		let name_ty_list = 
			match args_data with 
			| Sexp.List sexps -> (* args *)
				BatList.fold_left (fun acc sexp ->
					match sexp with 
					| Sexp.List args -> (* one arg = [name, type] *)
						let _ = assert ((BatList.length args) = 2) in 
    				let (param_name, param_ty) =
    					(Sexp.to_string (BatList.nth args 0), sexp_to_type (BatList.nth args 1))
    				in
    				acc @ [(param_name, param_ty)]
					| _ -> assert false  
				) [] sexps   
			| _ -> assert false 
		in
		let i_name_ty_list =
			BatList.combine 
				(BatList.range 0 `To ((BatList.length name_ty_list) - 1))
				name_ty_list 
		in  
		BatList.fold_left (fun m (i, (param_name, param_ty)) -> 
			BatMap.add param_name (Param(i, param_ty)) m 
		) BatMap.empty i_name_ty_list    
	in 	
	args_map

(* (define-fun ehad ((x (BitVec 64))) (BitVec 64) (bvlshr x #x0000000000000001)) *)
(* L[ A:define-fun A:ehad *)
(* 	 L[ *)
(* 			L[ A:x L[ A:BitVec A:64]]*)
(* 		] *)
(* 	 L[ A:BitVec A:64] *)
(* 	 L[ A:bvlshr A:x A:#x0000000000000001]  *)
(*  ] *)

(* return: (string, Exprs.expr (with Param)) BatMap.t *)
(* TODO: in case where other definitions used in a definition *)
let process_definitions defs_data =
	BatList.fold_left (fun m def_data -> 
  	let _ = assert ((BatList.length def_data) = 4) in  
  	let (name_data, args_data, ret_type_data, body_data) = 
  		(BatList.nth def_data 0, BatList.nth def_data 1, 
  		 BatList.nth def_data 2, BatList.nth def_data 3)
  	in
		let name = Sexp.to_string name_data in 
		let ret_type = sexp_to_type ret_type_data in 
		let args_map = get_args_map args_data in 
		let expr = sexp_to_expr body_data args_map in
		let _ = 
			if (!Options.get_size) then 
			begin
				let size = (Exprs.size_of_expr expr) in 
				prerr_endline (Printf.sprintf "%d" size);
				exit size
			end
		in
		(* prerr_endline (Printf.sprintf "%s -> %s" name (Exprs.string_of_expr expr));  *)
		BatMap.add name expr m     
	) BatMap.empty defs_data  	
	
(* (synth-fun SC ((s (BitVec 4)) (t (BitVec 4))) Bool                                                                                                                                                                           *)
(*     ((Start Bool (true false (not Start) (and Start Start) (or Start Start) *)
(* 		 (= StartBv StartBv) (bvult StartBv StartBv) (bvslt StartBv StartBv) *)
(* 		 (bvuge StartBv StartBv) (bvsge StartBv StartBv)))                            *)
(*     (StartBv (BitVec 4) (s t #x0 #x8 #x7 (bvneg StartBv) (bvnot StartBv) *)
(* 		 (bvadd StartBv StartBv) (bvsub StartBv StartBv) (bvand StartBv StartBv) *)
(* 		 (bvlshr StartBv StartBv) (bvor StartBv StartBv) (bvshl StartBv StartBv))))) *)
	
(* L[ A:synth-fun A:SC *)
(* 	L[ L[ A:s L[ A:BitVec A:4]] L[ A:t L[ A:BitVec A:4]]] A:Bool *)

(* 	L[ L[ A:Start A:Bool *)
(* 				L[ A:true A:false L[ A:not A:Start] L[ A:and A:Start A:Start] *)
(* 				  L[ A:or A:Start A:Start] L[ A:= A:StartBv A:StartBv] *)
(* 				  L[ A:bvult A:StartBv A:StartBv] *)
(* 				  L[ A:bvslt A:StartBv A:StartBv] *)
(* 				  L[ A:bvuge A:StartBv A:StartBv] *)
(* 				  L[ A:bvsge A:StartBv A:StartBv]*)
(*         ]*)
(* 			] *)
(* 		 L[ A:StartBv L[ A:BitVec A:4] *)
(* 				L[ A:s A:t A:#x0 A:#x8 A:#x7 *)
(* 			 	  L[ A:bvneg A:StartBv] *)
(* 		 		  L[ A:bvnot A:StartBv] *)
(* 				  L[ A:bvadd A:StartBv A:StartBv] *)
(* 				  L[ A:bvsub A:StartBv A:StartBv] *)
(* 				  L[ A:bvand A:StartBv A:StartBv] *)
(* 				  L[ A:bvlshr A:StartBv A:StartBv] *)
(* 				  L[ A:bvor A:StartBv A:StartBv] *)
(* 				  L[ A:bvshl A:StartBv A:StartBv]*)
(*         ]*)
(*  		] *)
(* 	 ]*)
(* 	] *)
let process_grammar args_map ret_type grammar_data =
	(* nt_rule_data: [Non-terminal, type, production_rules ] *)
	let get_nts acc nt_rule_data =
		let nt_rule_data = match nt_rule_data with Sexp.List nt_rule_data -> nt_rule_data | _ -> assert false in   
		let _ = assert ((BatList.length nt_rule_data) = 3) in  
  	let nt_data = BatList.nth nt_rule_data 0 in
		let nt = NTRewrite (Sexp.to_string nt_data) in
		BatSet.add nt acc 	 
	in 
	let process_rules nts grammar nt_rule_data = 
		let nt_rule_data = match nt_rule_data with Sexp.List nt_rule_data -> nt_rule_data | _ -> assert false in   
		let _ = assert ((BatList.length nt_rule_data) = 3) in  
  	let (nt_data, nt_type_data, rules_data) = 
  		(BatList.nth nt_rule_data 0, BatList.nth nt_rule_data 1, 
  		 BatList.nth nt_rule_data 2)
  	in
		let nt = NTRewrite (Sexp.to_string nt_data) in
		let nt_type = sexp_to_type nt_type_data in
		let _ = Grammar.nt_type_map := BatMap.add nt nt_type !Grammar.nt_type_map in  
		match rules_data with 
		| Sexp.List prod_rules_data ->
		 	BatList.fold_left (fun grammar prod_rule_data -> 
				let rule = sexp_to_rule nts prod_rule_data args_map in
				add_rule nt rule grammar 		 
			) grammar prod_rules_data
		| _ -> assert false
	in  
	match grammar_data with 
	| Sexp.List nt_rules_data ->
		let nts = BatList.fold_left get_nts BatSet.empty nt_rules_data in  
		BatList.fold_left (process_rules nts) empty_grammar nt_rules_data   
	| _ -> assert false  
	
let process_synth_funcs synth_fun_data =
	let _ = assert ((BatList.length synth_fun_data) = 4) in  
	let (name_data, args_data, ret_type_data, grammar_data) = 
		(BatList.nth synth_fun_data 0, BatList.nth synth_fun_data 1, 
		 BatList.nth synth_fun_data 2, BatList.nth synth_fun_data 3)
	in
	let name = Sexp.to_string name_data in
	let args_map = get_args_map args_data in  
	let ret_type = sexp_to_type ret_type_data in
	let grammar = process_grammar args_map ret_type grammar_data in 
	(name, args_map, grammar) 

let process_synth_invs synth_inv_data =
	let _ = assert ((BatList.length synth_inv_data) = 4 || (BatList.length synth_inv_data) = 3 || (BatList.length synth_inv_data) = 2) in  
	let (name_data, args_data, ret_type_data) = 
		(BatList.nth synth_inv_data 0, BatList.nth synth_inv_data 1, 
		 try BatList.nth synth_inv_data 2 with _ -> Sexp.Atom "Bool")
	in
	let args_map = get_args_map args_data in  
	let grammar_data =
		try BatList.nth synth_inv_data 3
		with _ ->
			Sexp.List [
				Sexp.List [
					Sexp.Atom "Start";
					Sexp.Atom "Bool"; 
					Sexp.List (BatMap.foldi (fun id param acc ->
						match param with
						| Param(i, ty) -> 
							if ty = Bool then 
								acc @ [Sexp.Atom id]
							else acc
						| _ -> assert false
					)	args_map [
						Sexp.Atom "true";
						Sexp.Atom "false";
						Sexp.List [Sexp.Atom "ite"; Sexp.Atom "Start"; Sexp.Atom "Start"; Sexp.Atom "Start"];
						Sexp.List [Sexp.Atom "not"; Sexp.Atom "Start"];
						Sexp.List [Sexp.Atom "and"; Sexp.Atom "Start"; Sexp.Atom "Start"];
						Sexp.List [Sexp.Atom "or"; Sexp.Atom "Start"; Sexp.Atom "Start"];
						Sexp.List [Sexp.Atom "="; Sexp.Atom "Start"; Sexp.Atom "Start"];
						Sexp.List [Sexp.Atom "<"; Sexp.Atom "StartInt"; Sexp.Atom "StartInt"];
						Sexp.List [Sexp.Atom "<="; Sexp.Atom "StartInt"; Sexp.Atom "StartInt"];
						Sexp.List [Sexp.Atom ">"; Sexp.Atom "StartInt"; Sexp.Atom "StartInt"];
						Sexp.List [Sexp.Atom ">="; Sexp.Atom "StartInt"; Sexp.Atom "StartInt"];
						Sexp.List [Sexp.Atom "="; Sexp.Atom "StartInt"; Sexp.Atom "StartInt"];
					])
				];
				Sexp.List [
					Sexp.Atom "StartInt";
					Sexp.Atom "Int";
					Sexp.List (BatMap.foldi (fun id param acc ->
						match param with
						| Param(i, ty) -> 
							if ty = Int then 
								acc @ [Sexp.Atom id]
							else acc
						| _ -> assert false
					)	args_map [
						Sexp.Atom "0";
						Sexp.Atom "1";
						Sexp.Atom "2";
						Sexp.Atom "3";
						Sexp.Atom "4";
						Sexp.Atom "5";
						Sexp.Atom "6";
						Sexp.Atom "7";
						Sexp.Atom "8";
						Sexp.Atom "9";
						Sexp.List [Sexp.Atom "ite"; Sexp.Atom "Start"; Sexp.Atom "StartInt"; Sexp.Atom "StartInt"];
						Sexp.List [Sexp.Atom "+"; Sexp.Atom "StartInt"; Sexp.Atom "StartInt"];
						Sexp.List [Sexp.Atom "-"; Sexp.Atom "StartInt"; Sexp.Atom "StartInt"];
						Sexp.List [Sexp.Atom "*"; Sexp.Atom "StartInt"; Sexp.Atom "StartInt"];
						Sexp.List [Sexp.Atom "/"; Sexp.Atom "StartInt"; Sexp.Atom "StartInt"];
						Sexp.List [Sexp.Atom "mod"; Sexp.Atom "StartInt"; Sexp.Atom "StartInt"];
					])
				]
			] 
		in
	let name = Sexp.to_string name_data in 
	let ret_type = sexp_to_type ret_type_data in
	let grammar = process_grammar args_map ret_type grammar_data 
	in
	(name, args_map, grammar) 

(* (declare-var x (BitVec 64)) *)
(* L[ A:declare-var L[ A:x L[ A:BitVec A:64]]] *)

(* return: name -> Var expr *)
let process_forall_vars forall_vars_data =
	BatList.fold_left (fun m forall_var_data ->
		let _ = assert ((BatList.length forall_var_data) = 2) in  
  	let (name_data, type_data) = 
  		(BatList.nth forall_var_data 0, BatList.nth forall_var_data 1)
  	in
		let name = Sexp.to_string name_data in
		let ty = sexp_to_type type_data in
		(* set up the domain. the range will be determined later *) 
		BatMap.add name (Var(name, ty)) m 
	) BatMap.empty forall_vars_data    

let process_primed_vars forall_vars_data =
	BatList.fold_left (fun m forall_var_data ->
		let _ = assert ((BatList.length forall_var_data) = 2) in  
  	let (name_data, type_data) = 
  		(BatList.nth forall_var_data 0, BatList.nth forall_var_data 1)
  	in
		let name = Sexp.to_string name_data in
		let ty = sexp_to_type type_data in
		(* set up the domain. the range will be determined later *) 
		let m = BatMap.add name (Var(name, ty)) m in
		BatMap.add (name ^ "!") (Var(name ^ "!", ty)) m 
	) BatMap.empty forall_vars_data    

(* (constraint (= (hd01 x) (f x))) *)
(* [L[ A:= L[ A:hd20 A:x] L[ A:f A:x]]] *)
(* (constraint (= (f #xeed40423e830e30d) #x8895fdee0be78e79)) *)
(* [L[ A:= L[ A:f A:#xeed40423e830e30d] A:#x8895fdee0be78e79]] *) 
(* return: spec as Exprs.expr *)
let process_constraints grammar target_function_name constraints_data macro_instantiator id2var =
	BatList.fold_left (fun spec constraint_data ->
		let constraint_data = try BatList.hd constraint_data with _ -> assert false in
		(* forall_var_map : variable name -> Var(name, ty) *) 
		let exp = sexp_to_expr constraint_data id2var in
		(* let _ = prerr_endline (string_of_expr exp) in *)
		if (String.compare (get_op exp) "=") = 0 then
			let children = get_children exp in
			let arg0 = BatList.nth children 0 in
			let arg1 = BatList.nth children 1 in
			let is_oracle_spec =
				if (Exprs.is_function_expr arg0) && (Exprs.is_function_expr arg1) then 
					let op0 = get_op arg0 in
					let op1 = get_op arg1 in
					((BatString.equal op0 target_function_name) && (BatMap.mem op1 macro_instantiator))
					|| ((BatString.equal op1 target_function_name) && (BatMap.mem op0 macro_instantiator))
				else
					false
			in
			let is_pbe_spec =
				if (Exprs.is_const_expr arg0) || (Exprs.is_const_expr arg1) then
					let target_expr = if (Exprs.is_const_expr arg0) then arg1 else arg0 in
					if (Exprs.is_function_expr target_expr) && (get_op target_expr) = target_function_name then 
						let children = Exprs.get_children target_expr in
						BatList.for_all (fun child -> Exprs.is_const_expr child) children
					else 
						false
				else
					false
			in	
			(* PBE spec: (f input) = output  *)
			if is_pbe_spec then
				let inputs, output = 
					if (BatString.equal (get_op arg0) target_function_name) then 
						(get_children arg0, expr2const arg1)
					else (get_children arg1, expr2const arg0)
				in
				(* let _ = prerr_endline (string_of_list string_of_expr inputs) in *)
				(* let _ = prerr_endline (string_of_expr output) in                *)
				let inputs = BatList.map expr2const inputs in   
				Specification.add_io_spec (inputs, output) spec
			(* Oracle spec: (f inputs) = (f' inputs) *)
			else if is_oracle_spec then 
				let oracle_expr, target_expr = 
					if (BatString.equal (get_op arg0) target_function_name) then 
						arg1, arg0
					else arg0, arg1 
				in
				let oracle_name = get_op oracle_expr in   
				let oracle_expr_resolved = try BatMap.find oracle_name macro_instantiator with _ -> assert false in  
				(* let _ = prerr_endline (Printf.sprintf "(assert (= %s %s))" (Exprs.string_of_expr oracle_expr_resolved) (Exprs.string_of_expr target_expr)) in  *)
				let _ = Specification.oracle_expr := oracle_expr in
				let _ = Specification.oracle_expr_resolved := oracle_expr_resolved in
				(* forall_var_map : variable name -> Param(int, ty) *)
				let _, forall_var_map = 
					let args = get_children oracle_expr in 
					List.fold_left (fun (i, m) var_expr ->
						let name = Exprs.string_of_expr var_expr in 
						(i + 1, BatMap.add name (Param(i, Exprs.type_of_expr var_expr)) m)  
					) (0, BatMap.empty) args 		
				in 
				let _ = Specification.forall_var_map := forall_var_map in 
				Specification.add_trivial_examples grammar spec
			else 
				let _ =
					try 
						assert ((BatMap.cardinal macro_instantiator) = 0)
					with _ -> failwith "Non-oracle spec cannot be mixed with macro definitions.";
				in
				let _ = LogicalSpec.add_constraint exp target_function_name in
				spec
		else
			let _ =
				try 
					assert ((BatMap.cardinal macro_instantiator) = 0)
				with _ -> failwith "Non-oracle spec cannot be mixed with macro definitions.";
			in
			let _ = LogicalSpec.add_constraint exp target_function_name in
			spec
	) Specification.empty_spec constraints_data 

let process_inv_constraints inv_constraints_data macro_instantiator target_function_name args_map =
	let _ = assert (BatList.length inv_constraints_data = 4) in
	let inv_constraints_data =
		BatList.map (fun sexp -> 
			match sexp with 
			| Sexp.Atom s -> s
			| _ -> assert false
		) inv_constraints_data
	in
	let (target, pre, trans, post) = 
		(BatList.nth inv_constraints_data 0, BatList.nth inv_constraints_data 1, 
		 BatList.nth inv_constraints_data 2, BatList.nth inv_constraints_data 3)
	in
	let _ =
		if (String.compare target target_function_name) != 0 then
			failwith ("Target function name does not match: expected " ^ target_function_name ^ ", but " ^ target); 
	in
	let _ = 
		if not ((BatMap.mem pre macro_instantiator) && (BatMap.mem trans macro_instantiator) && (BatMap.mem post macro_instantiator)) then
			failwith "Precondition, transition relation, and postcondition must be defined.";
	in
	let _ =
		if BatMap.cardinal macro_instantiator > 3 then
			failwith "Inv-constraint cannot be mixed with macro definitions.";
	in
	let pre_f = BatMap.find pre macro_instantiator in
	let trans_f = BatMap.find trans macro_instantiator in
	let post_f = BatMap.find post macro_instantiator in
	let (reverse_args_map, idx_to_type) = 
		BatMap.foldi (fun id param (acc1, acc2) ->
			match param with
			| Param(i, ty) -> 
				let (acc1, acc2) = (BatMap.add param (Var(id,ty)) acc1, BatMap.add i ty acc2) in
				(BatMap.add (Param(i + (BatMap.cardinal args_map), ty)) (Var(id ^ "!", ty)) acc1, BatMap.add (i + (BatMap.cardinal args_map)) ty acc2)
			| _ -> assert false
		) args_map (BatMap.empty, BatMap.empty)
	in
	let inv_f = 
		Function(
			target_function_name,
			BatList.map (fun idx -> 
				Param(idx, BatMap.find idx idx_to_type)
			) (BatList.range 0 `To ((BatMap.cardinal args_map) - 1)),
			Bool
		)
	in
	let inv_f_prime = 
		Function(
			target_function_name,
			BatList.map (fun idx -> 
				Param(idx, BatMap.find idx idx_to_type)
			) (BatList.range (BatMap.cardinal args_map) `To ((BatMap.cardinal args_map) * 2 - 1)),
			Bool
		)
	in
	let pre_constraint = Function("=>", [pre_f; inv_f], Bool) in
	let trans_constraint = Function("=>", [Function("and", [trans_f; inv_f], Bool); inv_f_prime], Bool) in
	let post_constraint = Function("=>", [inv_f; post_f], Bool) in
	let _ = LogicalSpec.add_pre_constraint (change_param_to_var reverse_args_map pre_constraint) in 
	let _ = LogicalSpec.add_trans_constraint (change_param_to_var reverse_args_map trans_constraint) in
	let _ = LogicalSpec.add_post_constraint (change_param_to_var reverse_args_map post_constraint) in
	Specification.empty_spec

let args_map_to_id2var args_map = 
	BatMap.foldi (fun id param acc ->
		match param with
		| Param(i, ty) -> 
			let nonprime = BatMap.add id (Var(id,ty)) acc in
		  BatMap.add (id ^ "!") (Var(id ^ "!", ty)) nonprime
		| _ -> assert false
	) args_map BatMap.empty

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
	let _ = Unix.unlink file' in
	let defs_data = filter_sexps_for "define-fun" sexps in
	(* BatSet.iter (fun sexp_list ->                                        *)
	(* 	let sexp = Sexp.List ((Sexp.Atom "define-fun") :: sexp_list) in    *)
	(* 	prerr_endline (string_of_sexp sexp)                                *)
	(* )  defs_data;                                                        *)
	let macro_instantiator = process_definitions defs_data in
	(* BatMap.iter (fun name expr ->               *)
	(* 	prerr_endline (sexpstr_of_fun name expr)  *)
	(* ) macro_instantiator;                       *)
	let synth_funs_data = filter_sexps_for "synth-fun" sexps in
	let _ =
		(* if (BatList.is_empty synth_funs_data) then
			failwith "No target function to be synthesized is given."
		else if (BatList.length synth_funs_data) > 1 then 
			failwith "Multi-function synthesis is not supported."  *)
		if (BatList.length synth_funs_data) > 1 then 
			failwith "Multi-function synthesis is not supported."	 
	in 
	if (BatList.is_empty synth_funs_data) then
	begin
		let synth_invs_data = filter_sexps_for "synth-inv" sexps in
		let _ = 
			if (BatList.is_empty synth_invs_data) then
				failwith "No target function to be synthesized is given."
			else if (BatList.length synth_invs_data) > 1 then 
				failwith "Multi-function synthesis is not supported."
		in
		let target_function_name, args_map, grammar = 
			process_synth_invs (BatList.hd synth_invs_data) 
		in
		let primed_vars_data = filter_sexps_for "declare-primed-var" sexps in
		let id2var =
			if (BatList.is_empty primed_vars_data) then
				let forall_vars_data = filter_sexps_for "declare-var" sexps in
				if (BatList.is_empty forall_vars_data) then
					args_map_to_id2var args_map
				else 
					process_forall_vars forall_vars_data
			else
				process_primed_vars primed_vars_data 
		in
		let _ = LogicalSpec.forall_var_map := id2var in (* to make Z3 query *)
		let inv_constraints_data = filter_sexps_for "inv-constraint" sexps in
		let _ = 
			if (BatList.is_empty inv_constraints_data) then
				failwith "No constraints are given."
			else if (BatList.length inv_constraints_data) > 1 then 
				failwith "Multi-function synthesis is not supported."
		in
		let spec = process_inv_constraints (BatList.hd inv_constraints_data) macro_instantiator target_function_name args_map in
		let spec =
			let cex_all_opt = LogicalSpec.add_trivial_examples target_function_name args_map spec in
			match cex_all_opt with
			| None -> spec
			| Some new_spec -> new_spec
		in
		(macro_instantiator, target_function_name, args_map, grammar, !Specification.forall_var_map, spec)
	end
	else
	begin
		let target_function_name, args_map, grammar = 
			process_synth_funcs (BatList.hd synth_funs_data) 
		in 
		(* prerr_endline (Grammar.string_of_grammar grammar); *)
		let forall_vars_data = filter_sexps_for "declare-var" sexps in
		let id2var = process_forall_vars forall_vars_data in  
		let constraints_data = filter_sexps_for "constraint" sexps in
		(* prerr_endline (string_of_list string_of_sexp (BatSet.choose constraints_data)); *)
		let spec = process_constraints grammar target_function_name constraints_data macro_instantiator id2var in
		let _ = LogicalSpec.forall_var_map := id2var in (* to make Z3 query *)
		let spec = 
			let cex_all_opt = LogicalSpec.add_trivial_examples target_function_name args_map spec in
			match cex_all_opt with
			| None -> spec
			| Some new_spec -> new_spec
		in
		my_prerr_endline (Specification.string_of_io_spec spec);
		(* print_endline (Specification.string_of_io_spec spec); *)
		(macro_instantiator, target_function_name, args_map, grammar, !Specification.forall_var_map, spec)  
	end