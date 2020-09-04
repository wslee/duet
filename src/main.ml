open Options
open Vocab

let main () = 
    let src = ref "" in
    let usage = "Usage: run <options> <file>" in
    let _ = Arg.parse options
                (fun
                   x ->
                     if Sys.file_exists x then src := x
                     else raise (Arg.Bad (x ^ ": No files given")))
                usage
    in
		if !src = "" then Arg.usage options usage
    else
			let (macro_instantiator, target_function_name, grammar, forall_var_map, spec) = 
				Parse.parse !src 
			in
			(* prerr_endline (Specification.string_of_io_spec spec);  *)
			(* let sol = Afta.synthesis (macro_instantiator, target_function_name, grammar, forall_var_map, spec) in *)
			(* let sol = Generator.enum_bu_search grammar spec in *)
			
			(* spec: ((const list) * const) list  *)
			let spec_total = spec in
			let start = Sys.time () in  
			(* CEGIS loop *)
			let rec cegis spec =
				prerr_endline (Specification.string_of_io_spec spec);
				prerr_endline (Printf.sprintf "CEGIS iter: %d" (List.length spec)); 
  			let sol =
  				Bidirectional.synthesis
						(macro_instantiator, target_function_name, grammar, forall_var_map, spec)
  			in
				(* let sol = Generator.enum_bu_search grammar spec in *)
				prerr_endline ("** candidate **");
				prerr_endline (Exprs.string_of_expr sol);
				let spec' = 
  				List.fold_left (fun acc (inputs, desired) ->
  					try
  						let signature = Exprs.compute_signature [(inputs, desired)] sol in
  						if (Pervasives.compare signature [desired]) <> 0
								 (* && (List.length acc) = (List.length spec)  *) (* only a single cex added *)
							then
  							acc @ [(inputs, desired)]
  						else acc
  					with Exprs.UndefinedSemantics -> acc @ [(inputs, desired)]
  				) spec spec_total
				in
				if (List.length spec) = (List.length spec') then 
					match (Specification.verify sol spec) with 
					| None -> sol 
					| Some cex ->
						prerr_endline (Specification.string_of_io_spec [cex]); 
						let _ = assert (not (List.mem cex spec')) in  
						cegis (cex :: spec')
				else cegis spec'
				(* try                                                                *)
				(* 	let signature = Exprs.compute_signature spec_total sol in        *)
				(* 	let desired = (List.map snd spec_total) in                       *)
  			(* 	let (i, _) =                                                     *)
  			(* 		BatList.findi (fun i (output_const, desired_output_const) ->   *)
  			(* 			(Pervasives.compare output_const desired_output_const) <> 0  *)
  			(* 		) (BatList.combine signature desired)                          *)
  			(* 	in                                                               *)
  			(* 	cegis (spec @ [List.nth spec_total i])                           *)
				(* with Not_found -> sol                                              *)
				(* | UndefinedSemantics ->                                            *)
			in
			let _ = assert ((List.length spec) > 0) in 
			(* let sol = cegis spec_total in *)
			let sol =
				if !Options.ex_all then cegis spec_total 
				else cegis [List.nth spec 0] 
			in
			prerr_endline ("****** solution *******");
			prerr_endline (Exprs.string_of_expr sol);
			prerr_endline ("size : " ^ (string_of_int (Exprs.size_of_expr sol)));
			prerr_endline ("time : " ^ (Printf.sprintf "%.2f sec" (Sys.time() -. start)));
			(* prerr_endline ("check dist time : " ^ (Printf.sprintf "%.2f sec" (!Witness.check_dist_time))); *)
			()
		 
let _ = main ()
