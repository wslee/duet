open Options
open Vocab

let main () = 
    let src = ref "" in
    let usage = Printf.sprintf "Usage: %s <options> <file>" Sys.argv.(0) in
    let _ = Arg.parse options
                (fun x ->
                     if Sys.file_exists x then src := x
                     else raise (Arg.Bad (x ^ ": No files given"))
								)
                usage
    in
		if !src = "" then Arg.usage options usage
    else
			let start = Sys.time () in
			let (macro_instantiator, target_function_name, args_map, grammar, forall_var_map, spec) = 
				Parse.parse !src 
			in
			let grammar = Grammar.preprocess macro_instantiator grammar in 
			(* PBE spec - input-output examples : ((const list) * const) list  *)
			let spec_total = spec in
			(* CEGIS loop *)
			let rec cegis spec =
				my_prerr_endline (Specification.string_of_io_spec spec);
				my_prerr_endline (Printf.sprintf "CEGIS iter: %d" (List.length spec));
  			let sol =
  				Bidirectional.synthesis
						(macro_instantiator, target_function_name, grammar, forall_var_map, spec)
  			in
				my_prerr_endline (Printf.sprintf "** Proposed candidate: %s **" (Exprs.string_of_expr sol));
				(* spec' = spec + mismatched input-output examples *)
				let spec' = 
  				List.fold_left (fun acc (inputs, desired) ->
  					try
  						let signature = Exprs.compute_signature [(inputs, desired)] sol in
  						if (Pervasives.compare signature [desired]) <> 0 then
  							acc @ [(inputs, desired)]
  						else acc
  					with Exprs.UndefinedSemantics -> acc @ [(inputs, desired)]
  				) spec spec_total
				in
				(* no mismatched input-output examples *)
				if (List.length spec) = (List.length spec') then 
					match (if !Options.z3_cli then Specification.verify_cli else Specification.verify) sol spec with 
					| None -> sol 
					| Some cex ->
						my_prerr_endline (Specification.string_of_io_spec [cex]); 
						let _ = assert (not (List.mem cex spec')) in  
						cegis (cex :: spec')
				else cegis spec'
			in
			let _ = assert ((List.length spec) > 0) in 
			let sol =
				if !Options.ex_all then cegis spec_total 
				else cegis [List.nth spec 0] 
			in
			(* prerr_endline (Exprs.string_of_expr sol); *)
			prerr_endline (Exprs.sexpstr_of_fun args_map target_function_name sol);
			prerr_endline ("****************** statistics *******************");
			prerr_endline ("size : " ^ (string_of_int (Exprs.size_of_expr sol)));
			prerr_endline ("time : " ^ (Printf.sprintf "%.2f sec" (Sys.time() -. start)));
			prerr_endline ("max_component_size : " ^ (string_of_int !Bidirectional.curr_comp_size));
			prerr_endline ("# components : " ^ (string_of_int !Bidirectional.num_components));
			prerr_endline ("time for composition : " ^ (Printf.sprintf "%.2f sec" !Bidirectional.td_time));
			prerr_endline ("time for component generation : " ^ (Printf.sprintf "%.2f sec" !Bidirectional.bu_time));
			(* prerr_endline ("*************** bottomup detail ******************");
			prerr_endline ("time for alternative spec : " ^ (Printf.sprintf "%.2f sec (%d components)" !Bottomup.alt_time !Bottomup.alt_comp));
			prerr_endline ("time for computing : " ^ (Printf.sprintf "%.2f sec" !Bottomup.compute_time));
			prerr_endline ("time for adapting : " ^ (Printf.sprintf "%.2f sec" !Bidirectional.adapt_time)); *)
			prerr_endline ("**************************************************");
			()
		 
let _ = main ()
