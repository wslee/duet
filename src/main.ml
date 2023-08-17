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
				Myparse.parse !src 
			in
			let synthesis = Cegis.cegis (macro_instantiator, target_function_name, args_map, grammar, forall_var_map, spec) in
			let endt = Sys.time () in
      (* print_endline (string_of_map string_of_int (string_of_map Grammar.string_of_rewrite (string_of_set string_of_int)) synthesis) *)
      (* print_endline (string_of_list Exprs.string_of_const synthesis) *)
      print_endline (string_of_float (endt -. start));
      print_endline (Exprs.string_of_expr synthesis);
      ()
		 
let _ = main ()