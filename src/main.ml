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

			()
		 
let _ = main ()