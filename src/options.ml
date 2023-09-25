let debug = ref false
let max_size = ref 32
let max_height = ref 0
let init_comp_size = ref 1
let find_all = ref false 
let get_size = ref false 
let ex_all = ref false 
let fast_dt = ref false 
let lbu = ref false 
let z3_cli = ref false

let options = 
	[
 	 ("-lbu", Arg.Set lbu, "Learning-based unifier");
	 ("-fastdt", Arg.Set fast_dt, "Use a heuristic to compute entropies faster (may generate larger solutions)");
	 ("-ex_all", Arg.Set ex_all, "Provide all the IO examples upfront");
	 ("-get_size", Arg.Set get_size, "Get size of an expression");
	 ("-all", Arg.Set find_all, "Find all solutions and pick the smallest one");	
	 ("-debug", Arg.Set debug, "print info for debugging");
	 ("-max_size", Arg.Int (fun x -> max_size := x), "set the maximum size of candidates");
	 ("-max_height", Arg.Int (fun x -> max_height := x), "set the maximum height of candidates");
	 ("-init_comp_size", Arg.Int (fun x -> init_comp_size := x), "set the initial size of components");
	 ("-z3cli", Arg.Set z3_cli, "Use Z3 via command line interface");
  ]