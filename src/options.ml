let debug = ref false
let max_size = ref 32
let max_height = ref 0
let init_comp_size = ref 1
let use_afta = ref true 
let use_ktree = ref true
let no_astar = ref false
let opt_solver = ref "~/utils/open-wbo/open-wbo" 
let used_primes = ref "3 5 7"
let modulus = ref 32 
let modulus_astar = ref 2
let find_all = ref false 
let get_size = ref false 
let theta = ref 0.9
let ex_all = ref false 
let fast_dt = ref false 
let lbu = ref false 

let options = 
	[
	 ("-theta", Arg.Float (fun x -> theta := x), "Set modulus");	
 	 ("-lbu", Arg.Set lbu, "Learning-based unifier");
	 ("-fastdt", Arg.Set fast_dt, "Use a heuristic to compute entropies faster (may generate larger solutions)");
	 ("-ex_all", Arg.Set ex_all, "Provide all the IO examples upfront");
	 ("-get_size", Arg.Set get_size, "Get size of an expression");
	 ("-all", Arg.Set find_all, "Find all solutions and pick the smallest one");	
	 ("-m", Arg.Int (fun x -> modulus := x), "Set modulus"); 	
	 ("-solver", (Arg.Set_string opt_solver), "Set path for maxsat solver (e.g., -solver [target_filename] (default:~/utils/open-wbo/open-wbo)");	
	 ("-debug", Arg.Set debug, "print info for debugging");
	 ("-max_size", Arg.Int (fun x -> max_size := x), "set the maximum size of candidates");
	 ("-max_height", Arg.Int (fun x -> max_height := x), "set the maximum height of candidates");
	 ("-init_comp_size", Arg.Int (fun x -> init_comp_size := x), "set the initial size of components");
	 ("-ktree", Arg.Set use_ktree, "use ktree encoding");
	 ("-afta", Arg.Set use_afta, "use afta");
	 ("-noastar", Arg.Set no_astar, "use uniform search");
	 ("-ma", Arg.Int (fun x -> modulus_astar := x), "modulus for astar search");
  ]