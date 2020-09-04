let rec gcd a b =
  if (Int64.equal b Int64.zero) then a else gcd b (Int64.rem a b) 
	
let g n x = Int64.rem (Int64.add (Int64.mul x x) Int64.one) n 
	
let factorize n = 
	if (Int64.equal n Int64.one) then (Int64.one, Int64.one)
	else 
	let x = ref (Int64.of_int 2) in 
	let y = ref (Int64.of_int 2) in 
	let d = ref (Int64.of_int 1) in 
	while (Int64.equal !d (Int64.one)) do
		x := (g n) !x;
		y := (g n (g n !y));
		d := gcd (Int64.abs (Int64.sub !x !y)) n;
		(* prerr_endline (Printf.sprintf "gcd %s %s = %s" (Int64.to_string (Int64.sub (Int64.abs !x) (Int64.abs !y))) (Int64.to_string n) (Int64.to_string !d)); *)
		(* prerr_endline (Printf.sprintf "n:%s x:%s y:%s d:%s" (Int64.to_string n) (Int64.to_string !x) (Int64.to_string !y) (Int64.to_string !d)); *)
	done;
	if (Int64.equal !d n) then (Int64.one, n)
	else (!d, Int64.div n !d) 
	 