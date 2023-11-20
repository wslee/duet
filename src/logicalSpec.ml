open Sexplib
open Vocab
open Exprs
open Z3
open BidirectionalUtils

type t = (Exprs.expr) list
let empty_spec = []

(* constraints that consist of logical spec *)
let logical_spec = ref empty_spec
let add_constraint e = 
	logical_spec := (e :: !logical_spec)

let get_counter_example sol spec = 
	if !logical_spec = [] then None (* can't found logical spec *)
	else 
		let ctx = Z3.mk_context	[("model", "true"); ("proof", "false")] in
		(* STEP 01 : make logical spec to one expression (combine by 'and') *)
		(* STEP 02 : resolve target function *)
		(* STEP 03 : make Z3 query *)
		(* STEP 04 : get cex-in as counter example *)
