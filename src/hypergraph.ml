(** hypergraph *)
open Graph 
open Vocab

module IntNode = 
	struct 
		type t = int
		let compare a b = a - b 
		let equal = (=) 
		let hash n = n  
	end    

module G = 
struct 
  module I = Imperative.Digraph.ConcreteBidirectional (IntNode) 
  
  type t = {graph : I.t; label: ((IntNode.t * IntNode.t), (IntNode.t list) BatSet.t) Hashtbl.t } 
  
  let create ~size () = { graph = I.create ~size (); label = Hashtbl.create (2 * size) }
  let succ g n = I.succ g.graph n
  let pred g n = I.pred g.graph n
  let nb_vertex g = I.nb_vertex g.graph
  let pred_e g n = I.pred g.graph n |> List.map (fun p -> (p, Hashtbl.find g.label (p,n), n))
  let fold_vertex f g a = I.fold_vertex f g.graph a
  let fold_edges f g a = I.fold_edges f g.graph a
  let iter_edges f g = I.iter_edges f g.graph
  let fold_succ f g a = I.fold_succ f g.graph a
  let remove_vertex g n = I.remove_vertex g.graph n; g
  let add_vertex g v = I.add_vertex g.graph v; g
	let add_edge g s d = I.add_edge g.graph s d; g
  let add_edge_e g (s,label,d) =
		let labels = try Hashtbl.find g.label (s, d) with _ -> BatSet.empty in  
    Hashtbl.replace g.label (s,d) (BatSet.add label labels);
    add_edge g s d
  let remove_edge g s d = I.remove_edge g.graph s d; Hashtbl.remove g.label (s,d); g
  let find_label g s d = Hashtbl.find g.label (s,d)
end
