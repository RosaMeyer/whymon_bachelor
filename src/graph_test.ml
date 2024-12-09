(* To run:

ocamlfind ocamlc -package ocamlgraph -linkpkg graph_test.ml -o graph_test
./graph_test

*)


(* graph_test.ml *)
open Graph

(* Define the graph module *)
module G = Graph.Pack.Digraph

(* Define the module for min_cutset operations *)
module Cut = Graph.Mincut


(* Function to create a sample graph *)
let create_sample_graph () =
  let g = G.create () in
  (* Add vertices *)
  let v1 = G.V.create 1 in
  let v2 = G.V.create 2 in
  let v3 = G.V.create 3 in
  let v4 = G.V.create 4 in
  let v5 = G.V.create 5 in
  List.iter (G.add_vertex g) [v1; v2; v3; v4; v5];
  (* Add edges *)
  G.add_edge g v1 v2;  (* edge from 1 to 2 *)
  G.add_edge g v1 v3;  (* edge from 1 to 3 *)
  G.add_edge g v2 v4;  (* edge from 2 to 4 *)
  G.add_edge g v3 v4;  (* edge from 3 to 4 *)
  G.add_edge g v4 v5;  (* edge from 4 to 5 *)
  (g, v1)  (* Return the graph and the source vertex *)
  
(* Test the min_cutset function *)
let test_min_cutset () =
  let g, source = create_sample_graph () in
  let cutset = Cut.min_cutset g source in
  Printf.printf "Min-cut vertices reachable from source (%d):\n" (G.V.label source);
  List.iter (fun v ->
    Printf.printf "Vertex: %d\n" (G.V.label v)
  ) cutset

(* Main function *)
let () =
  Printf.printf "Testing min_cutset on a sample graph:\n";
  test_min_cutset ()
