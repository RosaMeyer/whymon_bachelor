(* To run:

ocamlfind ocamlc -package ocamlgraph -linkpkg graph_test.ml -o graph_test
./graph_test

*)

(*
(* graph_test.ml *)
open Graph

(* Define the graph module *)
module G = Graph.Pack.Digraph

(* Define the module for min_cutset operations *)
module Cut = Graph.Mincut.Make(G)

(* Use the Edmonds-Karp algorithm for flow computation *)
module Flow = Graph.Flow.Ford_Fulkerson(G)

(* Define the Flow module outside of the function *)
module F = Flow(struct
  type t = int
  type label = int
  let max_capacity _ = max_int
  let flow _ = 0
  let add = (+)
  let sub = (-)
  let zero = 0
  let compare = compare
  let min_capacity _ = 0
  let graph = G.create ()
end)  

(* Main function *)
let () =
  (* Create a directed graph *)
  let g = G.create () in

  (* Add vertices *)
  let v1 = G.V.create 1 in
  let v2 = G.V.create 2 in
  let v3 = G.V.create 3 in
  let v4 = G.V.create 4 in
  let v5 = G.V.create 5 in

  G.add_vertex g v1;
  G.add_vertex g v2;
  G.add_vertex g v3;
  G.add_vertex g v4;
  G.add_vertex g v5;

  (* Add edges with capacities *)
  G.add_edge_e g (G.E.create v1 3 v2); (* Edge from v1 to v2 with weight 3 *)
  G.add_edge_e g (G.E.create v2 2 v3); (* Edge from v2 to v3 with weight 2 *)
  G.add_edge_e g (G.E.create v3 3 v4); (* Edge from v3 to v4 with weight 3 *)
  G.add_edge_e g (G.E.create v4 2 v5); (* Edge from v4 to v5 with weight 2 *)

  (* Compute max flow *)
  let source = v1 in
  let sink = v5 in
  let module F = Flow(struct
    type t = int
    type label = int
    let max_capacity _ = max_int
    let flow _ = 0
    let add = (+)
    let sub = (-)
    let zero = 0
    let compare = compare
    let min_capacity _ = 0
    let graph = G.create ()
  end) in
  let _, flow = F.maxflow g source sink in

  (* Print the maximum flow *)
  Printf.printf "Testing min_cut using Ford-Fulkerson algorithm:\n";
  Printf.printf "Maximum flow: %d\n" flow;

  (* Compute the min-cut *)
  let cutset = Cut.min_cutset g source in
  Printf.printf "Min-cut vertices reachable from source (%d):\n" (G.V.label source);
  List.iter
    (fun v -> Printf.printf "Vertex: %d\n" (G.V.label v))
    (G.fold_vertex (fun v acc -> if List.mem v cutset then v :: acc else acc) g []); *)






open Graph

(* Define the graph module *)
module G = Graph.Pack.Digraph

(* Define the module for min_cutset operations *)
module Cut = Graph.Mincut.Make(G)

(* module Flow = Graph.Flow.Goldberg_Tarjan(G)(struct
type t = int
type label = int
let max_capacity x = x
let flow _ = 0
let add = (+)
let sub = (-)
let zero = 0
let compare = compare
end) *)

module Flow = Graph.Flow.Ford_Fulkerson(G)(struct
  type t = int
  type label = int
  let max_capacity x = x
  let flow _ = 0
  let add = (+)
  let sub = (-)
  let zero = 0
  let compare = compare
  let min_capacity _ = 0
end)

(* Main function *)
let () =
  (* Create a directed graph *)
  let g = G.create () in

  (* Add vertices *)
  let v1 = G.V.create 1 in
  let v2 = G.V.create 2 in
  let v3 = G.V.create 3 in
  let v4 = G.V.create 4 in
  let v5 = G.V.create 5 in

  (* G.add_vertex g v1;
  G.add_vertex g v2; *)
  (* G.add_vertex g v3;
  G.add_vertex g v4;
  G.add_vertex g v5; *)

  let e1 = G.E.create v1 3 v2 in

  (* Add edges with capacities *)
  G.add_edge_e g (e1); (* Edge from v1 to v2 with weight 3 *)
  G.add_edge_e g (G.E.create v2 2 v3); (* Edge from v2 to v3 with weight 2 *)
  G.add_edge_e g (G.E.create v3 3 v4); (* Edge from v3 to v4 with weight 3 *)
  G.add_edge_e g (G.E.create v4 2 v5); (* Edge from v4 to v5 with weight 2 *)

  (* Compute max flow *)
  let source = v1 in
  let sink = v5 in
  let flow_f, flow = Flow.maxflow g source sink in

  (* Print the maximum flow *)
  Printf.printf "Testing min_cut using Ford-Fulkerson algorithm:\n";
  Printf.printf "Maximum flow: %d\n" flow;

  Printf.printf "Flow: %d\n" (flow_f e1);

  (* Compute the min-cut *)
  let cutset = Cut.min_cutset g source in
  Printf.printf "Min-cut vertices reachable from source (%d):\n" (G.V.label source);
  List.iter
    (fun v -> Printf.printf "Vertex: %d\n" (G.V.label v))
    cutset;    
    
  

G.iter_edges (fun v1 v2 -> Printf.printf "Edge: %d -> %d\n" (G.V.label v1) (G.V.label v2)) g; 








(*
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
  (g, v1)              (* Return the graph and the source vertex *)

(* Return the resulting list from min_cutset *)
let min_cutset () =
  let g, source = create_sample_graph () in
  let cutset = Cut.min_cutset g source in
  Printf.printf "Min cuts (%d):" (List.length cutset);
  List.iter (fun v -> Printf.printf " %d" (G.V.label v)) cutset;
  cutset

(* Main function *)
let () =
  let _ = min_cutset () in
  () *)






(* 
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
  (* Add edges with capacities *)
  G.add_edge_e g (G.E.create v1 3 v2);  (* edge from 1 to 2 with weight 3 *)
  G.add_edge_e g (G.E.create v1 2 v3);  (* edge from 1 to 3 with weight 2 *)
  G.add_edge_e g (G.E.create v2 4 v4);  (* edge from 2 to 4 with weight 4 *)
  G.add_edge_e g (G.E.create v3 1 v4);  (* edge from 3 to 4 with weight 1 *)
  G.add_edge_e g (G.E.create v4 2 v5);  (* edge from 4 to 5 with weight 2 *)
  (g, v1, v5)  (* Return the graph, source, and sink *)

(* Test the min_cutset function *)
let test_min_cutset () =
  let g, source, sink = create_sample_graph () in
  (* let _, max_flow = F.maxflow g source sink in
  Printf.printf "Maximum flow: %d\n" max_flow; *)
  (* Compute the minimum cut *)
  let cutset = Cut.min_cutset g source in
  Printf.printf "Min-cut vertices reachable from source (%d):\n" (G.V.label source);
  List.iter (fun v ->
    Printf.printf "Vertex: %d\n" (G.V.label v)
  ) cutset

(* Main function *)
let () =
  Printf.printf "Testing min_cut using Ford-Fulkerson algorithm:\n";
  test_min_cutset () *)