(* To run:

ocamlfind ocamlc -package ocamlgraph -linkpkg graph_test.ml -o graph_test
./graph_test

*)

(* bin/whymon.exe -sig examples/paper-tool/three_attempts.sig -formula examples/paper-tool/three_attempts_copy.mfotl -log examples/paper-tool/three_attempts.log *)

open Graph

(* Define the graph module *)
module G = Graph.Pack.Digraph

(* Define the module for min_cutset operations *)
module Cut = Graph.Mincut.Make(G)

type eint = Int of int | Inf

let e0 = Int 0

let eadd e1 e2 = match e1, e2 with
  | Int x, Int y -> Int (x + y)
  | _ -> Inf

let esub e1 e2 = match e1, e2 with
  | Int x, Int y -> Int (x - y)
  | Int x, Inf -> e0
  | _ -> Inf

let ecompare e1 e2 = match e1, e2 with
  | Int x, Int y -> compare x y
  | Int _, Inf -> -1
  | Inf, Int _ -> 1
  | Inf, Inf -> 0  
  
let to_string = function
  | Int x -> string_of_int x
  | Inf -> "inf"

module EI = struct
  type t = eint
  let compare : t -> t -> int = ecompare
  let default = e0
end
  
module EG = Imperative.Digraph.AbstractLabeled(EI)(EI)

module Flow = Graph.Flow.Ford_Fulkerson(EG)(struct
  type t = eint
  type label = eint
  let max_capacity x = x
  let flow _ = e0
  let add = eadd
  let sub = esub
  let zero = e0
  let compare = ecompare
  let min_capacity _ = e0
end)


(* Added: 28/01 - Perform depth-first search on the residual network to find the minimum cut - traverses the residual network
and marks reachable vertices, the markings are used to identify edges that form the minimum cut *)
let dfs residual visited start =
  let rec visit v =
    if not (Hashtbl.mem visited v) then (
      Hashtbl.add visited v true;
      EG.iter_succ (fun u ->
        let edge = EG.find_edge residual v u in
        let capacity = EG.E.label edge in (* lable = capacity *)
        if ecompare capacity e0 > 0 then visit u
      ) residual v)
in visit start

(* Added: 28/01 - identifies the marked vertices in the residual network and determines the edges that form the cut *)
(* Identify the minimum cut edges *)
let min_cut g source sink flow_f =
  (* Build the residual network *)
  let residual = EG.copy g in
  EG.iter_edges_e (fun e ->
    let u = EG.E.src e in
    let v = EG.E.dst e in
    let capacity = EG.E.label e in
    let f = flow_f e in
    let residual_capacity = esub capacity f in
    if ecompare residual_capacity e0 > 0 then
      EG.add_edge_e residual (EG.E.create u residual_capacity v);
    if ecompare f e0 > 0 then
      EG.add_edge_e residual (EG.E.create v f u)
  ) g;

  (* Mark all vertices reachable from the source in the residual network *)
  let visited = Hashtbl.create (EG.nb_vertex residual) in dfs residual visited source;

  (* Collect the edges that form the cut using List.fold_left *)
  EG.fold_edges_e (fun e acc ->
    let u = EG.E.src e in
    let v = EG.E.dst e in
    if Hashtbl.mem visited u && not (Hashtbl.mem visited v) then
      e :: acc  (* Add to the list acc *)
    else acc
  ) g []


(* Main function *)
let () =
  (* Create a directed graph *)
  let g = EG.create () in

  (* Add vertices *)
  let v1 = EG.V.create (Int 1) in
  let v2 = EG.V.create (Int 2) in
  let v3 = EG.V.create (Int 3) in
  let v4 = EG.V.create (Int 4) in

  let e1 = EG.E.create v1 (Inf) v2 in
  let e2 = EG.E.create v1 (Int 2) v3 in
  let e3 = EG.E.create v2 (Int 5) v3 in
  let e4 = EG.E.create v2 (Int 2) v4 in
  let e5 = EG.E.create v3 (Inf) v4 in
  let e6 = EG.E.create v1 (Int 6) v4 in

  (* Add edges with capacities *)
  EG.add_edge_e g (e1);
  EG.add_edge_e g (e2);
  EG.add_edge_e g (e3);
  EG.add_edge_e g (e4);
  EG.add_edge_e g (e5);
  EG.add_edge_e g (e6);

  (* Compute max flow *)
  let source = v1 in
  let sink = v4 in
  let flow_f, flow = Flow.maxflow g source sink in
  
  (* Print the maximum flow *)
  Printf.printf "Testing min_cut using Ford-Fulkerson algorithm:\n";
  Printf.printf "Maximum flow: %s\n" (to_string flow);

  (* Added: 01/02 - Function to collect edges from the graph *)
  let collect_edges graph =
    EG.fold_edges_e (fun e acc -> e :: acc) graph [] |> List.rev in
  
  (* Added: 01/02 - Function to print flows for all edges *)
  Printf.printf "\nMaximum flow for edges:\n";
  let edges = collect_edges g in
  List.iter (fun e ->
    let u = EG.E.src e in
    let v = EG.E.dst e in
    Printf.printf "Edge from v%s to v%s has flow %s\n"
      (to_string (EG.V.label u))
      (to_string (EG.V.label v))
      (to_string (flow_f e))  
  ) edges;

  (* Added: 28/01 - Finds and prints the minimum cut *)
  let cut_edges = min_cut g source sink flow_f in
  Printf.printf "\nMinimum cut edges:\n";
  List.iter (fun e ->
    let u = EG.E.src e in
    let v = EG.E.dst e in
    Printf.printf "Edge from v%s to v%s\n"
      (to_string (EG.V.label u))
      (to_string (EG.V.label v))
  ) cut_edges;





(* 

EXAMPlES and notes

*)


(*   
  let e1 = EG.E.create v1 (Int 10) v2 in
  let e2 = EG.E.create v1 (Int 10) v3 in
  let e3 = EG.E.create v2 (Int 2) v3 in
  let e4 = EG.E.create v2 (Int 8) v4 in
  let e5 = EG.E.create v3 (Int 9) v5 in
  let e6 = EG.E.create v4 (Int 6) v5 in
  let e7 = EG.E.create v2 (Int 4) v5 in
  let e8 = EG.E.create v5 (Int 10) v6 in
  let e9 = EG.E.create v4 (Int 10) v6 in

  (* Add edges with capacities *)
  EG.add_edge_e g (e1);
  EG.add_edge_e g (e2);
  EG.add_edge_e g (e3);
  EG.add_edge_e g (e4);
  EG.add_edge_e g (e5);
  EG.add_edge_e g (e6);
  EG.add_edge_e g (e7);
  EG.add_edge_e g (e8);
  EG.add_edge_e g (e9);
*)


(*   
  Printf.printf "Flow e1: %s\n" (to_string (flow_f e1));
  Printf.printf "Flow e2: %s\n" (to_string (flow_f e2));
  Printf.printf "Flow e3: %s\n" (to_string (flow_f e3));
  Printf.printf "Flow e4: %s\n" (to_string (flow_f e4));
  Printf.printf "Flow e4: %s\n" (to_string (flow_f e5)); 
*)

(*
  (* Add vertices *)
  let v1 = EG.V.create (Int 1) in
  let v2 = EG.V.create (Int 2) in
  let v3 = EG.V.create (Int 3) in
  let v4 = EG.V.create (Int 4) in
  let e1 = EG.E.create v1 (Inf) v2 in
  let e2 = EG.E.create v2 (Int 5) v3 in
  let e3 = EG.E.create v3 (Int 5) v4 in
  let e4 = EG.E.create v1 (Int 6) v4 in
  let e5 = EG.E.create v1 (Inf) v3 in
  let e6 = EG.E.create v2 (Int 2) v4 in
    
  (* Add edges with capacities *)
  EG.add_edge_e g (e1); (* Edge from v1 to v2 with weight 3 *)
  EG.add_edge_e g (e2);
  EG.add_edge_e g (e3);
  EG.add_edge_e g (e4);
  EG.add_edge_e g (e5);
  EG.add_edge_e g (e6); 
*)



(*
  (* Add vertices *)
  let v1 = EG.V.create (Int 1) in
  let v2 = EG.V.create (Int 2) in
  let v3 = EG.V.create (Int 3) in
  let v4 = EG.V.create (Int 4) in

  let e1 = EG.E.create v1 (Int 10) v2 in
  let e2 = EG.E.create v1 (Int 5) v3 in
  let e3 = EG.E.create v2 (Int 15) v3 in
  let e4 = EG.E.create v2 (Int 10) v4 in
  let e5 = EG.E.create v3 (Int 10) v4 in

  (* Add edges with capacities *)
  EG.add_edge_e g (e1);
  EG.add_edge_e g (e2);
  EG.add_edge_e g (e3);
  EG.add_edge_e g (e4);
  EG.add_edge_e g (e5);
*)



(* Working example

  (* Add vertices *)
  let v1 = EG.V.create (Int 1) in
  let v2 = EG.V.create (Int 2) in
  let v3 = EG.V.create (Int 3) in
  let v4 = EG.V.create (Int 4) in
  let v5 = EG.V.create (Int 5) in
  let v6 = EG.V.create (Int 6) in

  let e1 = EG.E.create v1 (Int 7) v2 in
  let e2 = EG.E.create v1 (Int 4) v3 in
  let e3 = EG.E.create v3 (Int 3) v2 in
  let e4 = EG.E.create v2 (Int 5) v4 in
  let e5 = EG.E.create v2 (Int 3) v5 in
  let e6 = EG.E.create v3 (Int 2) v5 in
  let e7 = EG.E.create v4 (Int 8) v6 in
  let e8 = EG.E.create v5 (Int 3) v4 in
  let e9 = EG.E.create v5 (Int 5) v6 in

  (* Add edges with capacities *)
  EG.add_edge_e g (e1);
  EG.add_edge_e g (e2);
  EG.add_edge_e g (e3);
  EG.add_edge_e g (e4);
  EG.add_edge_e g (e5);
  EG.add_edge_e g (e6);
  EG.add_edge_e g (e7);
  EG.add_edge_e g (e8);
  EG.add_edge_e g (e9);

*)



(* Working example

  (* Add vertices *)
  let v1 = EG.V.create (Int 1) in
  let v2 = EG.V.create (Int 2) in
  let v3 = EG.V.create (Int 3) in
  let v4 = EG.V.create (Int 4) in
  let v5 = EG.V.create (Int 5) in
  let v6 = EG.V.create (Int 6) in

  let e1 = EG.E.create v1 (Int 10) v2 in
  let e2 = EG.E.create v1 (Int 10) v3 in
  let e3 = EG.E.create v2 (Int 2) v3 in
  let e4 = EG.E.create v2 (Int 4) v4 in
  let e5 = EG.E.create v2 (Int 8) v5 in
  let e6 = EG.E.create v3 (Int 9) v5 in
  let e7 = EG.E.create v4 (Int 10) v6 in
  let e8 = EG.E.create v5 (Int 6) v4 in
  let e9 = EG.E.create v5 (Int 10) v6 in

  (* Add edges with capacities *)
  EG.add_edge_e g (e1);
  EG.add_edge_e g (e2);
  EG.add_edge_e g (e3);
  EG.add_edge_e g (e4);
  EG.add_edge_e g (e5);
  EG.add_edge_e g (e6);
  EG.add_edge_e g (e7);
  EG.add_edge_e g (e8);
  EG.add_edge_e g (e9);

*)


(*   let e1 = EG.E.create v1 (Int 4) v2 in
  let e2 = EG.E.create v1 (Int 3) v3 in
  let e3 = EG.E.create v2 (Int 2) v3 in
  let e4 = EG.E.create v2 (Int 1) v4 in
  let e5 = EG.E.create v3 (Int 3) v4 in

  (* Add edges with capacities *)
  EG.add_edge_e g (e1);
  EG.add_edge_e g (e2);
  EG.add_edge_e g (e3);
  EG.add_edge_e g (e4);
  EG.add_edge_e g (e5);*)