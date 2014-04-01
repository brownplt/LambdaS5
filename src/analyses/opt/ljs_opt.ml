open Ljs_syntax

type node = {
  block: exp;
  edgeIn: (node list) ref;
  edgeOut: (node list) ref;
}

(* cfg is used to describe a control flow graph. A cfg
consists of a `first` node, which is the node that flow 
comes into, and a set of `last` nodes, which the flow goes
out from *)
type cfg = {
  first: node;
  last : node list;
}

(* add edges from node1 to node2. node1's out edge will
   include node2 and node2's in edge will include node1 *)
let add_edge (node1 : node) (node2 : node) : unit =
  node1.edgeOut :=  node2 :: !(node1.edgeOut) ;
  node2.edgeIn  :=  node1 :: !(node2.edgeIn)
;;

(* add list of nodes as the in-nodes of the second argument *)
let add_edges (n_list : node list) (node2 : node) : unit =
  List.iter (fun node1 -> add_edge node1 node2) n_list
;;

let link_graphs (graph_list : cfg list) : unit =
  let rec link_graph (prev: cfg) (nexts: cfg list) : unit =
    match nexts with
    | [] -> ()
    | first :: rest -> 
       add_edges prev.last first.first;
       link_graph first rest in
  match graph_list with
  | [] -> ()
  | prev :: nexts -> link_graph prev nexts
;;

(* map from string(ret id in this case) to something else *)
module StringMap = Map.Make(String);;

let rec build_graph (labelMap : cfg StringMap.t) (e : exp) : cfg =
  let init_cfg exp = 
    let node = { block = exp; edgeIn = ref []; edgeOut = ref [] } in
    {first = node; last = [node]} in
  match e with
  | Null (_) -> init_cfg e
  | Undefined (_) -> init_cfg e
  | String (_, s) -> init_cfg e
  | Num (_, n) -> init_cfg e
  | True (_) -> init_cfg e
  | False (_) -> init_cfg e
  | Id (_, id) -> init_cfg e
  | Object (_, attr, lst) -> init_cfg e
  | GetAttr (_, prop, obj, field) ->
     let g1 = build_graph labelMap obj in
     let g2 = build_graph labelMap field in
     add_edges g1.last g2.first;
     {first = g1.first ; last = g2.last}

  | SetAttr (_, prop, obj, field, newval) ->
     let g1 = build_graph labelMap obj in
     let g2 = build_graph labelMap field in
     let g3 = build_graph labelMap newval in
     link_graphs [g1; g2; g3];
     {first = g1.first; last = g3.last}

  | GetObjAttr (_, oattr, obj) ->  build_graph labelMap obj
  | SetObjAttr (_, oattr, obj, attre) ->
     let g1 = build_graph labelMap obj in
     let g2 = build_graph labelMap attre in
     add_edges g1.last g2.first;
     {first = g1.first; last = g2.last}
  | GetField (_, obj, f, arg) ->
     let g1 = build_graph labelMap obj in
     let g2 = build_graph labelMap f in
     let g3 = build_graph labelMap arg in
     link_graphs [g1; g2; g3];
     {first = g1.first; last = g3.last}
  | SetField (_, obj, f, v, arg) ->
     let g1 = build_graph labelMap obj in
     let g2 = build_graph labelMap f in
     let g3 = build_graph labelMap v in
     let g4 = build_graph labelMap arg in
     link_graphs [g1; g2; g3; g4];
     {first = g1.first; last = g4.last}

  | DeleteField (_, obj, field) ->
     let g1 = build_graph labelMap obj in
     let g2 = build_graph labelMap field in
     add_edges g1.last g2.first;
     {first = g1.first; last = g2.last}

  | OwnFieldNames (_, obj) -> build_graph labelMap obj
  | SetBang (_, _, e) -> build_graph labelMap e
  | Op1 (_, op, e) -> build_graph labelMap e
  | Op2 (_, op, e1, e2) ->
     let g1 = build_graph labelMap e1 in
     let g2 = build_graph labelMap e2 in
     add_edges g1.last g2.first;
     {first = g1.first; last = g2.last}

  | Seq (_, e1, e2) ->
     let g1 = build_graph labelMap e1 in
     let g2 = build_graph labelMap e2 in
     add_edges g1.last g2.first;
     {first = g1.first ; last = g2.last}

  | If (_, tst, thn, els) ->
     let g1 = build_graph labelMap tst in
     let g2 = build_graph labelMap thn in
     let g3 = build_graph labelMap els in
     add_edges g1.last g2.first;
     add_edges g1.last g3.first;
     {first = g1.first ; last = List.append g2.last g3.last}

  (* TODO: simplify this *)
  | App (_, f, args) ->
     let g1 = build_graph labelMap f in
     let g_list = List.map (fun(arg : exp) -> build_graph labelMap arg)
                           args
     in 
     let rec walk_args (prev:cfg) (nexts:cfg list) =
       match nexts with
       | [] ->
         prev
       | f :: l  -> 
          add_edges prev.last f.first;
          walk_args f l
     in
     let last_cfg = walk_args g1 g_list in 
     { first = g1.first ; last = last_cfg.last }

  | Let (_, id, e, body) ->
     let g1 = build_graph labelMap e in
     let g2 = build_graph labelMap body in
     add_edges g1.last g2.first;
     { first = g1.first ; last = g2.last }

  | Rec (_, id, e, body) ->
     let g1 = build_graph labelMap e in
     let g2 = build_graph labelMap body in
     add_edges g1.last g2.first;
     { first = g1.first ; last = g2.last }

  | Label (pos, id, body) -> (* the id is a string *)
     let g1 = build_graph labelMap (Id(pos, id)) in
     let new_labelMap = StringMap.add id g1 labelMap in
     let g2 = build_graph new_labelMap body in
     (* flow from body to ret *)
     add_edges g2.last g1.first;
     { first = g2.first ; last = g1.last }

  | Break (pos, id, body) ->
     let g2 = build_graph labelMap body in
     let return_node = StringMap.find id labelMap in
     (* ret id -> cfg *)
     add_edges g2.last return_node.first;
     (* comes into body, goes out from ret id *)
     { first = g2.first; last = return_node.last }

  (* XXX: Potentially have edges from raise to try/catch and to try/finally. *)
  | TryCatch (_, body, catch) ->
     let g1 = build_graph labelMap body in
     let g2 = build_graph labelMap catch in
     {first = g1.first; last = List.append g1.last g2.last}

  | TryFinally (_, body, fin) ->
     let g1 = build_graph labelMap body in
     let g2 = build_graph labelMap fin in
     add_edges g1.last g2.first;
     {first = g1.first; last = g2.last}

  | Throw (_, e) -> build_graph labelMap e
  | Lambda (_, id_list, body) -> build_graph labelMap body
  | Eval (_, e, bindings) ->
     let g1 = build_graph labelMap e in
     let g2 = build_graph labelMap bindings in
     add_edges g1.last g2.first;
     {first = g1.first; last = g2.last}
  | Hint (_, _, e) -> build_graph labelMap e

(* use the map:
let m = StringMap.empty;;
let m = StringMap.add id node m;;
let m = StringMap.add id1 node1 m;;
 *)
