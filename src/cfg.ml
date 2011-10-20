open Prelude
open Es5_syntax
open Graph

type vert = 
    | Synth of string
    | TrueBranch of exp
    | FalseBranch of exp
    | AtomicExp of exp
module Vert_COMPARABLE = struct
  type t = vert
  let compare t1 t2 = Pervasives.compare t1 t2
  let hash t = Hashtbl.hash t
  let equal t1 t2 = (t1 = t2)
end

module Es5_ORDERED_TYPE_DFT = struct
  type t = Es5_syntax.exp
  let default = Hint (dummy_pos, "no-op", (Null dummy_pos))
  let compare t1 t2 = Pervasives.compare t1 t2
end

module G = Persistent.Digraph.ConcreteBidirectionalLabeled (Vert_COMPARABLE) (Es5_ORDERED_TYPE_DFT)

let build expr =
  let _ = Es5_cps.cps expr in
  let v = Synth "entry" in 
  let cfg = G.add_vertex G.empty v in
  let rec build_help (g : G.t) (entry : vert) (exp : Es5_syntax.exp) : (G.t * vert) =
    match exp with
    | Null pos -> (g, entry)
    | Undefined pos -> (g, entry)
    | String (pos, str) -> (g, entry)
    | Num (pos, value) -> (g, entry)
    | True pos -> (g, entry)
    | False pos -> (g, entry)
    | Id (pos, id) -> (g, entry)
    | Object (pos, meta, props) -> (g, entry)
    | GetAttr (pos, prop_meta, obj, pname) -> (g, entry)
    | SetAttr (pos, prop_meta, obj, pname, value) -> (g, entry)
    | GetField (pos, obj, field, args) -> (g, entry) 
    | SetField (pos, obj, field, value, args) -> (g, entry) 
    | DeleteField (pos, obj, field) -> (g, entry)
    | SetBang (pos, id, value) -> (g, entry)
    | Op1 (pos, op, exp) -> (g, entry)
    | Op2 (pos, op, left, right) -> (g, entry)
    | If (pos, cond, trueBranch, falseBranch) -> (g, entry)
    | App (pos, func, args) -> (g, entry)
    | Seq (pos, first, second) -> (g, entry)
    | Let (pos, id, value, body) -> (g, entry)
    | Rec (pos, id, value, body) -> (g, entry)
    | Label (pos, label, body) -> (g, entry)
    | Break (pos, label, value) -> (g, entry)
    | TryCatch (pos, body, handler_lam) -> (g, entry)
    | TryFinally (pos, body, exp) -> (g, entry)
    | Throw (pos, value) -> (g, entry)
    | Lambda (pos, args, body) -> (g, entry)
    | Eval (pos, broken) -> (g, entry) 
    | Hint (pos, label, exp) -> (g, entry) in
  fst (build_help cfg v expr)

module Display = struct
  include G
  let vertex_name v = match v with
  | Synth str -> "Synth(" ^ str ^ ")"
  | TrueBranch expr -> "TrueBranch"
  | FalseBranch expr -> "FalseBranch"
  | AtomicExp expr -> "AtomicExp"
  let graph_attributes _ = []
  let default_vertex_attributes _ = []
  let vertex_attributes _ = []
  let default_edge_attributes _ = []
  let edge_attributes _ = []
  let get_subgraph _ = None
end

module D = Graphviz.Dot(Display)

let print_cfg g = 
  D.fprint_graph Format.str_formatter g;
  Format.flush_str_formatter()
