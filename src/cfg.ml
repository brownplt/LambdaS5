open Prelude
open Es5_cps
open Graph

type vert = cps_exp
module Vert_COMPARABLE = struct
  type t = vert
  let compare t1 t2 = Pervasives.compare t1 t2
  let hash t = Hashtbl.hash t
  let equal t1 t2 = (t1 = t2)
end

module Es5_ORDERED_TYPE_DFT = struct
  type t = Es5_cps.cps_exp
  let default = AppRetCont ("dummy", Id(dummy_pos, "no-op"))
  let compare t1 t2 = Pervasives.compare t1 t2
end

module G = Persistent.Digraph.ConcreteBidirectionalLabeled (Vert_COMPARABLE) (Es5_ORDERED_TYPE_DFT)

let build expr =
  let v = expr in 
  let cfg = G.add_vertex G.empty v in
  let rec build_exp (g : G.t) (entry : vert) (exp : Es5_cps.cps_exp) : (G.t * vert) =
    match exp with
  | LetValue(pos, id, value, exp) -> (g, entry)
  | RecValue(pos, id, value, exp) -> (g, entry)
  | LetPrim(pos, id, prim, exp) -> (g, entry)
  | LetRetCont(ret, arg, retBody, exp) -> (g, entry)
  | LetExnCont(exn, arg, label, exnBody, exp) -> (g, entry)
  | GetField(pos, obj, field, args, ret, exn) -> (g, entry)
  | SetField(pos, obj, field, value, args, ret, exn) -> (g, entry)
  | If(pos, cond, trueBranch, falseBranch) -> (g, entry)
  | AppFun(pos, func, ret, exn, args) -> (g, entry)
  | AppRetCont(ret, arg) -> (g, entry)
  | AppExnCont(exn, arg, label) -> (g, entry)
  | Eval(pos, eval) -> (g, entry) in
  fst (build_exp cfg v expr)

let cpsv_to_string cps_value = 
  Es5_cps_pretty.value cps_value Format.str_formatter; 
  Format.flush_str_formatter()
module Display = struct
  include G
  let vertex_name v = match v with
  | LetValue(pos, id, value, exp) -> "LetValue(" ^ id ^ ")"
  | RecValue(pos, id, value, exp) -> "RecValue(" ^ id ^ ")"
  | LetPrim(pos, id, prim, exp) -> "LetPrim(" ^ id ^ ")"
  | LetRetCont(ret, arg, retBody, exp) -> "LetRet(" ^ ret ^ ")"
  | LetExnCont(exn, arg, label, exnBody, exp) -> "LetExn(" ^ exn ^ ")"
  | GetField(pos, obj, field, args, ret, exn) -> "GetField(" ^ (cpsv_to_string obj) 
    ^ "[" ^ (cpsv_to_string field) ^ "])"
  | SetField(pos, obj, field, value, args, ret, exn) -> "SetField(" ^ (cpsv_to_string obj)
    ^ "[" ^ (cpsv_to_string field) ^ "])"
  | If(pos, cond, trueBranch, falseBranch) -> "If(" ^ (cpsv_to_string cond) ^ ")"
  | AppFun(pos, func, ret, exn, args) -> "App(" ^ (cpsv_to_string func) ^ ")"
  | AppRetCont(ret, arg) -> "Ret(" ^ ret ^ ")"
  | AppExnCont(exn, arg, label) -> "Exn(" ^ exn ^ ", " ^ label ^ ")"
  | Eval(pos, eval) -> "Eval"
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
