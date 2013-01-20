module GC = Ljs_gc
module P = Prelude
module S = Ljs_syntax
module ST = Store
module V = Ljs_values
module LocSet = Store.LocSet

type id = string

(* CESK machine-specific continuations *)
type kont =
  | Mt
  | SetBang of ST.loc * kont
  | GetAttr  of S.pattr * S.exp * kont
  | GetAttr2 of S.pattr * V.value * kont
  | SetAttr  of S.pattr * S.exp * S.exp * kont
  | SetAttr2 of S.pattr * S.exp * V.value * kont
  | SetAttr3 of S.pattr * V.value * V.value * kont
  | GetObjAttr of S.oattr * kont
  | SetObjAttr  of S.oattr * S.exp * kont
  | SetObjAttr2 of S.oattr * V.value * kont
  | GetField  of P.Pos.t * S.exp * S.exp * V.env * kont
  | GetField2 of P.Pos.t * S.exp * V.value * V.env * kont
  | GetField3 of P.Pos.t * V.value * V.value * V.env * kont
  | GetField4 of V.env * kont
  | SetField  of P.Pos.t * S.exp * S.exp * S.exp * V.env * kont
  | SetField2 of P.Pos.t * S.exp * S.exp * V.value * V.env * kont
  | SetField3 of P.Pos.t * S.exp * V.value * V.value * V.env * kont
  | SetField4 of P.Pos.t * V.value * V.value * V.value * V.env * kont
  | SetField5 of V.env * kont
  | OwnFieldNames of kont
  | DeleteField  of P.Pos.t * S.exp * kont
  | DeleteField2 of P.Pos.t * V.value * kont
  | OpOne of string * kont
  | OpTwo  of string * S.exp * kont
  | OpTwo2 of string * V.value * kont
  | If of V.env * S.exp * S.exp * kont
  | App  of P.Pos.t * V.env * S.exp list * kont
  | App2 of P.Pos.t * V.value * V.env * V.value list * S.exp list * kont
  | App3 of V.env * kont
  | Seq of S.exp * kont
  | Let of id * S.exp * kont
  | Let2 of V.env * kont
  | Rec of ST.loc * S.exp * kont
  | Label of id * V.env * kont
  | Break of id * kont
  | TryCatch  of P.Pos.t * S.exp * V.env * kont
  | TryCatch2 of P.Pos.t * V.value * V.env * kont
  | TryCatch3 of V.env * kont
  | TryFinally  of S.exp * V.env * kont
  | TryFinally2 of exn * V.env * kont
  | Throw of kont
  | Eval  of P.Pos.t * S.exp * kont
  | Eval2 of P.Pos.t * V.value * kont
  | Eval3 of kont
  | Hint of kont
  | Object  of (string * S.prop) list * kont
  | Object2 of V.attrsv * (string * S.prop) list *
      (string * V.propv) list * kont
  | Attrs of string * (string * S.exp) list * (string * V.value) list *
      string * bool * kont
  | DataProp of string * bool * bool * bool * kont
  | AccProp  of string * S.exp * bool * bool * kont
  | AccProp2 of string * V.value * bool * bool * kont

(* for control flow *)
let shed k = match k with
  | SetBang (_, k) -> k
  | GetAttr (_, _, k) -> k
  | GetAttr2 (_, _, k) -> k
  | SetAttr (_, _, _, k) -> k
  | SetAttr2 (_, _, _, k) -> k
  | SetAttr3 (_, _, _, k) -> k
  | GetObjAttr (_, k) -> k
  | SetObjAttr (_, _, k) -> k
  | SetObjAttr2 (_, _, k) -> k
  | GetField (_, _, _, _, k) -> k
  | GetField2 (_, _, _, _, k) -> k
  | GetField3 (_, _, _, _, k) -> k
  | GetField4 (_, k) -> k
  | SetField (_, _, _, _, _, k) -> k
  | SetField2 (_, _, _, _, _, k) -> k
  | SetField3 (_, _, _, _, _, k) -> k
  | SetField4 (_, _, _, _, _, k) -> k
  | SetField5 (_, k) -> k
  | OwnFieldNames k -> k
  | DeleteField (_, _, k) -> k
  | DeleteField2 (_, _, k) -> k
  | OpOne (_, k) -> k
  | OpTwo (_, _, k) -> k
  | OpTwo2 (_, _, k) -> k
  | Mt -> k
  | If (_, _, _, k) -> k
  | App (_, _, _, k) -> k
  | App2 (_, _, _, _, _, k) -> k
  | App3 (_, k) -> k
  | Seq (_, k) -> k
  | Let (_, _, k) -> k
  | Let2 (_, k) -> k
  | Rec (_, _, k) -> k
  | Break (_, k) -> k
  | TryCatch (_, _, _, k) -> k
  | TryCatch2 (_, _, _, k) -> k
  | TryCatch3 (_, k) -> k
  | TryFinally (_, _, k) -> k
  | TryFinally2 (_, _, k) -> k
  | Throw k -> k
  | Eval (_, _, k) -> k
  | Eval2 (_, _, k) -> k
  | Eval3 k -> k
  | Hint k -> k
  | Object (_, k) -> k
  | Object2 (_, _, _, k) -> k
  | Attrs (_, _, _, _, _, k) -> k
  | DataProp (_, _, _, _, k) -> k
  | AccProp (_, _, _, _, k) -> k
  | AccProp2 (_, _, _, _, k) -> k
  | Label (_, _, k) -> k

let string_of_kont k = match k with
  | SetBang (_, _) -> "k.setbang"
  | GetAttr (_, _, _) -> "k.getattr"
  | GetAttr2 (_, _, _) -> "k.getattr2"
  | SetAttr (_, _, _, _) -> "k.setattr"
  | SetAttr2 (_, _, _, _) -> "k.setattr2"
  | SetAttr3 (_, _, _, _) -> "k.setattr3"
  | GetObjAttr (_, _) -> "k.getobjattr"
  | SetObjAttr (_, _, _) -> "k.setobjattr"
  | SetObjAttr2 (_, _, _) -> "k.setobjattr2"
  | GetField (_, _, _, _, _) -> "k.getfield"
  | GetField2 (_, _, _, _, _) -> "k.getfield2"
  | GetField3 (_, _, _, _, _) -> "k.getfield3"
  | GetField4 (_, _) -> "k.getfield4"
  | SetField (_, _, _, _, _, _) -> "k.setfield"
  | SetField2 (_, _, _, _, _, _) -> "k.setfield2"
  | SetField3 (_, _, _, _, _, _) -> "k.setfield3"
  | SetField4 (_, _, _, _, _, _) -> "k.setfield4"
  | SetField5 (_, _) -> "k.setfield5"
  | OwnFieldNames _ -> "k.ownfieldnames"
  | DeleteField (_, _, _) -> "k.deletefield"
  | DeleteField2 (_, _, _) -> "k.deletefield2"
  | OpOne (_, _) -> "k.opone"
  | OpTwo (_, _, _) -> "k.optwo"
  | OpTwo2 (_, _, _) -> "k.optwo2"
  | Mt -> "k.mt"
  | If (_, _, _, _) -> "k.if"
  | App (_, _, _, _) -> "k.app"
  | App2 (_, _, _, _, _, _) -> "k.app2"
  | App3 (_, _) -> "k.app3"
  | Seq (_, _) -> "k.seq"
  | Let (_, _, _) -> "k.let"
  | Let2 (_, _) -> "k.let2"
  | Rec (_, _, _) -> "k.rec"
  | Break (label, _) -> "k.break: "^label
  | TryCatch (_, _, _, _) -> "k.trycatch"
  | TryCatch2 (_, _, _, _) -> "k.trycatch2"
  | TryCatch3 (_, _) -> "k.trycatch3"
  | TryFinally (_, _, _) -> "k.tryfinally"
  | TryFinally2 (_, _, _) -> "k.tryfinally2"
  | Throw _ -> "k.throw"
  | Eval (_, _, _) -> "k.eval"
  | Eval2 (_, _, _) -> "k.eval2"
  | Eval3 _ -> "k.eval3"
  | Hint _ -> "k.hint"
  | Object (_, _) -> "k.object"
  | Object2 (_, _, _, _) -> "k.object2"
  | Attrs (_, _, _, _, _, _) -> "k.attrs"
  | DataProp (_, _, _, _, _) -> "k.dataprop"
  | AccProp (_, _, _, _, _) -> "k.accprop"
  | AccProp2 (_, _, _, _, _) -> "k.accprop2"
  | Label (_, _, _) -> "k.label"


let locs_of_values vs a =
  List.fold_left (fun a n -> (GC.locs_of_value n)::a) a vs

let locs_of_opt ox locs_of_x = match ox with
  | Some v -> locs_of_x v
  | None -> ST.LocSet.empty

let locs_of_opt_val ov = locs_of_opt ov GC.locs_of_value

let locs_of_propv pv = match pv with
  | V.Data ({ V.value=v }, _, _) -> GC.locs_of_value v
  | V.Accessor ({ V.getter=gv; V.setter=sv }, _, _) ->
    LocSet.union (GC.locs_of_value gv) (GC.locs_of_value sv)

let locs_of_propvs pvs a = List.fold_left (fun a (_, n) -> (locs_of_propv n)::a) a pvs

let locs_of_attrsv av =
  let { V.code=ov; V.proto=v; V.primval=ov' } = av in
  LocSet.unions [locs_of_opt_val ov; GC.locs_of_value v; locs_of_opt_val ov']

let rec locs_of_kont ko : LocSet.t = match ko with
  | SetBang (l, k) -> LocSet.union (LocSet.singleton l) (locs_of_kont k)
  | GetAttr (_, _, k) -> locs_of_kont k
  | GetAttr2 (_, v, k) -> LocSet.union (GC.locs_of_value v) (locs_of_kont k)
  | SetAttr (_, _, _, k) -> locs_of_kont k
  | SetAttr2 (_, _, v, k) -> LocSet.union (GC.locs_of_value v) (locs_of_kont k)
  | SetAttr3 (_, v1, v2, k) ->
    LocSet.unions [GC.locs_of_value v1; GC.locs_of_value v2; locs_of_kont k]
  | GetObjAttr (_, k) -> locs_of_kont k
  | SetObjAttr (_, _, k) -> locs_of_kont k
  | SetObjAttr2 (_, v, k) -> LocSet.union (GC.locs_of_value v) (locs_of_kont k)
  | GetField (_, _, _, e, k) -> LocSet.union (GC.locs_of_env e) (locs_of_kont k)
  | GetField2 (_, _, v, e, k) -> LocSet.unions [GC.locs_of_value v; GC.locs_of_env e; locs_of_kont k]
  | GetField3 (_, v1, v2, e, k) ->
    LocSet.unions [GC.locs_of_value v1; GC.locs_of_value v2; GC.locs_of_env e; locs_of_kont k]
  | GetField4 (e, k) -> LocSet.union (GC.locs_of_env e) (locs_of_kont k)
  | SetField (_, _, _, _, e, k) -> LocSet.union (GC.locs_of_env e) (locs_of_kont k)
  | SetField2 (_, _, _, v, e, k) ->
    LocSet.unions [GC.locs_of_value v; GC.locs_of_env e; locs_of_kont k]
  | SetField3 (_, _, v1, v2, e, k) ->
    LocSet.unions [GC.locs_of_value v1; GC.locs_of_value v2; GC.locs_of_env e; locs_of_kont k]
  | SetField4 (_, v1, v2, v3, e, k) ->
    LocSet.unions [GC.locs_of_value v1; GC.locs_of_value v2; GC.locs_of_value v3; GC.locs_of_env e;
                   locs_of_kont k]
  | SetField5 (e, k) -> LocSet.union (GC.locs_of_env e) (locs_of_kont k)
  | OwnFieldNames k -> locs_of_kont k
  | DeleteField (_, _, k) -> locs_of_kont k
  | DeleteField2 (_, v, k) -> LocSet.union (GC.locs_of_value v) (locs_of_kont k);
  | OpOne (_, k) -> locs_of_kont k
  | OpTwo (_, _, k) -> locs_of_kont k
  | OpTwo2 (_, v, k) -> LocSet.union (GC.locs_of_value v) (locs_of_kont k)
  | If (e, _, _, k) -> LocSet.union (GC.locs_of_env e) (locs_of_kont k)
  | App (_, e, _, k) -> LocSet.union (GC.locs_of_env e) (locs_of_kont k)
  | App2 (_, v, e, vs, _, k) ->
    LocSet.unions (locs_of_values vs [GC.locs_of_value v; GC.locs_of_env e; locs_of_kont k])
  | App3 (e, k) -> LocSet.union (GC.locs_of_env e) (locs_of_kont k)
  | Seq (_, k) -> locs_of_kont k
  | Let (_, _, k) -> locs_of_kont k
  | Let2 (_, k) -> locs_of_kont k
  | Rec (l, _, k) -> LocSet.add l (locs_of_kont k)
  | Break (_, k) -> locs_of_kont k
  | TryCatch (_, _, e, k) -> LocSet.union (GC.locs_of_env e) (locs_of_kont k)
  | TryCatch2 (_, v, e, k) -> LocSet.unions [GC.locs_of_value v; GC.locs_of_env e; locs_of_kont k]
  | TryCatch3 (e, k) -> LocSet.union (GC.locs_of_env e) (locs_of_kont k)
  | TryFinally (_, e, k) -> LocSet.union (GC.locs_of_env e) (locs_of_kont k)
  | TryFinally2 (_, e, k) -> LocSet.union (GC.locs_of_env e) (locs_of_kont k)
  | Throw k -> locs_of_kont k
  | Eval (_, _, k) -> locs_of_kont k
  | Eval2 (_, _, k) -> locs_of_kont k
  | Eval3 k -> locs_of_kont k
  | Hint k -> locs_of_kont k
  | Object (_, k) -> locs_of_kont k
  | Object2 (attrsv, _, propvs, k) ->
    LocSet.unions (locs_of_propvs propvs [locs_of_attrsv attrsv; locs_of_kont k])
  | Attrs (_, _, nvs, _, _, k) ->
    LocSet.unions (List.fold_left (fun a (_, n) -> (GC.locs_of_value n)::a) [locs_of_kont k] nvs)
  | DataProp (_, _, _, _, k) -> locs_of_kont k
  | AccProp (_, _, _, _, k) -> locs_of_kont k
  | AccProp2 (_, v, _, _, k) -> LocSet.union (GC.locs_of_value v) (locs_of_kont k)
  | Label (_, e, k) -> LocSet.union (GC.locs_of_env e) (locs_of_kont k)
  | Mt -> LocSet.empty
