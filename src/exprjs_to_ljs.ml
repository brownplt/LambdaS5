open Prelude

module E = Exprjs_syntax
module S = Es5_syntax

let rec exprjs_to_ljs (e : E.expr) : S.exp = match e with
  | E.True (p) -> S.True (p)
  | E.False (p) -> S.False (p)
  | E.Num (p, n) -> S.Num (p, n)
  | E.Undefined (p) -> S.Undefined (p)
  | E.Null (p) -> S.Null (p)
  | E.String (p, s) -> S.String (p, s)
  | E.IdExpr (p, nm) -> S.Id (p, nm)
  | E.BracketExpr (p, l, r) -> 
    let o = exprjs_to_ljs l
    and f = exprjs_to_ljs r in
    S.GetField (p, o, f, S.Null (p)) (* Args object is null for now *)
  | E.ObjectExpr (p, pl) ->
    let rec ejsprop_to_sprop pr = match pr with
      | E.Data (e) -> 
          let rec v = exprjs_to_ljs e
          and d = { S.value = v; S.writable = true; } in
          S.Data (d, true, true)
      | E.Getter (nm, e) -> failwith "getters unimplemented"
      | E.Setter (nm, e) -> failwith "setters unimplemented"
    and tuple_to_prop t = match t with
      (p, s, pr) -> (s, ejsprop_to_sprop pr)
    and form_props props = match props with
      | [] -> []
      | first :: rest -> (tuple_to_prop first) :: form_props rest in
    S.Object (p, S.d_attrs, form_props pl)
  | E.SeqExpr (p, e1, e2) -> S.Seq (p, exprjs_to_ljs e1, exprjs_to_ljs e2)
  | E.VarDeclExpr (p, id, e) -> S.SetBang (p, id, exprjs_to_ljs e)
  (* TODO: There's a comment in exprjs_syntax re: FuncStmtExpr.  Not sure
   * what it means. *)
  | E.FuncStmtExpr (p, nm, args, body) ->
    let rec f = exprjs_to_ljs body
    and l = S.Lambda (p, args, f) in
    S.Rec (p, nm, l, f)
  | _ -> failwith "unimplemented exprjs type"
