open Prelude

module E = Exprjs_syntax
module S = Es5_syntax

let rec exprjs_to_ljs (e : E.expr) : S.exp = match e with
  | E.Num (p, n) -> S.Num (p, n)
  | E.IdExpr (p, nm) -> S.Id (p, nm)
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
  | _ -> failwith "unimplemented exprjs type"
