open Prelude

module E = Exprjs_syntax
module S = Es5_syntax

let rec exprjs_to_ljs (e : E.expr) : S.exp = match e with
  | _ -> S.Null (dummy_pos)
