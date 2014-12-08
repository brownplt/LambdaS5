open Ljs_opt
open Ljs_syntax

let is_internal_checks exp = match exp with
  | App (_, Id (_, "%TypeError"), _) -> true
  | _ -> false
  
let rec no_checks (exp : exp) : exp =
  match exp with
  | If (p, tst, thn, els) ->
    if is_internal_checks thn then
      no_checks els
    else if is_internal_checks els then
      no_checks thn
    else
      If (p, (no_checks tst), (no_checks thn), (no_checks els))
  | _ -> optimize no_checks exp

