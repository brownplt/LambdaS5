open Ljs_opt
open Ljs_syntax

let is_internal_checks exp = match exp with
  | App (_, Id (_, "%TypeError"), _) -> true
  | _ -> false
  
let rec no_checks (exp : exp) : exp =
  match exp with
  | If (_, tst, thn, els) when is_internal_checks thn ->
    no_checks els
  | _ -> optimize no_checks exp

