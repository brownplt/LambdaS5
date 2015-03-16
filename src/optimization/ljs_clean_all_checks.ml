open Ljs_opt
open Ljs_syntax

let is_internal_checks exp = match exp with
  | App (_, Id (_, "%TypeError"), _) -> true
  | _ -> false
  
let rec clean_all_checks (exp : exp) : exp =
  match exp with
  | If (p, tst, thn, els) ->
    if is_internal_checks thn then
      clean_all_checks els
    else if is_internal_checks els then
      clean_all_checks thn
    else
      If (p, (clean_all_checks tst), (clean_all_checks thn), (clean_all_checks els))
  | _ -> optimize clean_all_checks exp

