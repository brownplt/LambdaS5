open Prelude
open Ljs_opt
open Ljs_syntax
open Exp_util

let is_internal_checks exp = match exp with
  | App (_, Id (_, "%TypeError"), _) -> true
  | _ -> false
  
let rec clean_assertion_harsh (exp : exp) : exp =
  match exp with
  | If (p, tst, thn, els) ->
    if is_internal_checks thn then
      clean_assertion_harsh els
    else if is_internal_checks els then
      clean_assertion_harsh thn
    else
      If (p, (clean_assertion_harsh tst), (clean_assertion_harsh thn), (clean_assertion_harsh els))
  | TryCatch (p, body, Id(_, "%ErrorDispatch")) ->
    clean_assertion_harsh body
  | _ -> optimize clean_assertion_harsh exp

