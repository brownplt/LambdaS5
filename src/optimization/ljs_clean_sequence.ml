open Ljs_opt
open Ljs_syntax
module EU = Exp_util

let cutting_flow (exp : exp) =
  (* to decide whether the exp will cut the flow. Expressions
     like break, throw will cut the flow
  *)
  match exp with
  | Break (_, _, _) -> true
  | Throw (_, _) -> true
  | _ -> false

let rec clean_sequence (exp : exp) : exp =
  match exp with
  | Seq (p, e1, e2) ->
    let new_e1 = clean_sequence e1 in
    if cutting_flow new_e1 then
      new_e1
    else if not (EU.has_side_effect new_e1) then
      clean_sequence e2
    else
      let new_e2 = clean_sequence e2 in
      Seq (p, new_e1, new_e2)
  | _ -> optimize clean_sequence exp
