open Prelude
open Ljs_syntax
open Ljs_opt

(* take out argument declaration exp, and return ordered formal
   parameters *)
let trim_args (exp : exp) : id list * exp =
  let get_args e =
    match e with
    | GetField (_, Id (_, "%args"), String (_, index), _) ->
      begin try
        Some (int_of_string index)
      with
        _ -> None
      end
    | _ -> None
  in
  let get_order (args : (int * id) list) : id list =
    let rec fetch (cur : int) =
      try
        let x = List.assoc cur args in
        x :: fetch (cur+1)
      with
        _ -> []
    in
    fetch 0
  in
  let args : (int * id) list ref = ref [] in
  let rec trim exp : exp =
    match exp with
    | Let (pos, x, xv, body) ->
      begin match get_args xv with
        | Some (index) ->
          args := (index, x) :: !args;
          trim body
        | None ->
          Let (pos, x, xv, trim body)
      end
    | Lambda (_, _, _) -> exp
    | exp -> optimize trim exp
  in
  get_order !args, trim exp

let update_args (old_xs : id list) (new_xs : id list) =
  match old_xs with
  | hd :: tl when hd = "%this" ->
    hd :: new_xs
  | _ -> old_xs
           
let fixed_arity (exp : exp) : exp =
  let rec fixed_formal_parameter (exp : exp) : exp =
    match exp with
    | Lambda (pos, xs, body) ->
      let args, new_body = trim_args body in
      let new_xs = update_args xs args in
      Lambda (pos, new_xs, fixed_formal_parameter new_body)
    | _ ->
      optimize fixed_formal_parameter exp
  in
  let rec fixed_call_site (exp : exp) : exp =
    exp
  in
  let e1 = fixed_formal_parameter exp in
  let e2 = fixed_call_site e1 in
  e2
