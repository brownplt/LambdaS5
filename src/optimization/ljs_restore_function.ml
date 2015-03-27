open Prelude
open Ljs_opt
open Ljs_syntax
open Debug
open Exp_util


(* if match successfully, this function will return
  exp in #code field
*)
let rec get_lambda exp : exp option =
  (* if exp is an object whose #code is not null *)
  let is_proto_obj exp : bool = match exp with
    | Object (_, {proto=Some (Id (_, "%ObjectProto")); klass="Object"}, _) -> true
    | _ -> false
  in
  let get_js_func exp : exp option = match exp with
    | Object (_, {code=Some code}, _) -> Some code
    | _ -> None
  in
  let rec get_func exp : exp option = match exp with
    | Let (_, _, x_v, body) -> begin match get_js_func x_v with
        | Some code -> Some code
        | None -> get_func body
      end
    | _ -> None
  in
  match exp with
  | Let (_, x, x_v, body) when is_proto_obj x_v ->
    (* function object always starts with prototype and then lambda *)
    (*let _ = printf "get proto, continue\n%!" in*)
    get_func body
  | _ -> None
      
(* env stores the id -> lambda code *)
type env = exp IdMap.t
  
let restore_function exp : exp =
  let rec restore_rec exp env : exp =
    let restore e = restore_rec e env in
    match exp with
    | Let (p, x, x_v, body) ->
      begin match get_lambda x_v with
        | Some (code) ->
          Let (p, x, restore code, restore body)
        | None ->
          Let (p, x, restore x_v, restore body)
      end
    | _ -> optimize restore exp
  in
  restore_rec exp IdMap.empty
