open Prelude
open Ljs_opt
open Ljs_syntax
open Debug
open Exp_util

let debug_on = false

let dprint = Debug.make_debug_printer ~on:debug_on "restore func"


(* if match successfully, this function will trim off
   the function object's properties and leave the function body
   and related let bindings.
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
    | Let (p, x, x_v, body) -> begin match get_js_func x_v with
        | Some code -> Some code
        | None ->
          (*this let binding is not what we are looking for, 
            keep it and continue looking. *)
          match get_func body with
          | Some code ->
            Some (Let (p, x, x_v, code))
          | None -> None
      end
    | exp ->
      get_js_func exp
  in
  match exp with
  | Let (_, x, x_v, body) when is_proto_obj x_v ->
    (* function object always starts with prototype and then lambda *)
    let _ = dprint "find prototype, continue matching\n" in
    get_func body
  | exp ->
    let _ = dprint (sprintf "entry not matched. it cannot be converted to procedure.\n" ) in
    None
      
(* env stores the id -> lambda code *)
type env = exp IdMap.t
  
(* the entry of this function normally accepts a Lambda, if the Lambda ever uses
   'this' keyword, the expression is not this free. The exception is that function contains
   '%resolveThis', which will use 'this'
*)
let rec this_free (exp : exp) : bool =
  let rec search_this (exp : exp) =
    match exp with
    | App (_, Id (_, "%resolveThis"), _) -> true
    | Id (_, "%this") -> false
    | Lambda (_, xs, body) when List.mem "%this" xs -> true
    | _ -> List.for_all search_this (child_exps exp)
  in
  match exp with
  | Lambda (_, xs, body) when List.mem "%this" xs -> search_this body
  | Let (_, _, _, body) -> (* jump over let bindings to reach to lambda *)
    this_free body
  | _ -> failwith (sprintf "this_free should be called only on a Lambda that contains 'this', now it gets %s" (ljs_str exp))

(* This transformation will restore function objects to procedures. We
   cannot decide which function is used as constructor. One method
   that makes this transformation a little bit useful is to only
   restore functions that do not use 'this' keyword.

   NOTE: to make this transformation somehow works, we have to modify
   ljs_delta.ml to let 'typeof' prim returns "function" when it gets a
   closure.
*)

let restore_function exp : exp =
  let rec restore_rec exp env : exp =
    let restore e = restore_rec e env in
    match exp with
    | Let (p, x, x_v, body) ->
      begin match get_lambda exp with
        | Some (code) ->
          let _ = dprint (sprintf "find patterns, procedure found: %s\n" (ljs_str code)) in
          if this_free code then
              restore code
          else 
              Let (p, x, restore x_v, restore body)

        | _ ->
          let _ = dprint (sprintf "for let(%s=...), no patterns found\n" x) in
          Let (p, x, restore x_v, restore body)
      end
    | _ -> optimize restore exp
  in
  restore_rec exp IdMap.empty

