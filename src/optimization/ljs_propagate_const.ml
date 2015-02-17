open Prelude
open Ljs_syntax
open Ljs_opt
module EU = Exp_util

type const_pool = exp IdMap.t

(** This phase only propagates primitive constants
    and function constants that are bound by let and have single def
    point. To prevent further bloat the code, function constants must
    be used at most once.

    situation like ``let (a = b)`` is not handled here, even if ``b``
    is a constant. See propagate copy phase.

    A constant object exists in S5, but does not in desugared
    JavaScript code, so this phase does not consider the object case
    neither.

 **)

(* constant lambda contains no free vars. Side effect in the body is fine *)
let is_lambda_constant (e: exp) : bool = match e with
  | Lambda (_, ids, body) ->
     IdSet.is_empty (free_vars e)
  | _ -> false

(* predicate for primitive constant *)
let is_prim_constant (e : exp) : bool = match e with
  | Null _
  | Undefined _
  | Num (_, _)
  | String (_, _)
  | True _
  | False _ -> true
  | _ -> false

let rec propagate_const (e : exp) : exp =
  let empty_const_pool = IdMap.empty in
  let rec propagate_rec (e : exp) (const_pool : const_pool) : exp = 
    let propagate exp = propagate_rec exp const_pool in
    match e with 
    | Undefined _ 
    | Null _
    | String (_,_)
    | Num (_,_)
    | True _
    | False _ -> e
    | Id (p, x) ->
      if IdMap.mem x const_pool then
        IdMap.find x const_pool
      else
        e
    | Let (p, x, x_v, body) ->
      let x_v = propagate_rec x_v const_pool in
      (* if x is not mutated and x_v is a constant that could be
         propagated, either a const primitive or a constant function
         used at most once, do the propagation *)
      if not (EU.mutate_var x body) &&
         (is_prim_constant x_v ||
          (is_lambda_constant x_v && not (EU.multiple_usages x body)))
      then
         let const_pool = IdMap.add x x_v const_pool in
         Let (p, x, x_v, propagate_rec body const_pool)
      else
         let const_pool = IdMap.remove x const_pool in
         Let (p,x,x_v, propagate_rec body const_pool)
    | Rec (p, x, x_v, body) ->
      let x_v = propagate_rec x_v (IdMap.remove x const_pool) in
      (* if x is not mutated and x_v is a const lambda used at most
         once, do the propagation *)
      if not (EU.mutate_var x body) &&
         (is_lambda_constant x_v && not (EU.multiple_usages x body))
      then
         let const_pool = IdMap.add x x_v const_pool in
         Rec (p, x, x_v, propagate_rec body const_pool)
      else
         let const_pool = IdMap.remove x const_pool in
         Rec (p,x,x_v, propagate_rec body const_pool)
    | Lambda (p, xs, body) ->
       (* remove each x in xs from const_pool *)
       let filtered_const_pool = 
         IdMap.filter (fun x _->not (List.mem x xs) ) const_pool in
       Lambda (p, xs, propagate_rec body filtered_const_pool)
    | Object (_, _, _) 
    | GetAttr (_, _, _, _) 
    | SetAttr (_, _, _, _, _) 
    | GetObjAttr (_, _, _) 
    | SetObjAttr (_, _, _, _)
    | GetField (_,_,_,_)
    | SetField (_,_,_,_,_)
    | DeleteField (_,_,_)
    | OwnFieldNames (_,_)
    | SetBang (_,_,_) 
    | Op1 (_,_,_)
    | Op2 (_,_,_,_)
    | If (_,_,_,_)
    | App (_,_,_) 
    | Seq (_,_,_)
    | Label (_,_,_)
    | Break (_,_,_)
    | TryCatch (_,_,_)
    | TryFinally (_,_,_)
    | Throw (_,_)
    | Hint (_,_,_) -> optimize propagate e in
  propagate_rec e empty_const_pool
