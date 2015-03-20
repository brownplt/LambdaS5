open Prelude
open Ljs_syntax
open Ljs_opt
module EU = Exp_util

(* map id -> id *)
type env = exp IdMap.t 

(* remove anything that maps to Id(pos, id) from env *)
let remove_id_value (id : id) (env : env) : env =
  let not_the_id (idstr : id) (idexp : exp) = match idexp with
    | Id (_, id) -> not (idstr = id)
    | _ -> failwith "[remove_id_value] how can it not be Id?"
  in 
  IdMap.filter (fun _ v->not_the_id id v) env

(* def_set stores the identifiers that are modified by assignment
   somewhere in their scopes, so any identifier that maps to such an
   id should not be appied copy propagation. This is a really
   conservative approximation.
*)
let propagate_copy (e : exp) : exp =
  let rec propagate_rec (e : exp) (env : env) (def_set : IdSet.t) : exp =
    let propagate (e : exp) = propagate_rec e env def_set in
    match e with
    | Undefined _ 
    | Null _ 
    | String (_, _)
    | Num (_, _)
    | True _ 
    | False _ -> e
    | Id (_, id) -> begin try IdMap.find id env with _ -> e end
    | Let (p, x, xexp, body) ->
       let x_v = propagate_rec xexp env def_set in
       (* env should change: 
            1. anything maps to x should be removed from env;
            2. anything that x maps to in env should be removed.
        *)
       let env = IdMap.remove x env in
       let env = remove_id_value x env in
       (* whatever x maps to, if x is mutated in its scope, the copy of x should
          not be propagated *)
       let x_is_assigned : bool = EU.mutate_var x body in
       let def_set = if x_is_assigned 
         then 
           IdSet.add x def_set 
         else if IdSet.mem x def_set then
           IdSet.remove x def_set
         else def_set in
       begin
         (* look at x_v. we are only interested in situation that x_v is an id *)
         match x_v with
         | Id (_, v_id) ->
           (* if x, or v_id gets mutated in body, x should not be replaced with v_id in body *)
           if x_is_assigned || (IdSet.mem v_id def_set) then
             Let (p, x, x_v, propagate_rec body env def_set)
           else 
             let env = IdMap.add x x_v env in
             Let (p, x, x_v, propagate_rec body env def_set)
         | _ -> Let (p, x, x_v, propagate_rec body env def_set)
       end 
    | Rec (p, x, xexp, body) ->
       let env = IdMap.remove x env in
       let def_set = IdSet.remove x def_set in
       let x_v = propagate_rec xexp env def_set in
       let env = remove_id_value x env in
       if (EU.mutate_var x xexp) || (EU.mutate_var x body) then
         let def_set = IdSet.add x def_set in
         Rec (p, x, x_v, propagate_rec body env def_set)
       else
         let def_set = IdSet.remove x def_set in
         Rec (p, x, x_v, propagate_rec body env def_set)
    | Lambda (p,xs,body) ->
       let rec remove_list (lst : id list) env = match lst with
         | [] -> env
         | fst :: rest -> remove_list rest (remove_id_value fst env) in
       let env = remove_list xs env in
       let env = IdMap.filter (fun var _->not (List.mem var xs)) env in
       (* decide for each parameter whether it is modified in body:
          - if it does, add to def_set
          - if it does not, remove from def_set
       *)
       let def_set = List.fold_left
           (fun set x-> if EU.mutate_var x body then
               IdSet.add x set
             else
               IdSet.remove x set)
           def_set xs in
       Lambda (p, xs, propagate_rec body env def_set)
    | Object (_,_,_) 
    | GetAttr (_, _, _, _)
    | GetObjAttr (_, _, _)
    | GetField (_, _, _, _)
    | Op1 (_,_,_)
    | Op2 (_,_,_,_)
    | If (_, _, _, _)
    | SetAttr (_,_,_,_,_)
    | SetObjAttr (_,_,_,_)
    | SetField (_,_,_,_,_)
    | DeleteField (_, _, _) 
    | OwnFieldNames (_,_)
    | SetBang (_,_,_)
    | App (_,_,_) 
    | Seq (_,_,_) 
    | Label (_,_,_)
    | Break (_,_,_)
    | TryCatch (_,_,_)
    | TryFinally (_,_,_)
    | Throw (_,_)
    | Hint (_,_,_)
      -> optimize propagate e

  in 
  propagate_rec e IdMap.empty IdSet.empty
