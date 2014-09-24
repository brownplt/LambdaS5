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

let alias_elimination (e : exp) : exp =
  let rec elimination_rec (e : exp) (env : env) : exp =
    let eliminate (e : exp) = elimination_rec e env in
    match e with
    | Undefined _ 
    | Null _ 
    | String (_, _)
    | Num (_, _)
    | True _ 
    | False _ -> e
    | Id (_, id) -> begin try IdMap.find id env with _ -> e end
    | Let (p, x, xexp, body) ->
       let x_v = elimination_rec xexp env in
       (* env should change: 
            1. anything maps to x should be removed from env;
            2. anything that x maps to in env should be removed.
        *)
       let env = IdMap.remove x env in
       let env = remove_id_value x env in
       begin
       (* look at x_v. we are only interested in situation that x_v is an id *)
       match x_v with
       | Id (_, v_id) -> 
          (* if x, or v_id gets mutated in body, x should not be replaced with v_id in body *)
          if EU.mutate_var x body || EU.mutate_var v_id body then
            Let (p, x, x_v, elimination_rec body env)
          else 
            let env = IdMap.add x x_v env in
            Let (p, x, x_v, elimination_rec body env)
       | _ -> Let (p, x, x_v, elimination_rec body env)
       end 
    | Rec (p, x, xexp, body) ->
       let env = IdMap.remove x env in
       let x_v = elimination_rec xexp env in
       let env = remove_id_value x env in
       Rec (p, x, x_v, elimination_rec body env)
    | Lambda (p,xs,body) ->
       let rec remove_list (lst : id list) env = match lst with
         | [] -> env
         | fst :: rest -> remove_list rest (remove_id_value fst env) in
       let env = remove_list xs env in
       let env = IdMap.filter (fun var _->not (List.mem var xs)) env in
       Lambda (p, xs, elimination_rec body env)
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
    | Eval (_,_,_)
    | Hint (_,_,_)
      -> optimize eliminate e

  in 
  elimination_rec e IdMap.empty
