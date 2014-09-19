open Prelude
open Ljs_syntax
open Ljs_opt
module EU = Exp_util

type env = exp IdMap.t 

let rec prim_propagation (e : exp) : exp =
  let empty_env = IdMap.empty in
  let rec propagation_rec (e : exp) (env : env) : exp = 
    let propagate exp = propagation_rec exp env in
    match e with 
    | Undefined _ 
    | Null _
    | String (_,_)
    | Num (_,_)
    | True _
    | False _ -> e
    | Id (p, x) ->
       begin
         try IdMap.find x env with _ -> e
       end 
    | Let (p, x, x_v, body) ->
       let x_v = propagation_rec x_v env in
       let is_const = EU.is_prim_constant x_v in 
       (* if x will be mutated or x_v is not prim constant *)
       if EU.mutate_var x body || not is_const then
         let env = IdMap.remove x env in
         Let (p,x,x_v, propagation_rec body env)
       else 
         let env = IdMap.add x x_v env in
         Let (p, x, x_v, propagation_rec body env)
    | Rec (p, x, x_v, body) ->
       let x_v = propagation_rec x_v env in
       let env = IdMap.remove x env in
       Rec (p, x, x_v, propagation_rec body env)
    | Lambda (p, xs, body) ->
       (* remove each x in xs from env *)
       let filtered_env = 
         IdMap.filter (fun x _->not (List.mem x xs) ) env in
       Lambda (p, xs, propagation_rec body filtered_env)
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
    | Eval (_,_,_)
    | Hint (_,_,_) -> optimize propagate e in
  propagation_rec e empty_env
