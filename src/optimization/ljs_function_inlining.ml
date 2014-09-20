open Prelude
open Ljs_syntax
open Ljs_opt
module EU = Exp_util

type env = exp IdMap.t

(* inline a function is to benefit folding, but it is hard to decide when to inline a function.
   Side effect will prevent folding an expression.*)
let rec function_inlining (e : exp) : exp =
  let empty_env = IdMap.empty in
  let rec inlining_rec e env =
    match e with
    | Undefined _
    | Null _ 
    | String (_, _) 
    | Num (_, _) 
    | True _ 
    | False _ -> e
    | Id (p, x) ->
       begin 
         try 
           IdMap.find x env 
         with _ -> e
       end 
    | App (p, func, args) ->
       (* if args are all constant and func is constant, do function inlining here, *)
       let f = inlining_rec func env in
       let a = List.map (fun x->inlining_rec x env) args in
         App (p, f, a)

    | Let (p, x, xexp, body) ->
       let x_v = inlining_rec xexp env in
       let del_x_from_env_continue curenv =
         let new_env = IdMap.remove x curenv in
         let new_body = inlining_rec body new_env in
         Let (p, x, x_v, new_body)
       in 
       let is_not_lambda e = match e with Lambda (_,_,_) -> false | _ -> true in
       if is_not_lambda x_v || EU.mutate_var x body then
         del_x_from_env_continue env 
       else 
         (* no mutation on x, decide if x_v can be put in env. To be put
            in env, x_v should have no free vars and
            1. if the lambda has side effect but just used once, put it in env
            2. if the lambda does not have side effect, put it in env 
               regardless how many times it's been used. 
            3. if x is just used once in the body, ignore the side effect
          *)
         let no_freevars = IdSet.is_empty (free_vars x_v)  in
         let x_used_manytimes = EU.multiple_usages x body in
         if not no_freevars || 
              (EU.has_side_effect x_v && x_used_manytimes) then
           del_x_from_env_continue env
         else 
           let env = IdMap.add x x_v env in 
           Let (p, x, x_v, (inlining_rec body env))

    | Rec (p, x, xexp, body) ->
       let x_v = inlining_rec xexp env in
       let del_x_from_env_continue curenv =
         let new_env = IdMap.remove x curenv in
         let new_body = inlining_rec body new_env in
         Rec (p, x, x_v, new_body)
       in 
       if EU.mutate_var x body then
         del_x_from_env_continue env 
       else 
         let no_freevars = IdSet.is_empty (free_vars x_v)  in
         if not no_freevars || 
              (EU.has_side_effect x_v && EU.multiple_usages x body) then
           del_x_from_env_continue env
         else 
           let new_env = IdMap.add x x_v env in 
           Rec (p, x, x_v, (inlining_rec body new_env))
    | Lambda (p,xs,body) ->
       let filtered_env = 
         IdMap.filter (fun x _->not (List.mem x xs)) env in
       Lambda (p, xs, inlining_rec body filtered_env)
    | Object (_, _, _) 
    | GetAttr (_, _, _, _) 
    | SetAttr (_, _, _, _, _)
    | GetObjAttr (_, _, _) 
    | SetObjAttr (_, _, _, _) 
    | GetField (_, _, _, _) 
    | SetField (_, _, _, _, _)
    | DeleteField (_, _, _) 
    | OwnFieldNames (_, _) 
    | Op1 (_, _, _) 
    | Op2 (_, _, _, _) 
    | If (_, _, _, _) 
    | SetBang(_,_,_)
    | Seq (_,_,_)
    | Label (_,_,_)
    | Break (_,_,_)
    | TryCatch (_,_,_)
    | TryFinally (_,_,_)
    | Throw (_,_)
    | Eval (_,_,_)
    | Hint(_,_,_)
      -> optimize (fun x->inlining_rec x env) e
  in 
  inlining_rec e empty_env
