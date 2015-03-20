open Ljs_syntax
open Ljs_opt

(* given a lambda definition, and a set of potential conflict ids,
   alpha rename the lambda formal arguments to be distinguishing from
   the given ids set.
*)

let is_empty_inter s1 s2 =
  IdSet.is_empty (IdSet.inter s1 s2)

(* env is used for name replacement: old name => new name *)
type env = id IdMap.t

let env_mem id env = IdMap.mem id env
let env_drop id env = IdMap.filter (fun x _ -> not (x = id)) env
    
let alpha_rename (func : exp) (namespace : IdSet.t) : exp =
  
  let rec resolve (exp : exp) (env : env) : exp =
    let resolve_helper e = resolve e env in
    match exp with
    | Id (p, id) when env_mem id env ->
      Id (p, IdMap.find id name_mapping)
    | Let (p, x, xv, body) when env_mem x env ->
      (* old name is rebound, so just leave it along *)
      let new_xv = resolve xv env in
      let new_env = env_drop x env in
      let new_body = resolve body new_env in
      Let (p, x, new_xv, new_body)
    | Rec (p, x, xv, body) when env_mem x env ->
      (* old name is rebound, so just leave it along *)
      (* the x in xv is bound to a new one, not the one we want to replace *)
      let new_env = env_drop x env in
      let new_xv = resolve xv new_env in
      let new_body = resolve body new_env in
      Rec (p, x, new_xv, new_body)
    | Lambda (p, xs, body) 
  in
  (* first, let's make sure the function formal argument has conflict *)
  match func with
  | Lambda (p, xs, body) ->
    let conflict_names = IdSet.inter (IdSet.from_list xs) conflict in
    if IdSet.is_empty conflict_names then
      (* no conflict, return the original form *)
      func
    else
      let new_xs, new_body = resolve xs body namespace in
      let fix_xs = 
      Lambda (p, new_xs, new_body)
  | _ -> failwith "alpha_rename only accepts function definition as the argument"
