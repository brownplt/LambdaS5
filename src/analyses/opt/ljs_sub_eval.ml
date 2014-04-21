open Prelude
open Ljs_syntax
open Ljs_constfolding

(* partial evaluation using substitution.
 * 
 * This function accepts an exp(see ljs_syntax.ml) and performs
 * subsitution to give out partial evaluation result
 *)
type env = exp IdMap.t

let partial_eval e : exp =
  let empty_env = IdMap.empty in
  let rec sub_eval e env = 
    match e with 
    | Undefined _ -> e
    | Null _ -> e
    | String (_, _) -> e
    | Num (_, n) -> e
    | True _ -> e
    | False _ -> e
    | Id (p, x) -> 
       begin
         try IdMap.find x env 
         with Not_found -> failwith ("[substitution] Unbound identifier: " ^ x) end
     (* TODO: attrs *)
    | Object (_, _, _) -> e 
    | GetAttr (p, pattr, obj, field) -> (* potential *)
       let o = sub_eval obj env in
       let f = sub_eval field env in
       GetAttr (p, pattr, o, f)
    | SetAttr (p, attr, obj, field, newval) -> (* potential *)
       let o = sub_eval obj env in
       let f = sub_eval field env in
       let v = sub_eval newval env in
       SetAttr (p, attr, o, f, v)
    | GetObjAttr (p, oattr, obj) -> (* potential *)
       GetObjAttr (p, oattr, (sub_eval obj env))
    | SetObjAttr (p, oattr, obj, attre) ->
       let o = sub_eval obj env in
       let attr = sub_eval attre env in
       SetObjAttr (p, oattr, o, attr)
    | GetField (p, obj, fld, args) -> (* potential *)
       let o = sub_eval obj env in
       let f = sub_eval fld env in
       let a = sub_eval args env in
       GetField (p, o, f, a)
    | SetField (p, obj, fld, newval, args) ->
       let o = sub_eval obj env in
       let f = sub_eval fld env in
       let v = sub_eval newval env in
       let a = sub_eval args env in
       SetField (p, o, f, v, a)
    | DeleteField (p, obj, fld) -> 
       let o = sub_eval obj env in
       let f = sub_eval fld env in
       DeleteField (p, o, f)
    | OwnFieldNames (p, obj) -> (* potential *)
       OwnFieldNames (p, (sub_eval obj env))
    | SetBang (p, x, e) ->
       SetBang (p, x, (sub_eval e env))
    | Op1 (p, op, e) -> 
       Op1 (p, op, (sub_eval e env))
    | Op2 (p, op, e1, e2) -> 
       Op2 (p, op, (sub_eval e1 env), (sub_eval e2 env))
    | If (p, cond, thn, els) ->
       If (p, (sub_eval cond env), (sub_eval thn env), (sub_eval els env))
    | App (p, func, args) ->
       let f = sub_eval func env in
       let a = List.map (fun x->sub_eval x env) args in
       App (p, f, a)
    | Seq (p, e1, e2) ->
       let new_e1 = sub_eval e1 env in
       let new_e2 = sub_eval e2 env in
       Seq (p, new_e1, new_e2)
    | Let (p, x, exp, body) ->
       let new_exp = sub_eval exp env in
       let new_env = IdMap.add x new_exp env in
       (* TODO: check the mutation in the body *)
       let new_body = sub_eval body new_env in
       Let (p, x, new_exp, new_body)
    | Rec (p, x, e, body) ->
       let new_e = sub_eval e env in
       let new_body = sub_eval body env in
       Rec (p, x, new_e, new_body)
    | Label (p, l, e) ->
       let new_e = sub_eval e env in
       Label (p, l, new_e)
    | Break (p, l, e) ->
       let new_e = sub_eval e env in
       Break (p, l, new_e)
    | TryCatch (p, body, catch) ->
       let b = sub_eval body env in
       let c = sub_eval catch env in
       TryCatch (p, b, c)
    | TryFinally (p, body, fin) ->
       let b = sub_eval body env in
       let f = sub_eval fin env in
       TryFinally (p, b, f)
    | Throw (p, e) ->
       Throw (p, (sub_eval e env))
    | Lambda (p, xs, e) ->
       Lambda (p, xs, (sub_eval e env))
    | Eval (p, e, bindings) ->
       let new_e = sub_eval e env in
       let new_bindings = sub_eval bindings env in
       Eval (p, new_e, new_bindings)
    | Hint (p, id, e) -> 
       Hint (p, id, (sub_eval e env))
  in 
  sub_eval e empty_env
