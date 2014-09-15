open Prelude
open Ljs_syntax
module EV = Exp_val

type env = exp IdMap.t

let rec inlining (e : exp) : exp =
  let empty_env = IdMap.empty in
  let rec inlining_rec e env =
    let rec inlining_rec_option opt env = match opt with
      | Some (e) -> Some (inlining_rec e env)
      | None -> None in
    match e with
    | Undefined _ -> e
    | Null _ -> e
    | String (_, _) -> e
    | Num (_, n) -> e
    | True _ -> e
    | False _ -> e
    | Id (p, x) ->
       begin 
         try 
           IdMap.find x env
         with _ -> e
       end 
    | Object (p, attrs, strprop) ->
       let new_attrs = {
         primval = inlining_rec_option attrs.primval env;
         code = inlining_rec_option attrs.code env;
         proto = inlining_rec_option attrs.proto env;
         klass = attrs.klass;
         extensible = attrs.extensible } in
       let handle_prop p = match p with
         | (s, Data (data, enum, config)) ->
            s, Data ({value = inlining_rec data.value env;
                      writable = data.writable}, enum, config)
         | (s, Accessor (acc, enum, config)) ->
            s, Accessor ({getter = inlining_rec acc.getter env; setter = inlining_rec acc.setter env},
                         enum, config) in
       let prop_list = List.map handle_prop strprop in
       Object (p, new_attrs, prop_list)

    | GetAttr (p, pattr, obj, field) -> 
       let o = inlining_rec obj env in
       let f = inlining_rec field env in
       GetAttr(p, pattr, o, f)

    | SetAttr (p, attr, obj, field, newval) ->
       let o = inlining_rec obj env in
       let f = inlining_rec field env in
       let v = inlining_rec newval env in
       SetAttr (p, attr, o, f, v)

    | GetObjAttr (p, oattr, obj) ->
       let o = inlining_rec obj env in
       GetObjAttr(p, oattr, o)

    | SetObjAttr (p, oattr, obj, attre) ->
       let o = inlining_rec obj env in
       let attr = inlining_rec attre env in
       SetObjAttr (p, oattr, o, attr)

    | GetField (p, obj, fld, args) -> 
       let o = inlining_rec obj env in
       let f = inlining_rec fld env in
       let a = inlining_rec args env in
       GetField (p, o, f, a)

    | SetField (p, obj, fld, newval, args) ->
       let o = inlining_rec obj env in
       let f = inlining_rec fld env in
       let v = inlining_rec newval env in
       let a = inlining_rec args env in
       SetField (p, o, f, v, a)

    | DeleteField (p, obj, fld) ->
       let o = inlining_rec obj env in
       let f = inlining_rec fld env in
       DeleteField (p, o, f)

    | OwnFieldNames (p, obj) -> 
       OwnFieldNames (p, (inlining_rec obj env))

    | SetBang (p, x, e) ->
       SetBang (p, x, (inlining_rec e env))

    | Op1 (p, op, e) ->
       Op1 (p, op, (inlining_rec e env))

    | Op2 (p, op, e1, e2) ->
       Op2 (p, op, (inlining_rec e1 env), (inlining_rec e2 env))

    | If (p, cond, thn, els) -> 
       If (p, (inlining_rec cond env), (inlining_rec thn env), (inlining_rec els env))

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
       if EV.mutate_var x body then
         del_x_from_env_continue env 
       else 
         (* no mutation on x, decide if it is constant lambda *)
         let is_const_func = EV.is_lambda_constant x_v in 
         if not is_const_func then
           del_x_from_env_continue env
         else 
           let new_env = IdMap.add x x_v env in 
           Let (p, x, x_v, (inlining_rec body new_env))

    | Rec (p, x, xexp, body) ->
       let x_v = inlining_rec xexp env in
       let del_x_from_env_continue curenv =
         let new_env = IdMap.remove x curenv in
         let new_body = inlining_rec body new_env in
         Rec (p, x, x_v, new_body)
       in 
       if EV.mutate_var x body then
         del_x_from_env_continue env 
       else 
         (* no mutation on x, decide if it is constant lambda *)
         let is_const_func = EV.is_lambda_constant x_v in 
         if not is_const_func then
           del_x_from_env_continue env
         else 
           let new_env = IdMap.add x x_v env in 
           Rec (p, x, x_v, (inlining_rec body new_env))

