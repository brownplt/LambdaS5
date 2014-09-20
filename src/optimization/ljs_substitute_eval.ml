open Prelude
open Ljs_syntax
open Ljs_const_folding
module EV = Exp_val


(* Optimization phase.
 *
 * partial evaluation by substitution.
 *
 * This function accepts an exp(see ljs_syntax.ml) and performs
 * subsitution to give out partial evaluation result
 *
 *)

(* pool is maps from id to `exp` and `is constant?` `can be substituted?`, which
   indicates if the `exp` can replace id.
 *)
type pool = (exp * bool * bool) IdMap.t

(* pool may contain id x ->id y mapping, this function can follow the id y and get
   the final exp *)
let rec follow_until_const_nonid e pool : exp =
  match e with
  | Id (_, id) -> 
     let (exp, const, _) = IdMap.find id pool in 
     if const then follow_until_const_nonid exp pool else failwith "follow id failed"
  | _ -> e


(* NOTE: xexp should be an optimized one

To drop a let(or rec binding), 
 - var will not be mutated.
 - either var is used only once if var is object constant or lambda constant, 
   or var is other constants, e.g. integer *)

let rec substitute_const (e : exp) : (exp * bool) =
  let empty_pool = IdMap.empty in
  let modified = (ref false) in
  let rec substitute_eval e pool =
    let rec substitute_eval_option opt pool = match opt with
      | Some (e) -> Some (substitute_eval e pool)
      | None -> None in
    let rec app_eval p lambda args pool =
      (* TODO: some prim needs to convert object, which will failwith something *)
      (* if f is a constant lambda and args are constants, evaluate to get the result *)
      let rec get_const e pool = 
        if EV.is_object_constant e pool || EV.is_lambda_constant e ||
             EV.is_scalar_constant e 
        then Some e
        else match e with
             | Id (_, id) ->
                begin
                  try 
                    let (exp, const, _) = IdMap.find id pool in
                    if const then 
                      get_const exp pool
                    else None
                  with _ -> None
                end 
             | _ -> None
      in 
      let are_const_args = List.for_all (fun(x)->EV.is_constant x pool) args in 
      let const_lambda = get_const lambda pool in 
      match are_const_args, const_lambda with
      | true, Some Lambda (_, xs, body) ->
         let const_args = List.map (fun e->follow_until_const_nonid e pool) args in
         let rec addbind xs args pool = match xs, args with
           | [], [] -> pool
           | x :: xrest, arg :: argrest ->
              addbind xrest argrest (IdMap.add x (arg, true, true) pool)
           | _ -> failwith "args has non-consistant length"
         in 
         let new_pool = addbind xs const_args pool in 
         substitute_eval body new_pool
      | _ -> App (p, lambda, args)
    in 
  

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
           match IdMap.find x pool with
           | (x_v, _, true) -> x_v
           | (x_v, _, false) -> e
         with Not_found -> e 
       end
    | Object (p, attrs, strprop) ->
       let new_attrs = {
         primval = substitute_eval_option attrs.primval pool;
         code = substitute_eval_option attrs.code pool;
         proto = substitute_eval_option attrs.proto pool;
         klass = attrs.klass;
         extensible = attrs.extensible } in
       let handle_prop p = match p with
         | (s, Data (data, enum, config)) ->
            s, Data ({value = substitute_eval data.value pool;
                      writable = data.writable}, enum, config)
         | (s, Accessor (acc, enum, config)) ->
            s, Accessor ({getter = substitute_eval acc.getter pool; setter = substitute_eval acc.setter pool},
                         enum, config) in
       let prop_list = List.map handle_prop strprop in
       Object (p, new_attrs, prop_list)

    | GetAttr (p, pattr, obj, field) -> 
       let o = substitute_eval obj pool in
       let f = substitute_eval field pool in
       GetAttr(p, pattr, o, f)

    | SetAttr (p, attr, obj, field, newval) ->
       let o = substitute_eval obj pool in
       let f = substitute_eval field pool in
       let v = substitute_eval newval pool in
       SetAttr (p, attr, o, f, v)

    | GetObjAttr (p, oattr, obj) ->
       let o = substitute_eval obj pool in
       GetObjAttr(p, oattr, o)

    | SetObjAttr (p, oattr, obj, attre) ->
       let o = substitute_eval obj pool in
       let attr = substitute_eval attre pool in
       SetObjAttr (p, oattr, o, attr)

    | GetField (p, obj, fld, args) -> 
       let o = substitute_eval obj pool in
       let f = substitute_eval fld pool in
       let a = substitute_eval args pool in
       GetField (p, o, f, a)

    | SetField (p, obj, fld, newval, args) ->
       let o = substitute_eval obj pool in
       let f = substitute_eval fld pool in
       let v = substitute_eval newval pool in
       let a = substitute_eval args pool in
       SetField (p, o, f, v, a)

    | DeleteField (p, obj, fld) ->
       let o = substitute_eval obj pool in
       let f = substitute_eval fld pool in
       DeleteField (p, o, f)

    | OwnFieldNames (p, obj) -> 
       OwnFieldNames (p, (substitute_eval obj pool))

    | SetBang (p, x, e) ->
       SetBang (p, x, (substitute_eval e pool))

    | Op1 (p, op, e) ->
       Op1 (p, op, (substitute_eval e pool))

    | Op2 (p, op, e1, e2) ->
       Op2 (p, op, (substitute_eval e1 pool), (substitute_eval e2 pool))

    | If (p, cond, thn, els) -> (* more optimization in constant folding *)
       If (p, (substitute_eval cond pool), (substitute_eval thn pool), (substitute_eval els pool))

    | App (p, func, args) ->
       let f = substitute_eval func pool in
       let a = List.map (fun x->substitute_eval x pool) args in
       app_eval p f a pool

    | Seq (p, e1, e2) ->
       let new_e1 = substitute_eval e1 pool in
       let new_e2 = substitute_eval e2 pool in
       Seq (p, new_e1, new_e2)

    | Let (p, x, exp, body) ->
       let x_v = substitute_eval exp pool in
       let del_x_from_pool_continue currentpool =
         let new_pool = IdMap.remove x currentpool in
         let new_body = substitute_eval body new_pool in 
         Let (p, x, x_v, new_body) 
       in 
       if EV.mutate_var x body then 
         del_x_from_pool_continue pool
       else
         (* no mutation, decide if it is constant *)
         let is_const = EV.is_constant x_v pool in
         if not is_const then 
           begin 
             (* if x_v is not constant, decide if x_v is an id and that id is not bound
                again in body. If so, x->(x_v, not constant, can be substituted) should  
                be added to pool *)
             if (EV.is_Id x_v && not (EV.is_bound x_v body)) then (* NOTE: both x and x_v should not be mutated *)
               let newpool = IdMap.add x (x_v, false, true) pool in
               begin
                 modified := true;
                 substitute_eval body newpool
               end 
             else  (* if it is not a constant and not an id, remove x from pool *)
               del_x_from_pool_continue pool
           end 
         else
           (* is constant, decide the substitute *)
           let substitute = 
             EV.is_scalar_constant x_v || EV.is_const_var x_v pool ||
               ((EV.is_object_constant x_v pool || EV.is_lambda_constant x_v) && 
                  not (EU.multiple_usages x body)) 
           in
           let new_pool = IdMap.add x (x_v, true, substitute) pool in
           (* get the substitution, decide if let should be dropped *)
           if substitute then
             begin 
               if (EV.is_bound x_v body) then 
                 (* if x_v is Id and is bound later. let (x=x_v) should be kept, and 
                      x should be substituted *)
                 let new_pool = IdMap.add x (x_v, true, false) pool in
                 Let (p, x, x_v, (substitute_eval body new_pool))
               else
                 begin
                   modified := true;
                   substitute_eval body new_pool
                 end
             end
           else
             let new_body = substitute_eval body new_pool in
             Let (p, x, x_v, new_body)
             
    | Rec (p, x, exp, body) ->  
       let x_v = substitute_eval exp pool in
       let del_x_from_pool_continue() =
         let new_pool = IdMap.remove x pool in
         let new_body = substitute_eval body new_pool in 
         Rec (p, x, x_v, new_body) in

       if EV.mutate_var x body then del_x_from_pool_continue()
       else
         (* no mutation *)
         let is_const = EV.is_constant x_v pool in
         if not is_const then del_x_from_pool_continue()
         else
           (* is constant, decide the substitute, const lambda exp can be substitute
              if the lambda is used once *)
           let substitute =  not (EU.multiple_usages x body) in
           let new_pool = IdMap.add x (x_v, true, substitute) pool in
           if substitute then
             begin
               modified := true;
               substitute_eval body new_pool
             end
           else
             let new_body = substitute_eval body new_pool in
             Rec (p, x, x_v, new_body)

    | Label (p, l, e) ->
       let new_e = substitute_eval e pool in
       Label (p, l, new_e)

    | Break (p, l, e) ->
       let new_e = substitute_eval e pool in
       Break (p, l, new_e)

    | TryCatch (p, body, catch) ->
       let b = substitute_eval body pool in
       let c = substitute_eval catch pool in
       TryCatch (p, b, c)

    | TryFinally (p, body, fin) ->
       let b = substitute_eval body pool in
       let f = substitute_eval fin pool in
       TryFinally (p, b, f)
    | Throw (p, e) ->
       Throw (p, (substitute_eval e pool))

    | Lambda (p, xs, e) -> (* lambda needs a modified pool *) (* TODO: see lambda in ljs_eval.ml *)
       let rec get_new_pool ids pool =  match ids with
         | [] -> pool
         | id :: rest ->
            let new_pool = IdMap.remove id pool in
            get_new_pool rest new_pool 
       in 
       let new_pool = get_new_pool xs pool in
       Lambda (p, xs, (substitute_eval e new_pool))

    | Eval (p, e, bindings) ->
       let new_e = substitute_eval e pool in
       let new_bindings = substitute_eval bindings pool in
       Eval (p, new_e, new_bindings)
    | Hint (p, id, e) ->
       Hint (p, id, (substitute_eval e pool)) 
  in
  let result = substitute_eval e empty_pool in
  result, !modified

