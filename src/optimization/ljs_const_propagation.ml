open Prelude
open Ljs_syntax
open Ljs_opt
module EU = Exp_util

type newenv = (exp * bool) IdMap.t

let rec is_constant (e : exp) newenv : bool = match e with
  | Object(_,_,_) -> is_object_constant e newenv
  | Lambda(_,_,_) -> is_lambda_constant e 
  | Id (_, _) -> is_const_var e newenv
  | _ -> is_prim_constant e
(* an const object requires extensible is false, all fields have configurable
   and writable set to false.

   XXX: it seems that when getter and setter are present, configurable cannot be set from 
        the syntax. So there is no such an object that getter and setter and configurable attr
        are both initially constant.
 *)
and is_object_constant (e : exp) newenv : bool = match e with
  | Object (_, attr, strprop) ->
     let { primval=primval;proto=proto;code=code;extensible = ext;klass=_ } = attr in
     let const_primval = match primval with
       | Some x -> is_constant x newenv && not (EU.has_side_effect x)
       | None -> true 
     in
     let const_proto = match proto with
       | Some x -> is_constant x newenv && not (EU.has_side_effect x)
       | None -> true
     in
     let const_code = match code with
       | Some x -> is_constant x newenv && not (EU.has_side_effect x)
       | None -> true
     in 
     if (not const_primval || not const_proto || not const_code || ext = true) then
       false 
     else begin 
         let const_prop (p : string * prop) = match p with
           | (s, Data ({value = value; writable=false}, _, false)) -> 
              is_constant value newenv && not (EU.has_side_effect value)
           | _ -> false
         in
         let is_const_property = List.for_all const_prop strprop in
         is_const_property
       end
  | _ -> false

(* a lambda is a constant if no free vars and side effect in the body is fine, because
   the optimization will require lambda is used once once. *)
and is_lambda_constant (e: exp) : bool = match e with
  | Lambda (_, ids, body) ->
     IdSet.is_empty (free_vars e)
  | _ -> false

(* NOTE(junsong): this predicate can only be used for non-lambda and non-object non-id exp *)
and is_prim_constant (e : exp) : bool = match e with
  | Null _
  | Undefined _
  | Num (_, _)
  | String (_, _)
  | True _
  | False _ -> true
  | _ -> false

and is_const_var (e : exp)  (newenv : newenv) : bool = match e with
  | Id (_, id) -> IdMap.mem id newenv 
  | _ -> false


let rec const_propagation (e : exp) : exp =
  let empty_newenv = IdMap.empty in
  let rec propagation_rec (e : exp) (newenv : newenv) : exp = 
    let propagate exp = propagation_rec exp newenv in
    match e with 
    | Undefined _ 
    | Null _
    | String (_,_)
    | Num (_,_)
    | True _
    | False _ -> e
    | Id (p, x) ->
       begin
         try 
           let (exp, subst) = IdMap.find x newenv in
           if subst then exp else e
         with _ -> e
       end 
    | Let (p, x, x_v, body) ->
       let x_v = propagation_rec x_v newenv in
       let is_const = is_constant x_v newenv in 
       (* if x will be mutated or x_v is not constant *)
       if EU.mutate_var x body || not is_const then
         let newenv = IdMap.remove x newenv in
         Let (p,x,x_v, propagation_rec body newenv)
       else 
         let substitute =
           is_prim_constant x_v || is_const_var x_v newenv ||
             ((is_object_constant x_v newenv || is_lambda_constant x_v) &&
                not (EU.multiple_usages x body))
         in 
         let newenv = IdMap.add x (x_v, substitute) newenv in
         Let (p, x, x_v, propagation_rec body newenv)
    | Rec (p, x, x_v, body) ->
       let x_v = propagation_rec x_v newenv in
       let is_const = is_constant x_v newenv in 
       (* if x will be mutated or x_v is not constant *)
       if EU.mutate_var x body || not is_const then
         let newenv = IdMap.remove x newenv in
         Rec (p,x,x_v, propagation_rec body newenv)
       else 
         let substitute = not (EU.multiple_usages x body) in
         let newenv = IdMap.add x (x_v, substitute) newenv in
         Rec (p, x, x_v, propagation_rec body newenv)
    | Lambda (p, xs, body) ->
       (* remove each x in xs from newenv *)
       let filtered_newenv = 
         IdMap.filter (fun x _->not (List.mem x xs) ) newenv in
       Lambda (p, xs, propagation_rec body filtered_newenv)
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
  propagation_rec e empty_newenv
