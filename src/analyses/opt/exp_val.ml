open Prelude
open Ljs_delta
module S = Ljs_syntax
module V = Ljs_values

exception ExpValError of string

(* TODO: move is_constant of ljs_substitute_eval here *)

let exp_to_value (e : S.exp) : V.value = 
  match e with 
  | S.Null _ -> V.Null
  | S.Undefined _ -> V.Null
  | S.Num (_, n) -> V.Num n
  | S.String (_, s) -> V.String s
  | S.True _ -> V.True
  | S.False _ -> V.False
  | _ -> raise (ExpValError "exp->value error")


let value_to_exp (v : V.value) (p : Pos.t) : S.exp =
  match v with
  | V.Null -> S.Null p
  | V.Undefined -> S.Undefined p
  | V.Num n -> S.Num (p, n)
  | V.String s -> S.String (p, s)
  | V.True -> S.True p
  | V.False -> S.False p
  | _ -> raise (ExpValError "value->exp error")

let dummy_store = (Store.empty, Store.empty)

let op_has_side_effect (op : string) : bool = match op with
  | "print"
  | "pretty"
  | "current-utc-millis" -> true
  | _ -> false 

let apply_op1 p (op : string) e : S.exp option = 
  if (op_has_side_effect op) then
    None
  else
    try 
      let v = exp_to_value e in
      let op = op1 dummy_store op in
      let result = op v in
      Some (value_to_exp result p)
    with _ -> None
                          
let apply_op2 p op e1 e2 : S.exp option =
  if (op_has_side_effect op) then
    None
  else
    try
      let v1 = exp_to_value e1 in
      let v2 = exp_to_value e2 in
      let op = op2 dummy_store op in
      let result = op v1 v2 in
      Some (value_to_exp result p)
    with _ -> None


                                                      
let rec is_constant (e : S.exp) : bool = match e with
  | S.Object(_,_,_) -> is_object_constant(e)
  | S.Lambda(_,_,_) -> is_lambda_constant(e)
  | _ -> is_scalar_constant(e)
 
(* an const object requires extensible is false, all fields have configurable
   and writable set to false.
   XXX: it seems that when getter and setter are present, configurable cannot be set from 
        the syntax. So there is no such an object that getter and setter and configurable attr
        are both initially constant.
 *)
and is_object_constant (e : S.exp) : bool = match e with
  | S.Object (_, attr, strprop) ->
     let { S.primval=primval;S.proto=proto;S.code=_;S.extensible = ext;S.klass=_ } = attr in
     let const_primval = match primval with
       | Some e -> is_constant e
       | None -> true 
     in
     let const_proto = match proto with
       | Some e -> is_constant e
       | None -> true
     in
     if (not const_primval || not const_proto || ext = true) then
       false
     else begin 
         let const_prop (p : string * S.prop) = match p with
           | (s, S.Data ({S.value = value; S.writable=false}, _, false)) -> 
              is_constant(value)
           | (s, S.Accessor({S.getter=getter; S.setter=setter}, _, false)) -> 
                is_constant getter && is_constant setter
           | _ -> false
         in
         let is_const_property = List.for_all const_prop strprop in
         is_const_property
       end
  | _ -> false

(* a lambda is a constant if no free vars in the body.
 NOTE: it is safe to have the side effect in the lambda body, since the shrink-optimization will
       only be performed when the lambda is used once.
*)
and is_lambda_constant (e: S.exp) : bool = match e with
  | S.Lambda (_, ids, body) ->
     let free_vars = S.free_vars e in 
     IdSet.is_empty free_vars
  | _ -> false

(* NOTE(junsong): this predicate can only be used for non-lambda and non-object exp *)
and is_scalar_constant (e : S.exp) : bool = match e with
  | S.Null _
  | S.Undefined _
  | S.Num (_, _)
  | S.String (_, _)
  | S.True _
  | S.False _ -> true
  (*| S.Id (_, _) -> true *)
  | _ -> false

           
       
