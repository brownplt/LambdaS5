open Prelude
open Ljs_delta
module S = Ljs_syntax
module V = Ljs_values

exception ExpValError of string
type pool = (S.exp * bool * bool) IdMap.t

let print_ljs ljs =
  Ljs_pretty.exp ljs Format.std_formatter; print_newline()

let exp_to_value (e : S.exp) : V.value = 
  match e with 
  | S.Null _ -> V.Null
  | S.Undefined _ -> V.Undefined
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

let rec is_bound (x : S.exp) (body : S.exp) : bool =
  match x, body with 
  | S.Id (_, var1), S.Let (_, var2, xexp, body) -> var1 = var2 || is_bound x xexp || is_bound x body
  | S.Id (_, var1), S.Rec (_, var2, xexp, body) -> var1 = var2 || is_bound x xexp || is_bound x body
  | S.Id (_, var1), S.Lambda (_, xs, body) ->
    List.mem var1 xs || is_bound x body
  | S.Id (_, var1), S.SetBang (_, var2, e) -> var1 = var2 || is_bound x e
  | _ -> List.exists (fun(e)->is_bound x e) (S.child_exps body)
                                                      
let is_Id (x : S.exp) : bool = match x with
  | S.Id (_, _) -> true
  | _ -> false

let rec is_constant (e : S.exp) pool : bool = match e with
  | S.Object(_,_,_) -> is_object_constant e pool
  | S.Lambda(_,_,_) -> is_lambda_constant e 
  | S.Id (_, _) -> is_const_var e pool
  | _ -> is_prim_constant e
(* an const object requires extensible is false, all fields have configurable
   and writable set to false.

   XXX: it seems that when getter and setter are present, configurable cannot be set from 
        the syntax. So there is no such an object that getter and setter and configurable attr
        are both initially constant.
 *)
and is_object_constant (e : S.exp) pool : bool = match e with
  | S.Object (_, attr, strprop) ->
     let { S.primval=primval;S.proto=proto;S.code=code;S.extensible = ext;S.klass=_ } = attr in
     let const_primval = match primval with
       | Some x -> is_constant x pool
       | None -> true 
     in
     let const_proto = match proto with
       | Some x -> is_constant x pool
       | None -> true
     in
     let const_code = match code with
       | Some x -> is_constant x pool
       | None -> true
     in 
     if (not const_primval || not const_proto || not const_code || ext = true) then
       false 
     else begin 
         let const_prop (p : string * S.prop) = match p with
           | (s, S.Data ({S.value = value; S.writable=false}, _, false)) -> 
              is_constant value pool
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
(* WRONG! check side effect *)
and is_lambda_constant (e: S.exp) : bool = match e with
  | S.Lambda (_, ids, body) ->
     let free_vars = S.free_vars e in 
     IdSet.is_empty free_vars
  | _ -> false

(* NOTE(junsong): this predicate can only be used for non-lambda and non-object non-id exp *)
and is_prim_constant (e : S.exp) : bool = match e with
  | S.Null _
  | S.Undefined _
  | S.Num (_, _)
  | S.String (_, _)
  | S.True _
  | S.False _ -> true
  | _ -> false

and is_const_var (e : S.exp)  (pool : pool) : bool = match e with
  | S.Id (_, id) -> 
     begin
       try let (_, const, subst) = IdMap.find id pool in const 
       with _ -> false
     end
  | _ -> false
       
(* decide if x is mutated in e *)
let rec mutate_var (x : id) (e : S.exp) : bool = match e with
  | S.SetBang (_, var, target) -> x = var || mutate_var x target
  | S.Let (_, var, defn, body) ->
     if (mutate_var x defn) then (* look at the def first *)
       true
     else
       if (var = x) then (* previous scope is over *)
         false
       else (* continue search in body *)
         mutate_var x body
  | S.Rec (_, var, defn, body) ->
     if (mutate_var x defn) then true
     else
       if (var = x) then false
       else mutate_var x body
  | S.Lambda (_, vars, body) ->
     if (List.mem x vars) then (* x is shadowed in lambda *)
       false
     else
       mutate_var x body
  | _ -> List.exists (fun x->x) (map (fun exp-> mutate_var x exp) (S.child_exps e))

let print_ljs ljs =
  Ljs_pretty.exp ljs Format.std_formatter; print_newline()


(*
 * this function will check whether exp `e' has side effect *when it is evaluated*.
 * NOTE(junsong): The subtle point is
 * let (x = func(){ y:=1} ) {x} does not have side effect
 * let (x = func(){ y:=1} ) {x()} has side effect.
 *
 * this function makes strong assertion on app(): any app has side effect
 *)
let rec has_side_effect (e : S.exp) : bool = match e with
  | S.Null _
  | S.Undefined _
  | S.String (_,_)
  | S.Num (_,_)
  | S.True _
  | S.False _
  | S.Id (_,_) 
    -> false
  | S.GetAttr (_, _,obj, flds) ->
     has_side_effect obj || has_side_effect flds
  | S.GetObjAttr (_, _, obj) ->
     has_side_effect obj
  | S.OwnFieldNames (_, obj) ->
     has_side_effect obj
  | S.Op2 (_,_,e1,e2) ->
     has_side_effect e1 || has_side_effect e2
  | S.Op1 (_,op,e1) ->
     op_has_side_effect op || has_side_effect e1
  | S.Object (_,_,_) ->
     List.exists has_side_effect (S.child_exps e)
  | S.If (_, cond, thn, els) ->
     List.exists has_side_effect [cond; thn; els]
  | S.Seq (_, e1, e2) ->
     has_side_effect e1 || has_side_effect e2
  | S.Let (_, x, x_v, body) ->
     let se = has_side_effect body in
     if se then true
     else 
       begin
         match x_v with 
         | S.Lambda (_, _, _) -> false
         | _ -> has_side_effect x_v 
       end 
  | S.Rec (_, x, x_v, body) ->
     has_side_effect body
  | S.Lambda (_, _, body) -> has_side_effect body
  | S.Label (_, _, e) -> has_side_effect e
  | S.Break (_, _, _)
  | S.SetAttr (_,_,_,_,_)
  | S.SetObjAttr (_,_,_,_)
  | S.GetField (_,_,_,_)
  | S.SetField (_,_,_,_,_)
  | S.DeleteField (_,_,_)
  | S.SetBang (_,_,_) 
  | S.App (_,_,_)           (* any f(x) is assumed to have side effect *)
  | S.TryCatch (_, _, _)    (* any try...catch is assumed to throw out uncatched error *)
  | S.TryFinally (_, _, _)  (* any try...finally is assumed to throw out uncached error *)
  | S.Throw (_,_)
  | S.Eval (_,_,_)
  | S.Hint (_,_,_)
    -> true
