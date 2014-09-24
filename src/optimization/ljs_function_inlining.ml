open Prelude
open Ljs_syntax
open Ljs_opt
module EU = Exp_util

type env = exp IdMap.t


let rec is_constant (e : exp) env : bool = match e with
  | Object(_,_,_) -> is_object_constant e env
  | Lambda(_,_,_) -> is_lambda_constant e 
  | Id (_, _) -> is_const_var e env
  | _ -> is_prim_constant e

(* an const object requires extensible is false, all fields have configurable
   and writable set to false.

   XXX: it seems that when getter and setter are present, configurable cannot be set from 
        the syntax. So there is no such an object that getter and setter and configurable attr
        are both initially constant.
 *)
and is_object_constant (e : exp) env : bool = match e with
  | Object (_, attr, strprop) ->
     let { primval=primval;proto=proto;code=code;extensible = ext;klass=_ } = attr in
     let const_primval = match primval with
       | Some x -> is_constant x env && not (EU.has_side_effect x)
       | None -> true 
     in
     let const_proto = match proto with
       | Some x -> is_constant x env && not (EU.has_side_effect x)
       | None -> true
     in
     let const_code = match code with
       | Some x -> is_constant x env && not (EU.has_side_effect x)
       | None -> true
     in 
     if (not const_primval || not const_proto || not const_code || ext = true) then
       false 
     else begin 
         let const_prop (p : string * prop) = match p with
           | (s, Data ({value = value; writable=false}, _, false)) -> 
              is_constant value env && not (EU.has_side_effect value)
           | _ -> false
         in
         let is_const_property = List.for_all const_prop strprop in
         is_const_property
       end
  | _ -> false

(* a lambda is a constant if no free vars and side effect should not occur in body
   the requirement is different with that of constant propagation *)
and is_lambda_constant (e: exp) : bool = match e with
  | Lambda (_, ids, body) ->
     IdSet.is_empty (free_vars e) && not (EU.has_side_effect body)
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

and is_const_var (e : exp)  (env : 'a IdMap.t) : bool = match e with
  | Id (_, id) -> IdMap.mem id env 
  | _ -> false

let rec get_lambda e env : exp option = match e with
  | Id (_, id) -> 
     begin
       try
         let v = IdMap.find id env in
         match v with 
         | Lambda (_,_,_) -> Some (v)
         | _ -> None
       with _ -> None
     end 
  | Lambda (_,_,_) -> Some e
  | _ -> None
  

(*
inline a function when
1. lambda that has no free variables and has no side effect in the body
2. function application's argument should be constants or `id`.
 *)
let rec function_inlining (e : exp) : exp =
  let empty_env = IdMap.empty in
  let rec inlining_rec e env =
    match e with
    | App (p, func, args) ->
       (* if args are all constant and func is constant, do function inlining here, *)
       let func = inlining_rec func env in
       let args = List.map (fun x->inlining_rec x env) args in
       let f = get_lambda func env in
       let are_const_args lst = List.for_all (fun e-> is_constant e env) lst in
       begin
         match f, are_const_args args with
         (*| Some (e), false -> printf "\nget one:"; printf "%s" (ljs_str e); printf "\nargs: "; List.iter (fun(x)->printf "%s," (ljs_str x)) args; App (p, func, args)*)
         | Some (e), true -> inline_lambda p e args
         | _ -> App (p, func, args)
       end 
    | Let (p, x, xexp, body) ->
       let x_v = inlining_rec xexp env in
       let is_const = is_constant x_v env in
       if EU.mutate_var x body ||  not is_const then
         let env = IdMap.remove x env in
         Let (p, x, x_v, inlining_rec body env)
       else 
         let env = IdMap.add x x_v env in 
         Let (p, x, x_v, (inlining_rec body env))

    | Rec (p, x, xexp, body) ->
       let x_v = inlining_rec xexp env in
       let is_const = is_constant x_v env in
       if EU.mutate_var x body || not is_const then
         let env = IdMap.remove x env in
         Rec (p, x, x_v, inlining_rec body env)
       else 
         let new_env = IdMap.add x x_v env in 
         Rec (p, x, x_v, inlining_rec body new_env)
    | Lambda (p,xs,body) ->
       let filtered_env = 
         IdMap.filter (fun x _->not (List.mem x xs)) env in
       Lambda (p, xs, inlining_rec body filtered_env)
    | Undefined _
    | Null _ 
    | String (_, _) 
    | Num (_, _) 
    | True _ 
    | False _ -> e
    | Id (p, x) -> e
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

and inline_lambda p (f : exp) (args : exp list) : exp = 
  let rec build_env keys vals env = match keys, vals with
    | [], [] -> Some env
    | k :: rst_k, v :: rst_v ->
       build_env rst_k rst_v (IdMap.add k v env)
    | _ -> None
  in 
  let name_creator () : unit->string = 
    let idx = ref 0 in
    let creator () : string= 
      idx := !idx + 1;
      "%alphaconv" ^ (string_of_int !idx)
    in 
    creator
  in 
  let get_new_name : unit->string = name_creator() in
  let rec subst_rec e env = 
    let subst e = subst_rec e env in
    match e with
    | Id (_, id) -> 
       begin
         try IdMap.find id env 
         with _ -> e
       end 
    | Let (p, x, x_v, body) -> (* alpha conversion *)
       let x_v = subst_rec x_v env in
       let new_name = get_new_name() in
       let env = IdMap.add x (Id(p, new_name)) env in
       Let (p, new_name, x_v, subst_rec body env)
    | Rec (p, x, x_v, body) -> 
       (* rec should put x->newname first, and then get into x_v *)
       let new_name = get_new_name() in
       let env = IdMap.add x (Id(p, new_name)) env in
       let x_v = subst_rec x_v env in
       Rec (p, new_name, x_v, subst_rec body env)
    | Lambda (p, xs, body) ->
       (* remove each x in xs from env *)
       let filtered_env = 
         IdMap.filter (fun x _->not (List.mem x xs) ) env in
       Lambda (p, xs, subst_rec body filtered_env)
    | SetBang (p,x,v)  ->
       let v = subst_rec v env in 
       begin
         try
           let new_name = IdMap.find x env in
           match new_name with
           | Id (_, id) -> SetBang(p, id, v)
           | _ -> failwith "SetBang: id in env is not an Id"
         with _ -> failwith "SetBang finds unkown id"
       end 
    | Undefined _ 
    | Null _
    | String (_,_)
    | Num (_,_)
    | True _
    | False _ 
    | Object (_, _, _) 
    | GetAttr (_, _, _, _) 
    | SetAttr (_, _, _, _, _) 
    | GetObjAttr (_, _, _) 
    | SetObjAttr (_, _, _, _)
    | GetField (_,_,_,_)
    | SetField (_,_,_,_,_)
    | DeleteField (_,_,_)
    | OwnFieldNames (_,_)
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
    | Hint (_,_,_) -> optimize subst e in
  match f with 
  | Lambda (p, xs, body) ->
     (* #parameter and #argument may not agree *)
     let env_option = build_env xs args IdMap.empty in
     begin
       match env_option with
       | Some (env) -> subst_rec body env
       | None -> App (p, f, args)
     end 
  | _ -> App (p, f, args)

