open Prelude
open Ljs_syntax
module EU = Exp_util

type env = exp IdMap.t 


(* attrs contains expression option.
   f is a function that will apply to those expression options.
 *)
let apply_to_attr (f : exp->exp) (attr : attrs) = 
  let apply_to_option (opt : exp option) : exp option = match opt with
    | Some(e) -> Some (f e)
    | None -> None
  in 
  let res = { primval= apply_to_option attr.primval;
              code = apply_to_option attr.code;
              proto = apply_to_option attr.proto;
              klass = attr.klass; 
              extensible = attr.extensible} in
  res
    
let rec apply_to_props (f : exp->exp) 
                       (props : (string * prop) list) : (string * prop) list =
  let handle_prop p = match p with
    | (s, Data (data, enum, config)) ->
       s, Data ({value = f data.value; writable = data.writable}, enum, config)
    | (s, Accessor (acc, enum, config)) ->
       s, Accessor ({getter = f acc.getter; setter = f acc.setter}, enum, config) 
  in
  List.map handle_prop props
           

let rec optimize (optimizer : exp->exp) (e : exp) : exp =
  match e with
  | Undefined _
  | Null _
  | String (_,_)
  | Num (_,_)
  | True _
  | False _ 
  | Id _ -> optimizer e
  | Object (p, attrs, props) ->
     let new_attrs = apply_to_attr optimizer attrs in
     let new_props = apply_to_props optimizer props in
     Object (p, new_attrs, new_props)

  | GetAttr(p, pattr, obj, field) ->
     let o = optimizer obj in
     let f = optimizer field in
     GetAttr (p, pattr, o, f)

  | SetAttr (p, attr, obj, field, newval) ->
     let o = optimizer obj in
     let f = optimizer field in
     let v = optimizer newval in
     SetAttr (p, attr, o, f, v)

  | GetObjAttr (p, oattr, obj) ->
     let o = optimizer obj in
     GetObjAttr(p, oattr, o)

  | SetObjAttr (p, oattr, obj, attre) ->
     let o = optimizer obj in
     let attr = optimizer attre in
     SetObjAttr (p, oattr, o, attr)

  | GetField (p, obj, fld, args) -> 
     let o = optimizer obj in
     let f = optimizer fld in
     let a = optimizer args in
     GetField (p, o, f, a)

  | SetField (p, obj, fld, newval, args) ->
     let o = optimizer obj in
     let f = optimizer fld in
     let v = optimizer newval in
     let a = optimizer args in
     SetField (p, o, f, v, a)

  | DeleteField (p, obj, fld) ->
     let o = optimizer obj in
     let f = optimizer fld in
     DeleteField (p, o, f)

  | OwnFieldNames (p, obj) -> 
     OwnFieldNames (p, optimizer obj)

  | SetBang (p, x, e) ->
     SetBang (p, x, optimizer e)

  | Op1 (p, op, e) ->
     Op1 (p, op, optimizer e)

  | Op2 (p, op, e1, e2) ->
     Op2 (p, op, optimizer e1, optimizer e2)

  | If (p, cond, thn, els) -> 
     If (p, optimizer cond, optimizer thn, optimizer els)

  | App (p, func, args) ->
     let f = optimizer func in
     let a = List.map (fun x->optimizer x) args in
     App (p, f, a)

  | Seq (p, e1, e2) ->
     let new_e1 = optimizer e1 in
     let new_e2 = optimizer e2 in
     Seq (p, new_e1, new_e2)

  | Let (p, x, exp, body) ->
     let x_v = optimizer exp in
     let v_body = optimizer body in
     Let (p, x, x_v, v_body)

  | Rec (p, x, exp, body) -> 
     let x_v = optimizer exp in
     let v_body = optimizer body in
     Rec (p, x, x_v, v_body)

  | Label (p, l, e) ->
     let new_e = optimizer e in
     Label (p, l ,new_e)

  | Break (p, l, e) ->
     let new_e = optimizer e in
     Break (p, l ,new_e)
           
  | TryCatch (p, body, catch) ->
     let b = optimizer body in
     let c = optimizer catch in
     TryCatch (p, b, c)

  | TryFinally (p, body, fin) ->
     let b = optimizer body in
     let f = optimizer fin in
     TryFinally (p, b, f)

  | Throw (p, e) ->
     let e = optimizer e in
     Throw (p, e)

  | Lambda (p, xs, e) -> 
     let e = optimizer e in
     Lambda (p, xs, e)

  | Eval (p, e, bindings) ->
     let e = optimizer e in
     let bindings = optimizer bindings in
     Eval (p, e, bindings)

  | Hint (p, id, e) ->
     let e = optimizer e in
     Hint (p, id, e)


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
