open Prelude
open Ljs_syntax
module EV = Exp_val

(* Optimization phase
 * 
 * constant folding will fold two constant into one, in place.
 *)

(* TODO: should the opt phase check type error? e.g.
   to check the op1 args has the right type for op1.
 *)

(* to check if the value of an constant expression is true. 
   if the argument passed in is not a const, return None
TODO: what about lambda and object
*)
let is_true (e : exp) : bool option =
  match e with
  | Undefined _ -> Some false
  | Null _ -> Some false
  | False _ -> Some false
  | True _ -> Some true
  | String (_, s) -> Some (not (String.length s = 0))
  | Num (_, x) -> Some (not (x == nan || x = 0.0 || x = -0.0))
  | _ -> None

(* try to simplify the op1, 
 * return new exp in option on success, None otherwise.
 * Note: the e should be a simplified exp.
 *)
let const_folding_op1 (p : Pos.t) (op : string) (e : exp) : exp option =
  EV.apply_op1 p op e

let const_folding_op2 (p : Pos.t) (op : string) (e1 : exp) (e2 : exp) : exp option = 
  EV.apply_op2 p op e1 e2


(* function for extracting property of one field *)
let rec get_obj_field (name : string) (obj_fields : (string * prop) list) : prop option = 
  match obj_fields with 
  | (fld_name, p) :: rest -> 
     if (fld_name = name) 
     then Some p
     else get_obj_field name rest  
  | [] -> None 


(* if object is a const object and field name is a const, 
   try to get the field and then its attr. to make sure the
   result code not bigger, only const folding should only apply to 
   a const attr.

   partially evaluate exp GetAttr. This optimization can shink the code
   only if the `obj` is an Object appearing only once in the code. substitute_const 
   will do that.

   *)
let const_folding_getattr pos pattr obj field : exp = 
  let exp_bool (b : bool) : exp = match b with
    | true -> True pos
    | false -> False pos in

  match obj, field with 
  | Object (_, attrs, strprop), String (_, name) -> 
     (* get field and its property *)
     begin match get_obj_field name strprop with
     | Some prop -> 
        begin
          match pattr, prop with 
          | Value, Data ({value = v; writable=_}, _, _) -> v
          | Writable, Data({value=_; writable=w}, _, _) -> exp_bool w
          | Enum, Data(_, enum, _) -> exp_bool enum
          | Config, Data (_, _, config) -> exp_bool config
          | _ -> GetAttr(pos, pattr, obj, field) (* no optimization in other situations *)
        end
     | None -> GetAttr(pos, pattr, obj, field) (* if field is not in the object. don't optimize. *)
     end
  | _ -> GetAttr(pos, pattr, obj, field)
 
(* partially evaluate exp GetObjAttr. This optimization can shink the code
   only if the `o` is an Object appearing only once in the code. substitute_const 
   will do that.

TODO: maybe we can do more on this? since o is Object, maybe we can get all attr directly.
 *)
let const_folding_getobjattr pos (oattr : oattr) o : exp =
  match oattr, o with 
  | Klass, Object (_, {klass=klass}, _) -> String (pos, klass)
  | Code, Object (_, {code=None}, _) -> Null pos
  | Code, Object (_, {code=Some code}, _) -> code
  | Extensible, Object (_, {extensible=ext},_) ->
     if ext then True pos else False pos
  | Proto, Object (_, {proto=Some proto}, _) -> proto
  | Proto, Object (_, {proto=None}, _) -> Null pos
  | _ -> GetObjAttr(pos, oattr, o)

let rec const_folding (e : exp) : exp =
  let const_folding_option (o : exp option) : exp option =
    match o with
    | Some (o) -> Some (const_folding o)
    | None -> None in
  match e with
  | Undefined _ -> e
  | Null _ -> e
  | String (_, _) -> e
  | Num (_, n) -> e
  | True _ -> e
  | False _ -> e
  | Id (p, x) -> e
  | Object (p, attr, strprop) -> 
     let new_attrs = {
       primval = const_folding_option attr.primval;
       code = const_folding_option attr.code;
       proto = const_folding_option attr.proto;
       klass = attr.klass;
       extensible = attr.extensible
     } in
     let handle_prop p = match p with 
       | (s, Data (data, b1, b2)) ->
          s, Data ({value = const_folding data.value; 
                      writable = data.writable}, b1, b2)
       | (s, Accessor (acc, b1, b2)) -> 
          s, Accessor ({getter = const_folding acc.getter; 
                        setter = const_folding acc.setter},
                       b1, b2) in
     let prop_list = List.map handle_prop strprop in
     Object (p, new_attrs, prop_list)

  | GetAttr (p, pattr, obj, field) -> 
     let o = const_folding obj in
     let f = const_folding field in
     const_folding_getattr p pattr o f

  | SetAttr (p, attr, obj, field, newval) ->
     let o = const_folding obj in
     let f = const_folding field in
     let v = const_folding newval in
     SetAttr (p, attr, o, f, v)

  | GetObjAttr (p, oattr, obj) -> 
     let o = const_folding obj in     
     const_folding_getobjattr p oattr o

  | SetObjAttr (p, oattr, obj, attre) ->
     let o = const_folding obj in
     let attr = const_folding attre in
     SetObjAttr (p, oattr, o, attr)

  | GetField (pos, obj, fld, args) -> 
     let o = const_folding obj in
     let f = const_folding fld in
     let a = const_folding args in
     begin
       match o, f with
       | Object (_, _, strprop), String (_, fld) ->
          begin
            let p = get_obj_field fld strprop in 
            match p with
            | None -> Undefined pos
            | Some (Data ({value=v; writable=_},_,_)) -> v
            | _ -> failwith "opt on field containing accessors are not implemented"
          end
       | _ -> GetField (pos, o, f, a)
     end
  | SetField (p, obj, fld, newval, args) ->
     let o = const_folding obj in
     let f = const_folding fld in
     let v = const_folding newval in
     let a = const_folding args in
     SetField (p, o, f, v, a)

  | DeleteField (p, obj, fld) -> 
     let o = const_folding obj in
     let f = const_folding fld in
     DeleteField (p, o, f)

  | OwnFieldNames (p, obj) -> (* TODO: opt this to what? *)
     let o = const_folding obj in
     OwnFieldNames (p, o)

  | SetBang (p, x, e) ->
     SetBang (p, x, (const_folding e))

  | Op1 (p, op, e) ->
     let newe = const_folding e in
     let v = const_folding_op1 p op newe in 
     begin
       match v with
       | Some (folded) -> folded
       | None -> Op1 (p, op, newe)
     end 
  | Op2 (p, op, e1, e2) ->
     let newe1 = const_folding e1 in
     let newe2 = const_folding e2 in
     let v = const_folding_op2 p op newe1 newe2 in
     begin
       match v with
       | Some (folded) -> folded
       | None -> Op2 (p, op, newe1, newe2)
     end
  | If (p, cond, thn, els) ->
     let c_val = const_folding cond in
     begin
       match (is_true c_val) with
       | Some (v) ->
          if v 
          then const_folding thn
          else const_folding els
       | None -> (* cannot fold *)
          let t = const_folding thn in
          let e = const_folding els in
          If (p, c_val, t, e)
     end 
  | App (p, func, args) ->
     let f = const_folding func in
     let a = List.map const_folding args in
     App (p, f, a)
  | Seq (p, e1, e2) ->
     let new_e1 = const_folding e1 in
     let new_e2 = const_folding e2 in
     Seq (p, new_e1, new_e2)
  | Let (p, x, e, body) ->
     let new_e = const_folding e in
     let new_body = const_folding body in
     Let (p, x, new_e, new_body)
  | Rec (p, x, e, body) ->
     let new_e = const_folding e in
     let new_body = const_folding body in
     Rec (p, x, new_e, new_body)
  | Label (p, l, e) ->
     let new_e = const_folding e in
     Label (p, l, new_e)
  | Break (p, l, e) ->
     let new_e = const_folding e in
     Break (p, l, new_e)
  | TryCatch (p, body, catch) ->
     let b = const_folding body in
     let c = const_folding catch in
     TryCatch (p, b, c)
  | TryFinally (p, body, fin) ->
     let b = const_folding body in
     let f = const_folding fin in
     TryFinally (p, b, f)
  | Throw (p, e) ->
     Throw (p, (const_folding e))
  | Lambda (p, xs, e) ->
     Lambda (p, xs, (const_folding e))
  | Eval (p, e, bindings) ->
     let new_e = const_folding e in
     let new_bindings = const_folding bindings in
     Eval (p, new_e, new_bindings)
  | Hint (p, id, e) -> 
     Hint (p, id, (const_folding e))
