open Prelude
module S = Ljs_syntax
module OP = Op1_op2

(* TODO: should the opt phase check type error? e.g.
   to check the op1 args has the right type for op1.
 *)

(* to check if the value of an constant expression is true. 
   if the argument passed in is not a const, return None
*)
let is_true (e : S.exp) : bool option =
  match e with
  | S.Undefined _ -> Some false
  | S.Null _ -> Some false
  | S.False _ -> Some false
  | S.True _ -> Some true
  | S.String (_, s) -> Some (not (String.length s = 0))
  | S.Num (_, x) -> Some (not (x == nan || x = 0.0 || x = -0.0))
  | S.Lambda (_, _, _) -> Some true
  | _ -> None

let is_contant(e : S.exp) : bool= 
  match e with
  | S.Undefined _
  | S.Null _
  | S.False _
  | S.True _
  | S.String (_, _)
  | S.Num (_, _)
  | S.Object (_, _, _)
  | S.Lambda (_, _, _) -> true
  | _ -> false 

(* try to simplify the op1, 
 * return new exp in option on success, None otherwise.
 * Note: the e should be a simplified exp.
 *)
let const_folding_op1 (p : Pos.t) (op : string) (e : S.exp) : S.exp option =
  OP.op1 p op e

let const_folding_op2 (p : Pos.t) (op : string) (e1 : S.exp) (e2 : S.exp) : S.exp option = 
  OP.op2 p op e1 e2

(* obj and field should be simplified before passing it *)  
let const_folding_GetAttr p pattr obj field = 
  match obj with 
  | S.Object (_, attrs, props) ->
     begin
       match field with
         (* TODO: here check the field for optimizing *)
       | _ -> S.GetAttr (p, pattr, obj, field)
     end
  | _ -> S.GetAttr (p, pattr, obj, field)

let rec const_folding (e : S.exp) : S.exp =
  match e with
  | S.Undefined _ -> e
  | S.Null _ -> e
  | S.String (_, _) -> e
  | S.Num (_, n) -> e
  | S.True _ -> e
  | S.False _ -> e
  | S.Id (p, x) -> e
  | S.Object (_, _, _) -> e
  | S.GetAttr (p, pattr, obj, field) -> (* TODO: opt this *)
     let o = const_folding obj in
     let f = const_folding field in
     const_folding_GetAttr p pattr o f
  | S.SetAttr (p, attr, obj, field, newval) ->
     let o = const_folding obj in
     let f = const_folding field in
     let v = const_folding newval in
     S.SetAttr (p, attr, o, f, v)
  | S.GetObjAttr (p, oattr, obj) -> (* TODO: opt this *)
     S.GetObjAttr (p, oattr, (const_folding obj))
  | S.SetObjAttr (p, oattr, obj, attre) ->
     let o = const_folding obj in
     let attr = const_folding attre in
     S.SetObjAttr (p, oattr, o, attr)
  | S.GetField (p, obj, fld, args) -> (* TODO: opt this *)
     let o = const_folding obj in
     let f = const_folding fld in
     let a = const_folding args in
     S.GetField (p, o, f, a)
  | S.SetField (p, obj, fld, newval, args) ->
     let o = const_folding obj in
     let f = const_folding fld in
     let v = const_folding newval in
     let a = const_folding args in
     S.SetField (p, o, f, v, a)
  | S.DeleteField (p, obj, fld) -> 
     let o = const_folding obj in
     let f = const_folding fld in
     S.DeleteField (p, o, f)
  | S.OwnFieldNames (p, obj) -> (* TODO: opt this *)
     S.OwnFieldNames (p, (const_folding obj))
  | S.SetBang (p, x, e) ->
     S.SetBang (p, x, (const_folding e))
  | S.Op1 (p, op, e) ->
     let newe = const_folding e in
     let v = const_folding_op1 p op newe in 
     begin
       match v with
       | Some (folded) -> folded
       | None -> S.Op1 (p, op, newe)
     end 
  | S.Op2 (p, op, e1, e2) ->
     let newe1 = const_folding e1 in
     let newe2 = const_folding e2 in
     let v = const_folding_op2 p op newe1 newe2 in
     begin
       match v with
       | Some (folded) -> folded
       | None -> S.Op2 (p, op, newe1, newe2)
     end
  | S.If (p, cond, thn, els) ->
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
          S.If (p, c_val, t, e)
     end 
  | S.App (p, func, args) ->
     let f = const_folding func in
     let a = List.map const_folding args in
     S.App (p, f, a)
  | S.Seq (p, e1, e2) ->
     let new_e1 = const_folding e1 in
     let new_e2 = const_folding e2 in
     S.Seq (p, new_e1, new_e2)
  | S.Let (p, x, e, body) ->
     let new_e = const_folding e in
     let new_body = const_folding body in
     S.Let (p, x, new_e, new_body)
  | S.Rec (p, x, e, body) ->
     let new_e = const_folding e in
     let new_body = const_folding body in
     S.Rec (p, x, new_e, new_body)
  | S.Label (p, l, e) ->
     let new_e = const_folding e in
     S.Label (p, l, new_e)
  | S.Break (p, l, e) ->
     let new_e = const_folding e in
     S.Break (p, l, new_e)
  | S.TryCatch (p, body, catch) ->
     let b = const_folding body in
     let c = const_folding catch in
     S.TryCatch (p, b, c)
  | S.TryFinally (p, body, fin) ->
     let b = const_folding body in
     let f = const_folding fin in
     S.TryFinally (p, b, f)
  | S.Throw (p, e) ->
     S.Throw (p, (const_folding e))
  | S.Lambda (p, xs, e) ->
     S.Lambda (p, xs, (const_folding e))
  | S.Eval (p, e, bindings) ->
     let new_e = const_folding e in
     let new_bindings = const_folding bindings in
     S.Eval (p, new_e, new_bindings)
  | S.Hint (p, id, e) -> 
     S.Hint (p, id, (const_folding e))
