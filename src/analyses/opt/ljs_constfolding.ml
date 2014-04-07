module S = Ljs_syntax

(* TODO: should the opt phase check type error? e.g.
   to check the op1 args has the right type for op1.
 *)

(* consts are either 
   Undefined, Null, String, Num, True, False
   XXX: what about Lambdas?
 *)

(* TODO: for the condition of if, it seems to only check the constant 
 * is not enough, what about "If (Lambda) thn els", this can be
 * evaluate to true *)
(* to check if an expression is a constant *)
let is_constant (e : S.exp) : bool =
  | Undefined _ -> true
  | Null _ -> true 
  | String (_, _) -> true
  | Num (_, _) -> true 
  | True _ ->  true 
  | False _ -> true
  | _ -> false

(* to check if the value of an constant expression is true.
 * assumption: the exp passed in is a constant 
 * see Ljs_delta.ml prim_to_bool *)
let is_true (e : S.exp) : bool =
  assert (is_constant e);
  match e with
  | Undefined _ -> false
  | Null _ -> false
  | False _ -> false
  | String (_, s) -> not (string_len s = 0)
  | Num (_, n) -> not (x == nan || x = 0.0 || x = -0.0)
  | _ -> true

(* try to simplify the op1, 
 * return new exp in option on success, None otherwise.
 * Note: the e should be a simplified exp.
 *)
let const_folding_op1 (op : string) (e : S.exp) : S.exp option =
  None

let const_folding_op2 (op : string) (e1 : S.exp) (e2 : S.exp) : S.exp option = 
  None
  
let const_folding (e : S.exp) : S.exp =
  match e with
  | S.Undefined _ -> e
  | S.Null _ -> e
  | S.String (_, _) -> e
  | S.Num (_, n) -> e
  | S.True _ -> e
  | S.False _ -> e
  | S.Id (p, x) -> e
  | S.Object (_, _, _) -> e
  | S.GetAttr (p, attr, obj, field) ->
     let o = const_folding obj in
     let f = const_folding field in
     S.GetAttr p attr o f
  | S.SetAttr (p, attr, obj, field, newval) ->
     let o = const_folding obj in
     let f = const_folding field in
     let v = const_folding newval in
     S.SetAttr p, attr, o, f, v
  | S.GetObjAttr (p, oattr, obj) ->
     S.GetObjAttr p oattr (const_folding obj)
  | S.SetObjAttr (p, oattr, obj, attre) ->
     let o = const_folding obj in
     let attr = const_folding attre in
     S.SetObjAttr p oattr o attr
  | S.GetField (p, obj, fld, args) ->
     let o = const_folding obj in
     let f = const_folding fld in
     let a = const_folding args in
     S.GetField p o f a
  | S.SetField (p, obj, fld, newval, args) ->
     let o = const_folding obj in
     let f = const_folding fld in
     let v = const_folding newval in
     let a = const_folding args in
     S.SetField p o f v a
  | S.DeleteField (p, obj, fld) -> 
     let o = const_folding obj in
     let f = const_folding fld in
     S.DeleteField p o f
  | S.OwnFieldNames (p, obj) ->
     S.OwnFieldNames p (const_folding obj)
  | S.SetBang (p, x, e) ->
     S.SetBang p x (const_folding e)
  | S.Op1 (p, op, e) ->
     let newe = const_folding e in
     let v = const_folding_op1 op newe in
     match v with
     | Some (folded) -> folded
     | None -> S.Op1 p op newe
  | S.Op2 (p, op, e1, e2) ->
     let newe1 = const_folding e1 in
     let newe2 = const_folding e2 in
     let v = const_folding_op2 op newe1 newe2 in
     match v with
     | Some (folded) -> folded
     | None -> S.Op2 p op newe1 newe2
  | S.If (p, cond, thn, els) ->
     let c_val = const_folding cond in
     if (is_constant c_val)
     then if (is_true c_val)
          then const_folding thn
          else const_folding els
     else 
       let t = const_folding thn in
       let e = const_folding els in
       S.If p c_val t e
  | S.App (p, func, args) ->
     let f = const_folding func in
     let a = List.Map const_folding args in
     S.App p f a
  | S.Seq (p, e1, e2) ->
     let new_e1 = const_folding e1 in
     let new_e2 = const_folding e2 in
     S.Seq p new_e1 new_e2
  | S.Let (p, x, e, body) ->
     let new_e = const_folding e in
     let new_body = const_folding body in
     S.Let p x new_e new_body
  | S.Rec (p, x, e, body) ->
     let new_e = const_folding e in
     let new_body = const_folding body in
     S.Rec p x new_e new_body
  | S.Label (p, l, e) ->
     let new_e = const_folding e in
     S.Label p l new_e
  | S.Break (p, l, e) ->
     let new_e = const_folding e in
     S.Break p l new_e
    (* TODO: can we do anything with TryCatch in constant folding? *)
  | S.TryCatch (p, body, catch) ->
     let b = const_folding body in
     let c = const_folding catch in
     S.TryCatch p b c
  | S.TryFinally (p, body, fin) ->
     let b = const_folding body in
     let f = const_folding fin in
     S.TryFinally p b f
  | S.Throw (p, e) ->
     S.Throw p (const_folding e)
  | S.Lambda (p, xs, e) ->
     S.Lambda p xs (const_folding e)
  | S.Eval (p, e, bindings) ->
     let new_e = const_folding e in
     let new_bindings = const_folding bindings in
     S.Eval p new_e new_bindings
  | S.Hint (p, id, e) -> 
     S.Hint p id (const_folding e)
