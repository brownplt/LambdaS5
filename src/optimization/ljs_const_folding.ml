open Prelude
open Ljs_syntax
open Ljs_opt
module EU = Exp_util

(* Optimization phase
 * 
 * constant folding will fold two constant into one, in place.
 *)

(* TODO: should the opt phase check type error? e.g.
   to check the op1 args has the right type for op1.
 *)

(* try to simplify the op1, 
 * return new exp in option on success, None otherwise.
 * Note: the e should be a simplified exp.
 *)
let const_folding_op1 (p : Pos.t) (op : string) (e : exp) : exp option =
  EU.apply_op1 p op e

let const_folding_op2 (p : Pos.t) (op : string) (e1 : exp) (e2 : exp) : exp option = 
  EU.apply_op2 p op e1 e2

(* function for extracting property of one field *)
let rec get_obj_field (name : string) (obj_fields : (string * prop) list) : prop option = 
  match obj_fields with 
  | (fld_name, p) :: rest -> 
     if (fld_name = name) 
     then Some p
     else get_obj_field name rest  
  | [] -> None 


(* if 
      1. obj is a const object (no side effect)
      2. field name is a const, 

   try to get the field and then its attr. to make sure the

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
                
(* partially evaluate exp GetObjAttr only if 
   1. o is Object and 
   2. TODO: o does not have side effect
 *)
let const_folding_getobjattr pos (oattr : oattr) o : exp =
  match oattr, o with 
  | Klass, Object (_, {klass=klass}, _) -> String (pos, klass)
  | Code, Object (_, {code=None}, _) -> Null pos
  | Code, Object (_, {code=Some code}, _) -> code
  | Extensible, Object (_, {extensible=true},_) -> True pos
  | Extensible, Object (_, {extensible=false},_) -> False pos
  | Proto, Object (_, {proto=Some proto}, _) -> proto
  | Proto, Object (_, {proto=None}, _) -> Undefined pos
  (* primval should not be None, if it is None, leave it as it is and let
     interp issues an error on that. REF get_obj_attr in ljs_eval.ml *)
  | Primval, Object (_, {primval=Some primval},_) -> primval
  | _ -> GetObjAttr(pos, oattr, o)


let const_folding_getfield pos o f a = 
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


let valid_object_for_folding (e : exp) : bool = 
  let rec valid_checking_rec (exp : exp) : bool =
  match exp with
  | Null _ 
  | Undefined _
  | String (_,_)
  | Num (_,_)
  | True _
  | False _ -> true
  | Id (_,_) -> false
  | Object (_, attr, strprop) ->
     let { primval=primval;proto=proto;code=code;extensible = ext;klass=_ } = attr in
     let const_primval = match primval with
       | Some x -> valid_checking_rec x && not (EU.has_side_effect x)
       | None -> true 
     in
     let const_proto = match proto with 
       | Some x -> valid_checking_rec x && not (EU.has_side_effect x)
       | None -> true
     in
     let const_code = match code with
       | Some x -> valid_checking_rec x && not (EU.has_side_effect x) 
       | None -> true
     in 
     if (not const_primval || not const_proto || not const_code || ext = true) then
       false 
     else 
         let const_prop (p : string * prop) = match p with
           | (s, Data ({value = value; writable=false}, _, false)) -> 
              valid_checking_rec value && EU.has_side_effect value
           | (s, Accessor ({getter=_; setter=_},_,false)) -> true
           | _ -> false
         in
         List.for_all const_prop strprop 
  | _ -> List.for_all valid_checking_rec (child_exps exp)
  in 
  match e with
  | Object (_,_,_) -> valid_checking_rec e
  | _ -> false

let rec const_folding (e : exp) : exp =
  match e with
  | Undefined _ 
  | Null _ 
  | String (_, _)
  | Num (_, _)
  | True _ 
  | False _ 
  | Id (_, _) -> e

  | GetAttr (p, pattr, obj, field) -> 
     let o = const_folding obj in
     let f = const_folding field in
     (* todo f predicate is wrong below *)
     if valid_object_for_folding o && valid_object_for_folding f then
       const_folding_getattr p pattr o f
     else
       GetAttr (p, pattr, o, f)

  | GetObjAttr (p, oattr, obj) -> 
     let o = const_folding obj in
     if valid_object_for_folding o then
       const_folding_getobjattr p oattr o
     else 
       GetObjAttr (p, oattr, o)

  | GetField (pos, obj, fld, args) -> 
     let o = const_folding obj in
     let f = const_folding fld in
     let a = const_folding args in
     if valid_object_for_folding o && valid_object_for_folding f && valid_object_for_folding a then
       const_folding_getfield pos o f a
     else 
       GetField (pos, o, f, a)

  | Op1 (p, op, e) ->
     let newe = const_folding e in
     let v = const_folding_op1 p op newe in 
     begin
       try 
         match v with
         | Some (folded) -> folded
         | None -> Op1 (p, op, newe)
       with _ -> Op1 (p, op, newe)
     end 
  | Op2 (p, op, e1, e2) ->
     let newe1 = const_folding e1 in
     let newe2 = const_folding e2 in
     let v = const_folding_op2 p op newe1 newe2 in
     begin
       try 
         match v with
         | Some (folded) -> folded
         | None -> Op2 (p, op, newe1, newe2)
       with _ -> Op2 (p, op, newe1, newe2)
     end
  | If (p, cond, thn, els) ->
     let c_val = const_folding cond in
     begin
       match c_val with
       | True _ -> const_folding thn
       | False _ 
       | Null _
       | Undefined _
       | Num (_,_)
       | String (_,_)
       | Lambda (_,_,_)
       | Object (_,_,_) -> const_folding els 
       | _ -> 
          begin
            let t = const_folding thn in
            let e = const_folding els in
            If (p, c_val, t, e)
          end 
     end 
  | Object (_,_,_) 
  | SetAttr (_,_,_,_,_)
  | SetObjAttr (_,_,_,_)
  | SetField (_,_,_,_,_)
  | DeleteField (_, _, _) 
  | OwnFieldNames (_,_)
  | SetBang (_,_,_)
  | Lambda (_,_,_)
  | App (_,_,_) 
  | Seq (_,_,_) 
  | Let (_,_,_,_)
  | Rec (_,_,_,_)
  | Label (_,_,_)
  | Break (_,_,_)
  | TryCatch (_,_,_)
  | TryFinally (_,_,_)
  | Throw (_,_)
  | Eval (_,_,_)
  | Hint (_,_,_)
    -> optimize const_folding e

