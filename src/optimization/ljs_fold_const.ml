open Prelude
open Ljs_syntax
open Ljs_opt
module EU = Exp_util

(* TODO: should the opt phase check type error? e.g.
   to check the op1 args has the right type for op1.
 *)

(* try to simplify the op1, 
 * return new exp in option on success, None otherwise.
 * Note: the e should be a simplified exp.
 *)
let fold_const_op1 (p : Pos.t) (op : string) (e : exp) : exp option =
  EU.apply_op1 p op e

let fold_const_op2 (p : Pos.t) (op : string) (e1 : exp) (e2 : exp) : exp option = 
  EU.apply_op2 p op e1 e2

let fold_eqeq (e1 : exp) (e2 : exp) : exp option =
  let to_ans b = match b with
    | true -> Some (True Pos.dummy)
    | false -> Some (False Pos.dummy) in
  match e1, e2 with
  | Undefined _, Undefined _
  | Undefined _, Null _
  | Null _, Undefined _
  | Null _, Null _ 
  | True _, True _ 
  | False _, False _ -> to_ans true
  | True _, False _
  | False _, True _ -> to_ans false
  | Num (_, n1), Num (_, n2) -> to_ans (n1 = n2)
  | String (_, s1), String (_, s2) -> to_ans (s1 = s2)
  | _ -> None
  

let rec fold_app f args : exp option =
  let get_id e = match e with
    | Id (_, id) -> id
    | _ -> ""
  in
  match get_id f, args with
  | "%PrimAdd", [Num (p, n1); Num (_, n2)] ->
    Some (Num (p, n1 +. n2))
  | "%PrimAdd", [String (p, s1); String (_, s2)] ->
    Some (String (p, s1 ^ s2))
  | "%PrimSub", [Num (p, n1); Num (_, n2)] ->
    Some (Num (p, n1 -. n2))
  | "%EqEq", [e1; e2] -> fold_eqeq e1 e2
  | "", _
  | _ -> None
    
let rec fold_const (e : exp) : exp =
  match e with
  | Undefined _ 
  | Null _ 
  | String (_, _)
  | Num (_, _)
  | True _ 
  | False _ 
  | Id (_, _) -> e
  | Op1 (p, op, e) ->
     let newe = fold_const e in
     begin match fold_const_op1 p op newe with
       | Some (folded) -> folded
       | None -> Op1 (p, op, newe)
     end
  | Op2 (p, op, e1, e2) ->
     let newe1 = fold_const e1 in
     let newe2 = fold_const e2 in
     begin match fold_const_op2 p op newe1 newe2 with
       | Some (folded) -> folded
       | None -> Op2 (p, op, newe1, newe2)
     end
  | If (p, cond, thn, els) ->
     let c_val = fold_const cond in
     begin
       match c_val with
       | True _ -> fold_const thn
       | False _ 
       | Null _
       | Undefined _
       | Num (_,_)
       | String (_,_)
       | Lambda (_,_,_)
       | Object (_,_,_) -> fold_const els 
       | _ -> 
          begin
            let t = fold_const thn in
            let e = fold_const els in
            If (p, c_val, t, e)
          end 
     end
  | App (p, f, args) ->
    let f = fold_const f in
    let args = List.map fold_const args in
    begin match fold_app f args with
      | Some (newexp) -> newexp
      | None -> App (p, f, args)
    end
  | GetAttr (_, _, _, _)
  | GetObjAttr (_, _, _)
  | GetField (_, _, _, _)
  | Object (_,_,_) 
  | SetAttr (_,_,_,_,_)
  | SetObjAttr (_,_,_,_)
  | SetField (_,_,_,_,_)
  | DeleteField (_, _, _) 
  | OwnFieldNames (_,_)
  | SetBang (_,_,_)
  | Lambda (_,_,_)
  | Seq (_,_,_) 
  | Let (_,_,_,_)
  | Rec (_,_,_,_)
  | Label (_, _, _)
  | TryCatch (_, _, _)
  | Break (_,_,_)
  | TryFinally (_,_,_)
  | Throw (_,_)
  | Hint (_,_,_)
  | Eval (_,_,_)
    -> optimize fold_const e

