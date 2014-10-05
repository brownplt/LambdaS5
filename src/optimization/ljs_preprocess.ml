open Prelude
open Ljs_syntax
open Ljs_opt

let is_obj_context = function
  | Id (_, id) -> id = "%context" || id = "%global" || id = "%globalContext"
  | _ -> false

let transform_GetField pos obj fld args =
  let get_static_str_fld e : string option = match e with
    | String (_, str) -> Some str
    | _ -> None
  in 
  match is_obj_context obj, get_static_str_fld fld with
  | true, Some(s) -> Id (pos, s)
  | _ -> GetField (pos, obj, fld, args)

(* %context["z" = fobj6, args] returns Some ("z", fobj6)
*)
let transform_SetField pos obj fld newval args : exp =
  let get_static_str_fld e : string option = match e with
    | String (_, str) -> Some str
    | _ -> None
  in 
  match is_obj_context obj, get_static_str_fld fld with
  | true, Some(s) -> SetBang (pos, s, newval)
  | _ -> SetField (pos, obj, fld, newval, args)

let rec preprocess (e : exp) : exp = 
  match e with 
  | GetField (pos, obj, fld, args) ->
    let o = preprocess obj in
    let f = preprocess fld in
    let a = preprocess args in
    transform_GetField pos o f a
  | SetField (pos, obj, fld, newval, args) ->
    let o = preprocess obj in
    let f = preprocess fld in
    let v = preprocess newval in
    let a = preprocess args in
    transform_SetField pos o f v a 
  | Seq (_, _, _)
  | Undefined _ 
  | Null _ 
  | String (_, _)
  | Num (_, _)
  | True _ 
  | False _ 
  | Id (_, _)
  | Op1 (_,_,_)
  | Op2 (_,_,_,_)
  | If (_,_,_,_)
  | App (_,_,_)
  | Label (_,_,_)
  | Object (_,_,_) 
  | GetObjAttr (_, _, _)
  | SetAttr (_,_,_,_,_)
  | GetAttr (_,_,_,_)
  | SetObjAttr (_,_,_,_)
  | DeleteField (_, _, _) 
  | OwnFieldNames (_,_)
  | SetBang (_,_,_)
  | Lambda (_,_,_)
  | Let (_,_,_,_)
  | Rec (_,_,_,_)
  | Break (_,_,_)
  | TryCatch (_,_,_)
  | TryFinally (_,_,_)
  | Throw (_,_)
  | Hint (_,_,_)
    -> optimize preprocess e


