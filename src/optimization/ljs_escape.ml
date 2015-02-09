open Prelude
open Ljs_syntax
open Exp_util
(* simplified escape analysis for s5 code *)

type escape_t =
  (* called as a function *)
  | Called
  (* used as function argument *)
  | Escaped
  (* x has alias. e.g. y := x; o["fld"=x]; {[#value x]} *)
  | Aliased
  (* x is used as an object for fetching property *)
  | GetProperty
  (* x is used as an object for setting property *)
  | SetProperty
  (* x is used as an object for fetching object attribute *)
  | GetObjectAttribute
  (* | LetBounded *)

module EscapeOrderedType = struct
  type t = escape_t
  let compare = Pervasives.compare
end

module EscapeSet = SetExt.Make (EscapeOrderedType)

(* to check whether exp is Id and the id is in the given id set *)
let is_the_id (exp : exp) (ids : IdSet.t) : bool =
  match exp with
  | Id (_, i) -> IdSet.mem i ids
  | _ -> false

let escape (id : id) (exp : exp) : EscapeSet.t = 
  let rec escape_rec (ids : IdSet.t) (exp : exp) : EscapeSet.t = 
    match exp with
    | Null _
    | Undefined _
    | String (_, _)
    | Num (_, _)
    | True _
    | False _ 
    | Id (_, _) -> EscapeSet.empty
    | Object (_, attrs, props) ->
      (* check alias in Object *)
    | GetObjAttr (_, _, o) when is_the_id o ids ->
      EscapeSet.singleton GetObjectAttribute
    | GetField (_, o, fld, arg) when is_the_id o ids ->
      let fld_res = escape_rec ids fld in
      let arg_res = escape_rec ids arg in
      fld_res
      |> EscapeSet.union arg_res
      |> EscapeSet.union (EscapeSet.singleton GetProperty)
    | SetField (_, o, fld, v, arg) ->
      let result =
        if is_the_id o ids then
          EscapeSet.singleton SetProperty
        else if is_the_id v ids then
          EscapeSet.singleton Aliased
        else
          EscapeSet.empty
      in
      let fld_res = escape_rec ids fld in
      let v_res = escape_rec ids v in
      let arg_res = escape_rec ids arg in
      fld_res
      |> EscapeSet.union v_res
      |> EscapeSet.union arg_res
      |> EscapeSet.union result
    | SetField (_, o, fld, v, arg) when is_the_id v ids ->
      
    | SetBang (_, x, x_v) ->
      let xv_res = escape_rec ids x_v in
      if IdSet.mem x ids then
        EscapeSet.union xv_res (EscapeSet.singleton Aliased)
      else
        xv_res
    | App (_, f, args) when is_the_id f ids ->
      EscapeSet.unions (List.map (fun e -> escape_rec ids e) args)
      |> EscapeSet.union (EscapeSet.singleton Called)
    | Let (_, x, x_v, body) when is_the_id x_v ids ->
      if IdSet.mem x ids then
        escape_rec ids body
      else
        let ids = IdSet.add x ids in
        escape_rec ids body
    | Let (_, x, x_v, body) ->
      let xv_res = escape_rec ids x_v in
      let ids = if IdSet.mem x ids then
          IdSet.remove x ids
        else
          IdSet.add x ids
      in
      xv_res
      |> EscapeSet.union (escape_rec ids body)
    | Rec (_, x, x_v, body) ->
      let ids = if IdSet.mem x ids then
          IdSet.remove x ids
        else
          IdSet.add x ids
      in
      escape_rec ids x_v
      |> EscapeSet.union (escape_rec ids body)
    | Lambda (_, xs, body) ->
      let ids = List.fold_right IdSet.remove xs ids in
      escape_rec ids body
    | Label (_, _, _)
    | Break (_, _, _)
    | TryCatch (_, _, _)
    | TryFinally (_, _, _)
    | Throw (_, _)
    | Seq (_, _, _)
    | Op1 (_, _, _)
    | Op2 (_, _, _, _)
    | If (_, _, _, _)
    | DeleteField (_, _, _)
    | SetObjAttr (_, _, _, _)
    | GetAttr (_, _, _, _)
    | SetAttr (_, _, _, _, _)
    | Object (_, _, _)
    | GetObjAttr (_, _, _)
    | GetField (_, _, _, _)
    | OwnFieldNames (_, _)
    | App (_, _, _)
    | Hint (_, _, _)
      ->
      EscapeSet.unions
        (List.map
           (fun e -> escape_rec ids e) (child_exps exp))
  in
  escape_rec (IdSet.singleton id) exp
