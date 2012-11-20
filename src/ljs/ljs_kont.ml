open Prelude
open Store
open Ljs_values
module S = Ljs_syntax

type id = string

(* when I write "we'll have n cases for this...", it means we'll match the
   expressions to see if they're values, if they are we just move on to the
   next (immediately right) exp, if there are no more exps, we move on. *)

type kont =
(* exp type continuations *)
  | SetBang of loc * kont
  (* primval * codexp opt * codeval opt * protoexp opt * protoval opt *  *)
  | GetAttr of S.pattr * value option * S.exp option * kont
  | SetAttr of S.pattr * value option * S.exp option * value option * S.exp option * kont
  | GetObjAttr of S.oattr * kont
  | SetObjAttr of S.oattr * value option * S.exp option * kont
  | GetField of Pos.t * value option * S.exp option * value option * S.exp option * env * bool * kont
  | SetField of Pos.t * value option * S.exp option * value option * S.exp option * value option * S.exp option * env * bool * kont
  | OwnFieldNames of kont
  | DeleteField of Pos.t * value option * S.exp option * kont
  | Op1 of string * kont
  | Op2 of string * value option * S.exp option * kont
  | Mt
  | If of env * S.exp * S.exp * kont
  | App of Pos.t * value option * env * value list * S.exp list * bool * kont
  | Seq of S.exp * kont
  | Let of id * S.exp * kont
  | Rec of loc * S.exp * kont
  | Break of id * kont
  | TryCatch of Pos.t * S.exp option * env * value option * kont
  | TryFinally of S.exp option * env * exn option * kont
  | Throw
  | Eval of Pos.t * value option * S.exp option * store * kont
  | Hint
  | Object of attrsv option * (string * S.prop) list * (string * propv) list * kont
(* attr continuation *)
  | Attrs of string * (string * S.exp) list * (string * value) list * string * bool * kont
(* property continuation *)
  | DataProp of string * bool * bool * bool * kont
  | AccProp of string * value option * S.exp option * bool * bool * kont
