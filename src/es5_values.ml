open Prelude
open JavaScript_syntax
open Es5_syntax

type value =
  | Const of JavaScript_syntax.const
      (* A VarCell can contain an ObjCell, but not vice versa.  This
      mimics the semantics of heap-like object refs alongside mutable
      variables *)
  | VarCell of value ref 
      (* Objects shouldn't have VarCells in them, but can have any of
      the other kinds of values *)
  | ObjCell of (value IdMap.t * ((value AttrMap.t) IdMap.t)) ref
  | Closure of (value list -> value)
  | Fail of string

type env = value IdMap.t
type label = string

exception Break of label * value
exception Throw of value

let rec pretty_value v = match v with 
  | Const c -> begin match c with
      | CInt d -> string_of_int d
      | CNum d -> string_of_float d
      | CString s -> "\"" ^ s ^ "\""
      | CBool b -> string_of_bool b
      | CUndefined -> "undefined"
      | CNull -> "null"
    end
  | Closure c -> "function"
  | ObjCell o -> "object"
  | VarCell v -> "&<" ^ pretty_value !v ^ ">"
  | Fail s -> "[fail: " ^ s ^ "]"

let rec pretty_value_list vs = match vs with
  | (v::vs) -> pretty_value v ^ ", " ^ pretty_value_list vs
  | [] -> ""
