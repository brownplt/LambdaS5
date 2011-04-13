open Prelude
open Es5_syntax

type value =
  | Null
  | Undefined
  | Num of float
  | String of string
  | True
  | False
      (* A VarCell can contain an ObjCell, but not vice versa.  This
      mimics the semantics of heap-like object refs alongside mutable
      variables *)
  | VarCell of value ref 
      (* Objects shouldn't have VarCells in them, but can have any of
      the other kinds of values *)
  | ObjCell of (attrsv * (propv IdMap.t)) ref
  | Closure of (value list -> value)
  | Fail of string
and
  attrsv = { code : value option;
             proto : value;
             extensible : bool;
             klass : string; }
and
  propv = 
  | Data of datav * bool * bool
  | Accessor of accessorv * bool * bool
  | Generic of bool * bool
and datav = { value : value; writable : bool; }
and accessorv = { getter : value; setter : value; }

let d_attrsv = { code = None; 
                 proto = Undefined; 
                 extensible = false; 
                 klass = "LambdaJS internal"; }

type env = value IdMap.t
type label = string

exception Break of label * value
exception Throw of value

let rec pretty_value v = match v with 
  | Num d -> string_of_float d
  | String s -> "\"" ^ s ^ "\""
  | True -> "true"
  | False -> "false"
  | Undefined -> "undefined"
  | Null -> "null"
  | Closure c -> "function"
  | ObjCell o -> "object"
  | VarCell v -> "&<" ^ pretty_value !v ^ ">"
  | Fail s -> "[fail: " ^ s ^ "]"

let rec pretty_value_list vs = match vs with
  | (v::vs) -> pretty_value v ^ ", " ^ pretty_value_list vs
  | [] -> ""
