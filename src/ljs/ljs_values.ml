open Prelude
open Ljs_syntax

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
  | VarLoc of Store.loc
      (* Objects shouldn't have VarCells in them, but can have any of
      the other kinds of values *)
  | ObjLoc of Store.loc
  | Closure of (value list -> store -> (value * store))
and store = ((attrsv * (propv IdMap.t)) Store.t * value Store.t)
and
  attrsv = { code : value option;
             proto : value;
             extensible : bool;
             klass : string;
             primval : value option; }
and
  propv = 
  | Data of datav * bool * bool
  | Accessor of accessorv * bool * bool
and datav = { value : value; writable : bool; }
and accessorv = { getter : value; setter : value; }

let d_attrsv = { primval = None;
                 code = None; 
                 proto = Undefined; 
                 extensible = false; 
                 klass = "LambdaJS internal"; }

let get_obj (objs, _) loc = Store.lookup loc objs
let get_var (_, vars) loc = Store.lookup loc vars

let set_obj ((objs, vars) : store) (loc : Store.loc) new_obj =
  (Store.update loc new_obj objs), vars
let set_var (objs, vars) loc new_val =
  (objs, Store.update loc new_val vars)

let add_obj (objs, vars) new_obj =
  let new_loc, objs' = Store.alloc new_obj objs in
  new_loc, (objs', vars)
let add_var (objs, vars) new_val =
  let new_loc, vars' = Store.alloc new_val vars in
  new_loc, (objs, vars')

type env = value IdMap.t
type label = string

exception Break of label * value * store
exception Throw of value * store

let rec pretty_value v = match v with 
  | Num d -> string_of_float d
  | String s -> "\"" ^ s ^ "\""
  | True -> "true"
  | False -> "false"
  | Undefined -> "undefined"
  | Null -> "null"
  | Closure c -> "function"
  | ObjLoc o -> "object"
  | VarLoc v -> "&<" ^ Store.print_loc v ^ ">"

let rec pretty_value_list vs = match vs with
  | (v::vs) -> pretty_value v ^ ", " ^ pretty_value_list vs
  | [] -> ""

