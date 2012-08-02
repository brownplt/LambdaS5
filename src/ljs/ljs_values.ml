open Prelude
open Ljs_syntax

open Format
open FormatExt

type env = Store.loc IdMap.t
type label = string

type value =
  | Null
  | Undefined
  | Num of float
  | String of string
  | True
  | False
      (* Objects shouldn't have VarCells in them, but can have any of
      the other kinds of values *)
  | ObjLoc of Store.loc
  | Closure of env * id list * exp
and store = (objectv Store.t * value Store.t)
and objectv = attrsv * (propv IdMap.t)
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
                 proto = Null; 
                 extensible = false; 
                 klass = "LambdaJS internal"; }

let get_obj (objs, _) loc = Store.lookup loc objs
let get_var (_, vars) loc = Store.lookup loc vars

let get_maybe_obj ((objs, _) as store) loc =
  if Store.mem loc objs
  then Some (get_obj store loc)
  else None

let get_maybe_var ((_, vars) as store) loc =
  if Store.mem loc vars
  then Some (get_var store loc)
  else None

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

exception Break of exp list * label * value * store
exception Throw of exp list * value * store
exception PrimErr of exp list * value
exception Snapshot of exp list * value * env list * store


let pretty_value v = match v with
  | Num d -> string_of_float d
  | String s -> "\"" ^ s ^ "\""
  | True -> "true"
  | False -> "false"
  | Undefined -> "undefined"
  | Null -> "null"
  | ObjLoc _ -> "object"
  | Closure _ -> "function"
