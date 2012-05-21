open Prelude
open Ljs_syntax
open Ljs_pretty

open Format
open FormatExt

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
                 proto = Null; 
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

type env = Store.loc IdMap.t
type label = string

exception Break of label * value * store
exception Throw of value * store

let pretty_value v = match v with 
  | Num d -> string_of_float d
  | String s -> "\"" ^ s ^ "\""
  | True -> "true"
  | False -> "false"
  | Undefined -> "undefined"
  | Null -> "null"
  | Closure c -> "function"
  | ObjLoc o -> "object"

let pretty_valuef v = text (pretty_value v)

let rec pretty_value_store v store = match v with
  | ObjLoc loc ->
    let (avs, props) = get_obj store loc in
    let proplist = IdMap.fold (fun k v l -> (k, v)::l) props [] in
      begin match proplist with
        | [] -> braces (pretty_attrsv avs store)
        | _ ->
          braces (vert [pretty_attrsv avs store;
                        vert (vert_intersperse (text ",")
                              (map (fun p -> pretty_prop p store) proplist))])
      end
  | _ -> pretty_valuef v

and pretty_attrsv ({ proto = p; code = c; extensible = b; klass = k; primval = pv } : attrsv) store =
  let proto = [horz [text "#proto:"; pretty_valuef p]] in
  let primval = match pv with None -> []
    | Some v -> [horz [text "#prim:"; pretty_valuef v]] in
  let code = match c with None -> [] 
    | Some v -> [horz [text "#code:"; pretty_valuef v]] in
  brackets (horzOrVert (map (fun x -> squish [x; (text ",")])
                          (primval@
                            proto@
                             code@
                             [horz [text "#class:"; text ("\"" ^ k ^ "\"")]; 
                              horz [text "#extensible:"; text (string_of_bool b)]])))

and pretty_prop (f, prop) store = match prop with
  | Data ({value=v; writable=w}, enum, config) ->
    horz [text ("'" ^ f ^ "'"); text ":"; 
          braces (horzOrVert [horz [text "#value";
                                    pretty_valuef v;
                                    text ","]; 
                              horz [text "#writable"; text (string_of_bool w); text ","];
                              horz [text "#configurable"; text (string_of_bool config)]])]
  | Accessor ({getter=g; setter=s}, enum, config) ->
    horz [text ("'" ^ f ^ "'"); text ":"; braces (vert [horz [text "#getter";
                                          pretty_valuef g; text ","];
                                          horz[text "#setter";
                                               pretty_valuef s]])]

let string_of_value v store =
  (FormatExt.to_string (fun v -> pretty_value_store v store) v)

let rec pretty_value_list vs = match vs with
  | (v::vs) -> pretty_value v ^ ", " ^ pretty_value_list vs
  | [] -> ""

