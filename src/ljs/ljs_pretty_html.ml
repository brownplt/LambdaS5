open Format
open Prelude
open Ljs_values
open Html

module LocMap = Store.LocMap

let print_loc = Store.print_loc


let html_of_null = style "constant" (text "null")
let html_of_undefined = style "constant" (text "undefined")
let html_of_bool bool = style "constant" (text (string_of_bool bool))
let html_of_string string = style "string" (text string)
let html_of_float float = style "number" (text (string_of_float float))

let html_of_objloc loc =
  anchor ("obj" ^ print_loc loc) [style "objloc" (text (print_loc loc))]
let html_of_varloc loc =
  anchor ("var" ^ print_loc loc) [style "varloc" (text (print_loc loc))]
let html_of_objref loc =
  anchor_link ("obj" ^ print_loc loc) [style "objref" (text (print_loc loc))]
let html_of_varref loc =
  anchor_link ("var" ^ print_loc loc) [style "varref" (text (print_loc loc))]


let html_of_env env =
  let html_of_binding (id, var) = row [cell [style "id" (text id)];
									   cell [html_of_varref var]] in
  table (map html_of_binding (IdMap.bindings env))

let html_of_value value = match value with
  | Null -> html_of_null
  | Undefined -> html_of_undefined
  | True -> html_of_bool true
  | False -> html_of_bool false
  | Num n -> html_of_float n
  | String s -> html_of_string s
  | ObjLoc loc -> html_of_objref loc
  | Closure (env, args, body) ->
	let args = "(" ^ String.concat ", " args ^ ")" in
  let code = FormatExt.to_string Ljs_pretty.exp body in
  let code_html = table [row [cell [style "code" (pre code)]]] in
  tag "div" [] [style "closure" (text "let"); html_of_env env;
                style "closure" (text ("in func" ^ args)); code_html]
      
let html_of_obj (attrs, props) =

  let html_of_attrs {proto=p; code=c; extensible=e; klass=k; primval=v} =
	  let html_of_attr attr value =
	    row [cell [style "attr" (text attr)]; cell value] in
	  let proto = [html_of_attr "proto" [html_of_value p]] in
	  let primval = match v with
	    | None -> []
	    | Some v -> [html_of_attr "prim" [html_of_value v]] in
	  let code = match c with
	    | None -> []
	    | Some v -> [html_of_attr "code" [html_of_value v]] in
	  let klass = [html_of_attr "class" [html_of_string k]] in
	  let extensible = [html_of_attr "extensible" [html_of_bool e]] in
	  List.concat [primval; proto; code; klass; extensible] in

  let html_of_props props =
	  let html_of_propv propv =
	    let prop_attr attr value =
		    row [cell [style "propattr" (text attr)]; cell value] in
	    match propv with
	    | Data ({value=v; writable=w}, enum, config) ->
		    table [prop_attr "value" [html_of_value v];
		           prop_attr "writable" [html_of_bool w];
		           prop_attr "enumerable" [html_of_bool enum];
		           prop_attr "configurable" [html_of_bool config]]
	    | Accessor ({getter=g; setter=s}, enum, config) ->
		    table [prop_attr "getter" [html_of_value g];
		           prop_attr "setter" [html_of_value s];
		           prop_attr "enumerable" [html_of_bool enum];
		           prop_attr "configurable" [html_of_bool config]] in
	  let html_of_prop (id, propv) =
	    row [cell [style "prop" (text id)]; cell [html_of_propv propv]] in
	  map html_of_prop (IdMap.bindings props) in
  
  table (html_of_attrs attrs @ html_of_props props)


let html_of_store (obj_store, var_store) =
  let html_of_obj_binding (loc, obj) =
    row [cell [html_of_objloc loc]; cell [html_of_obj obj]] in
  let html_of_var_binding (loc, value) =
    row [cell [html_of_varloc loc]; cell [html_of_value value]] in
  table (map html_of_obj_binding (LocMap.bindings obj_store)
         @ map html_of_var_binding (LocMap.bindings var_store))
  
