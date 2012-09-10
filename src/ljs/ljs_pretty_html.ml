open Format
open Prelude
open Ljs_values
open Html
open Reachability

let print_loc = Store.print_loc

let style_backrefs = style "backrefs"
let style_label = style "label"
(* value styles *)
let style_constant = style "constant"
let style_string = style "string"
let style_number = style "number"
let style_closure = style "closure"
let style_code = style "code"
(* object styles *)
let style_attr = style "attr"
let style_prop = style "prop"
let style_prop_attr = style "propattr"
(* store styles *)
let style_objloc = style "objloc"
let style_varloc = style "varloc"
let style_objref = style "objref"
let style_varref = style "varref"
(* environment styles *)
let style_id = style "id"


let label str = style_label (text str)
let html_of_null = style_constant (text "null")
let html_of_undefined = style_constant (text "undefined")
let html_of_bool bool = style_constant (text (string_of_bool bool))
let html_of_string string = style_string (text string)
let html_of_float float = style_number (text (string_of_float float))

let html_of_objloc loc =
  anchor ("obj" ^ print_loc loc) [style_objloc (text (print_loc loc))]
let html_of_varloc loc =
  anchor ("var" ^ print_loc loc) [style_varloc (text (print_loc loc))]
let html_of_objref loc =
  anchor_link ("obj" ^ print_loc loc) [style_objref (text ("obj" ^ print_loc loc))]
let html_of_varref loc =
  anchor_link ("var" ^ print_loc loc) [style_varref (text ("var" ^ print_loc loc))]
let html_of_id id = style_id (text id)


let html_of_env env =
  let html_of_binding (id, var) = row [cell [html_of_id id];
									                     cell [html_of_varref var]] in
  table (map html_of_binding (IdMap.bindings env))

let html_of_value value =
  let html_of_closure env args body =
	  let args = "(" ^ String.concat ", " args ^ ")" in
    let code = FormatExt.to_string Ljs_pretty.exp body in
    let code_html = tag "textarea" [("rows", "5"); ("cols", "80")] [text code] in
    tag "div" [] [style_closure (text "let");
                  html_of_env env;
                  style_closure (text ("in func" ^ args));
                  tag "br" [] [];
                  code_html] in
  match value with
  | Null -> html_of_null
  | Undefined -> html_of_undefined
  | True -> html_of_bool true
  | False -> html_of_bool false
  | Num n -> html_of_float n
  | String s -> html_of_string s
  | ObjLoc loc -> html_of_objref loc
  | Closure (env, args, body) -> html_of_closure env args body

let html_of_obj obj styles =

  let html_of_attrs {proto=p; code=c; extensible=e; klass=k; primval=v} =
	  let html_of_attr attr value =
	    row [cell [style_attr (text attr)]; cell value] in
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
		    [cell [style_prop_attr (text attr)]; cell value] in
      let mask w e c =
        let mask_char char bool =
          if bool then char else "-" in
        let str = mask_char "w" w ^ mask_char "e" e ^ mask_char "c" c in
        style "mask" (text str) in
	    match propv with
	    | Data ({value=v; writable=w}, enum, config) ->
        table [row (cell [mask w enum config]
                    :: prop_attr "value" [html_of_value v])]
	    | Accessor ({getter=g; setter=s}, enum, config) ->
        table [row (cell [mask false enum config]
                    :: prop_attr "getter" [html_of_value g]
                    @ prop_attr "setter" [html_of_value s])] in
	  let html_of_prop (id, propv) =
	    row [cell [style_prop (text id)]; cell [html_of_propv propv]] in
	  map html_of_prop (IdMap.bindings props) in

  match obj with
  | (attrs, props) ->
    style styles (table (html_of_attrs attrs @ html_of_props props))


let html_of_paths paths =
  let html_of_attr_type attr_type =
    style_attr (text (string_of_attr_type attr_type)) in
  let html_of_prop_attr_type attr_type =
    style_prop_attr (text (string_of_prop_attr_type attr_type)) in
  let html_of_node node = match node with
    | IdNode id -> html_of_id id
    | VarNode (loc, value) -> html_of_varref loc
    | ObjNode (loc, obj) -> html_of_objref loc
    | PropNode id -> style_prop (text id)
    | AttrNode t -> html_of_attr_type t
    | PropAttrNode t -> html_of_prop_attr_type t
    | ClosureNode (env, args, exp) ->
      style_closure (text ("func(" ^ String.concat ", " args ^ "){...}")) in
  let html_of_path path =
    table (List.map (fun node -> row [cell [html_of_node node]]) path) in
  let html_row_of_path path = row [cell [html_of_path path]] in
  let first_row = row [cell [style_label (text "BackRefs")]] in
  style_backrefs (div [table (first_row :: List.map html_row_of_path paths)])


let html_of_answer answer filter =
  match answer with
  | Ljs_eval.Answer (_, _, envs, store) ->
    let store = (Store.to_map (fst store), Store.to_map (snd store)) in
    let env = (* Is (last envs) correct? *)
      IdMap.filter (fun id _ -> List.mem id Env_free_vars.ids) (last envs) in
    let reachability =
      make_reachability_graph store env filter in
    let store = match store with
      | (obj_store, var_store) ->
      (LocMap.filter (fun loc _ -> LocMap.mem loc (fst reachability)) obj_store,
       LocMap.filter (fun loc _ -> LocMap.mem loc (snd reachability)) var_store) in
    let html_of_store (obj_store, var_store) =
      let html_of_obj_refs loc = html_of_paths (LocMap.find loc (fst reachability)) in
      let html_of_var_refs loc = html_of_paths (LocMap.find loc (snd reachability)) in
      let html_of_obj_binding (loc, obj) =
        let obj_style =
          let primordial = LocSet.mem loc filter.primordials in
          let frozen = Heapwalk.is_frozen obj in
          if primordial && frozen then "frozen_primordial"
          else if primordial then "unfrozen_primordial"
          else if frozen then "frozen"
          else "unfrozen" in
        row [cell [html_of_objloc loc];
             cell [html_of_obj_refs loc];
             cell [div [label ("Contents (" ^ obj_style ^ ")");
                        html_of_obj obj obj_style]]] in
      let html_of_var_binding (loc, value) =
        row [cell [html_of_varloc loc];
             cell [html_of_var_refs loc];
             cell [html_of_value value]] in
      (table (map html_of_obj_binding (LocMap.bindings obj_store)),
       table (map html_of_var_binding (LocMap.bindings var_store))) in
    let html_key = defns [("Green", text "frozen primordial");
                          ("Red", text "unfrozen primordial");
                          ("Blue", text "frozen");
                          ("Gray", text "unfrozen")] in
    match html_of_store store with
    | (obj_table, var_table) ->
      div [header 1 "Javascript heap"; html_key;
           header 2 "Environment"; html_of_env env;
           header 2 "Objects"; obj_table;
           header 2 "Variables"; var_table]
