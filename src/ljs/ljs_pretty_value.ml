open Prelude
open Ljs_values
open Ljs_pretty

open Format
open FormatExt

let pretty_loc loc = text ("#" ^ Store.print_loc loc)

let pretty_env env =
  let pretty_bind (var, loc) = horz [text var; text "="; pretty_loc loc] in
  braces (vert (map pretty_bind (IdMap.bindings env)))

let pretty_value value = match value with 
  | ObjLoc loc -> pretty_loc loc
  | Closure (env, args, body) ->
    vert [text "let";
          pretty_env env;
          horz [text "in func";
                parens (squish (intersperse (text ",") (map text args)))];
          braces (exp body)]
  | primitive -> text (Ljs_values.pretty_value primitive)

let rec pretty_value_store v store = match v with
  | ObjLoc loc -> pretty_obj store (get_obj store loc)
  | _ -> pretty_value v

and pretty_obj store (avs, props) = 
    let proplist = IdMap.fold (fun k v l -> (k, v)::l) props [] in
      match proplist with
        | [] -> braces (pretty_attrsv avs store)
        | _ ->
          braces (vert [pretty_attrsv avs store;
                        vert (vert_intersperse (text ",")
                              (map (fun p -> pretty_prop p store) proplist))])

and pretty_attrsv ({ proto = p; code = c; extensible = b; klass = k; primval = pv } : attrsv) store =
  let proto = [horz [text "#proto:"; pretty_value p]] in
  let primval = match pv with None -> []
    | Some v -> [horz [text "#prim:"; pretty_value v]] in
  let code = match c with None -> [] 
    | Some v -> [horz [text "#code:"; pretty_value v]] in
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
                                    pretty_value v;
                                    text ","]; 
                              horz [text "#writable"; text (string_of_bool w); text ","];
                              horz [text "#configurable"; text (string_of_bool config)]])]
  | Accessor ({getter=g; setter=s}, enum, config) ->
    horz [text ("'" ^ f ^ "'"); text ":"; braces (vert [horz [text "#getter";
                                          pretty_value g; text ","];
                                          horz[text "#setter";
                                               pretty_value s]])]

let string_of_value v store =
  (FormatExt.to_string (fun v -> pretty_value_store v store) v)

let strings_of_store store = match store with
  | (obj_store, value_store) ->
    let pretty_bind printer (loc, value) =
      (loc, horzOrVert [horz [pretty_loc loc; text "="]; printer value]) in
    let bindings =
        (map (pretty_bind (pretty_obj store)) (Store.bindings obj_store))
      @ (map (pretty_bind pretty_value) (Store.bindings value_store)) in
    let cmp_bindings (x, _) (y, _) = compare x y in
    let binding_printers = map snd (List.sort cmp_bindings bindings) in
    map (fun fmt -> FormatExt.to_string (fun _ -> fmt) ()) binding_printers


(* Stores can be very large. This function avoids mapping over them,
   which tends to overflow the stack. *)
let print_store store = match store with
  | (obj_store, value_store) ->
    let pretty_bind printer (loc, value) =
      horzOrVert [horz [pretty_loc loc; text "="]; printer value] in
    let print_binding printer binding =
      print_endline (FormatExt.to_string (pretty_bind printer) binding) in
    List.iter (print_binding (pretty_obj store)) (Store.bindings obj_store);
    List.iter (print_binding pretty_value) (Store.bindings value_store)
