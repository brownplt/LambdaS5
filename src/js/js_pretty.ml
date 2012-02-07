open Js_syntax
open Format
open Prelude

let rec print_lit = function
  | Null -> print_string "null"
  | Bool (b) -> print_string (string_of_bool b)
  | Num (n) -> print_string (string_of_float n)
  | Str (s) -> print_string s
  | Regexp _ -> failwith "Can't print Regexps yet"

and print_propname = function
  | PropId (s) -> print_string s
  | PropStr (s) -> print_string s
  | PropNum (n) -> print_string (string_of_float n)

and print_mem = function
  | Field (pn, e) ->
    open_hovbox 1; print_string "(Field"; 
    print_propname pn; print_expr e;
    print_string ")"; close_box ()
  | Get (pn, sel) -> failwith "getters not yet implemented"
  | Set (pn, arg, sel) -> failwith "setters not yet implemented"

and print_se = function
  | _ -> failwith "what"

and print_expr = function
  | This (p) -> print_string "this"
  | Id (p, id) -> print_string id
  | Lit (p, l) -> print_lit l
  | Array (p, el) -> 
    open_hovbox 1; print_string "(Array";
    List.iter (fun e -> print_expr e) el;
    print_string ")"; close_box ()
  | Object (p, ml) ->
    open_hovbox 1; print_string "(Object";
    List.iter (fun m -> print_mem m) ml;
    print_string ")"; close_box ()
  | Paren (p, el) ->
    open_hovbox 1; print_string "(Paren";
    List.iter (fun e -> print_expr e) el;
    print_string ")"; close_box ()
  | Func (p, nm, args, sel) ->
    let ns = match nm with
      | None -> "_"
      | Some s -> s in
    open_hovbox 1; print_string "(Func";
    print_string ns; ; List.iter (fun se -> print_se se) sel;
    print_string ")"; close_box ()
  | Bracket (p, e1, e2) ->
    open_hovbox 1; print_string "(Bracket";
    print_expr e1; print_expr e2; print_string ")"; close_box ()
  | Dot (p, e, id) ->
    open_hovbox 1; print_string "(Dot"; print_expr e; print_string id;
    print_string ")"; close_box ()
  | New (p, e, el) -> failwith "not implemented yet"
  | _ -> failwith "not implemented yet"



     

