open Js_syntax
open Format
open Prelude

let rec print_lit = function
  | Null -> print_string "null"
  | Bool (b) -> print_string (string_of_bool b)
  | Num (n) -> print_string (string_of_float n)
  | Str (s) -> print_string s

and print_propname = function
  | PropId (s) -> print_string s
  | PropStr (s) -> print_string s
  | PropNum (n) -> print_string (string_of_float n)

and print_mem = function
  | Field (pn, e) ->
    open_hovbox 1; print_string "("; 
    print_propname pn; print_expr e;
    print_string ")"; close_box ()
  | Get (pn, sel) -> failwith "getters not yet implemented"
  | Set (pn, arg, sel) -> failwith "setters not yet implemented"

and print_expr = function
  | This (p) -> print_string "this"
  | Id (p, id) -> print_string id
  | Lit (p, l) -> print_lit l
  | Array (p, el) -> 
    open_hovbox 1; print_string "(";
    List.iter (fun e -> print_expr e) el;
    print_string ")"; close_box ()
  | Object (p, ml) -> 
  

