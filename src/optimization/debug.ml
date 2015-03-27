open Prelude
open Ljs_syntax
    
let print_ljs ljs =
  Ljs_pretty.exp ljs Format.std_formatter; print_newline()

let ljs_str ljs =
  Ljs_pretty.exp ljs Format.str_formatter; Format.flush_str_formatter()

(* this function will return printer for 
   print with normal args; print literal string and print ljs
*)
let make_debug_printer ?(on=false) name =
  if not on then 
    fun (s : string) -> ()
  else 
    fun (s : string) ->
      Printf.printf "[%s] %s%!" name s

