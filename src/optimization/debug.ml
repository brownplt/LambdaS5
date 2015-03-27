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
  let print = 
    if not on then 
      fun fmt s -> ()
    else 
      fun fmt s ->
        Printf.printf "[%s] " name;
        Printf.printf fmt s;
        Printf.printf "%!"
  in 
  let print_string s = 
    print "%s" s
  in 
  let print_ljs ljs = 
    print "%s" (Exp_util.ljs_str ljs)
  in 
  (print, print_string, print_ljs)

        
let debug_exp_IdMap (m : exp IdMap.t) : unit =
  IdMap.iter (fun k v->printf "| %s  -> %s \n%!" k (Exp_util.ljs_str v)) m
