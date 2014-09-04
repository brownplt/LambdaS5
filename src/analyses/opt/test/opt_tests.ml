open Ljs
open Prelude

(* regression test for optimization *)

let _ = 
  let program = "{ let (x = '1') 
                    let (t = prim('string+', x, 'ok')) 
                      t; }" in
  let ljs = parse program in
  let new_ljs, m = substitute_const ljs in
  Ljs_pretty.exp new_ljs Format.std_formatter;; 
(*
  let path = "./t.s5" in
  let ljs = Ljs.parse_es5 (open_in path) path in
  let new_ljs = Ljs_const_propagation.const_propagation ljs in
  Ljs_pretty.exp new_ljs Format.std_formatter;; 
  let e = Let (p, "x", (Null p),
               Let (p, "x", Num (p, 1.0), Id (p, "x")))
  in
  Printf.printf "result: %B" (used_more_than_once "z" e);; *)

    
