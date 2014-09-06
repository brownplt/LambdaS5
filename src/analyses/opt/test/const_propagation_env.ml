open Ljs
open Prelude
open Util
open Ljs_const_propagation

let _ =
  let env = Ljs.parse_es5_env (open_in "./es5.env") "./es5.env" in
  let ljs = env (parse "1") in
  let optimized = const_propagation ljs in
  Printf.printf "env node count:  %d\n" (count ljs);
  Printf.printf "optimized count: %d\n" (count optimized)
