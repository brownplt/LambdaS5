open Ljs_const_folding
open Ljs_substitute_eval

(* Optimization phase
 * 
 * This optimization phase combines constant folding and substitute 
 * evaluation.
 *)
let rec const_propagation e =
  let new_e = const_folding e in 
  let new_e, modified = substitute_const new_e in
  if modified 
  then const_propagation new_e
  else new_e
