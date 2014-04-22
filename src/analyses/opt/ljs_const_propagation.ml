open Ljs_const_folding
open Ljs_partial_eval

let rec const_propagation e =
  let new_e = const_folding e in 
  let new_e, modified = partial_eval new_e in
  if modified 
  then const_propagation new_e
  else new_e
