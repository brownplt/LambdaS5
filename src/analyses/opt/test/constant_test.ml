open Ljs_syntax
open Util
open Exp_val

let constants = [
  "null";
  "undefined";
  "'string'";
  "1"; "1.3";
  "true"; "false";
  "{[#proto: null, #extensible: false]
    'field1': {#value 0, #writable false}}";
  "func(x, y) { prim('+', x, y) }";
]

let non_constants = [
  (* not lambda constant *)
  "func(x, y) { prim('pretty', x, y) }";
  "func(x, y) { prim('print', x, y) }";
  "func(x) { prim('+', x, s) }";
  

  (* not object constant *)
  (* if some exp in object are not constant, this object is not a constant *)
  "{[#proto: null, #extensible: true]}";
  "{[#proto: {[#proto: null, #extensible: true]},
     #extensible: false]}";
  "{[#proto: null, #extensible: false]
    'field1': {#value 0, #writable true}}";
  "{[#proto: null, #extensible: false]
    'field1': {#value {[#proto: null, #extensible: true]}, #writable false}}";
  (* TODO: getter and setter *)
]

let _ =
  let is_const(e : exp) : bool =
    is_scalar_constant e || is_object_constant e || is_lambda_constant e
  in
  let check_const (s : string) =
    let e = parse s in
    if is_const e then succeed
    else fail s
  in
  let check_nonconst (s: string) =
    let e = parse s in
    if not (is_const e) then succeed
    else fail s
  in
  List.map check_const constants;
  List.map check_nonconst non_constants

  
  
