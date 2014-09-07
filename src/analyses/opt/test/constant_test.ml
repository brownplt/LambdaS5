open Ljs_syntax
open Util
open Exp_val
open Prelude

let constants = [
  "const";
  "null";
  "undefined";
  "'string'";
  "1"; "1.3";
  "true"; "false";
  "{[#extensible: false]}";
  "{[#proto: null, #extensible: false]
    'field1': {#value 0, #writable false, #configurable false}}";

  "func(x, y) { prim('+', x, y) }";
  "func(x,y,z) {1}";

  "{[#proto: const, #extensible: false]
    'field1': {#value 0, #writable false, #configurable false}}";

  "{[#code: func(x) {x}, #extensible: false]
    'field1': {#value 0, #writable false, #configurable false}}";

  "{[#proto: null, #extensible: false]
    'field1': {#value const, #writable false, #configurable false}}";
]

(*"func(x, y) { prim('pretty', x, y) }";
  "func(x, y) { prim('print', x, y) }";*)

let non_constants = [
  (* not lambda constant *)
  "func(x) { prim('+', x, s) }";
  
  (* not object constant *)
  (* if some exp in object are not constant, this object is not a constant *)
  "{[#proto: null, #extensible: true]}";
  "{[#proto: {[#proto: null, #extensible: true]},
     #extensible: false]}";
  "{[#proto: {[#proto: unknown, #extensible: false]},
     #extensible: false]}";
  "{[#proto: null, #extensible: false]
    'field1': {#value 0, #writable true}}";
  "{[#proto: null, #extensible: false]
    'field1': {#value {[#proto: null, #extensible: true]}, #writable false}}";
  "{[#proto: null, #extensible: false]
    'field1': {#value unknown, #writable false}}";


  (* TODO: getter and setter *)
]

let _ =
  let check_const (s : string) =
    let e = parse s in
    let env = IdMap.empty in
    let env = IdMap.add "const" ((parse "1"), true, true) env in
    if is_constant e env then succeed ()
    else fail s; ()
  in
  let check_nonconst (s: string) =
    let e = parse s in
    if not (is_constant e IdMap.empty) then succeed ()
    else fail s; ()
  in
  List.iter check_const constants;
  List.iter check_nonconst non_constants;

