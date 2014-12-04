open Prelude
open Util
open OUnit2
open Exp_util

(* tips: do everything in function test instead of in cmp *)
let side_effect_test = 
  let checkse (code : string) (result : bool) = 
    let test test_ctxt = 
      assert_equal (has_side_effect (parse code)) result
    in 
    test
  in 
  "Test side effect" >:::
    [
      "lambda is closure. It has no side effect" >::
        (checkse "func(s) {prim('print',s)}" false);

      "lambda is closure. It has no side effect" >::
        (checkse "func(s) {prim('+',s, 1)}" false);

      "set field" >::
        (checkse "f['field'=12]" true);

      "get field" >::
        (checkse "f['field']" true);

      "get obj attr" >::
        (checkse "f[<#extensible>]" false);

      "set obj attr" >::
        (checkse "f[<#extensible>=true]" true);

      "get property attr" >::
        (checkse "f['field'<#writable>]" false);

      "set property attr" >::
        (checkse "f['field'<#writable>=true]" true);

      "test op2 1" >::
        (checkse "let (x=1)
                  let (y= prim('+', x:=3, 1)) {y}"
                 true);

      "test op2 2" >::
        (checkse "let (x=1)
                  let (y= prim('pretty', x)) {y}"
                 true);

      "test op2 3" >::
        (checkse "let (x=1)
                  let (y= prim('obj->bool', {[] 'fld': {#value x:=1, #writable false}}))
                  {y}"
                 true);
                                
      "test let binding an unused function" >::
        (checkse "let (f = func(s) {s:=1})
                  f" false);

      "test application" >::
        (checkse "let (f = func(s) {s:=1})
                  f(1)" true);

      "not every application has side effect" >::
        (checkse "func(s) {1}(1)" false);

      "this application has side effect 1" >::
        (checkse "func(s) {print('pretty', s)}(1)" true);

      "this application should be assumed to have side effect" >::
        (checkse "f(2)" true);

      "this application has side effect 2" >::
        (checkse "func(s){ func(t) {prim('pretty', t)}}(2)(2)" true);

      "this application will be assumed to have side effect" >::
        (checkse "let (t = func(s){func(t) {prim('+', 1, t)}})
                  t(2)(2)" true);

      "this application will be assumed to have side effect" >::
        (checkse "{1; func(s){func(t) {prim('+', 1, t)}}}(2)(2)"
                  true);

      "seq" >::
        (checkse "1; s:=1" true);

      "rec does not have side effect" >::
        (checkse "rec (f = func(x, y) {
                       if (x === 1) {y} else {f(prim('-', x, 1), prim('+', y, 1))}})
                    f(3, 0)"
                 false);

      "rec has side effect" >::
        (checkse "rec (f = func(x, y) {
                       if (x === 1) {prim('pretty',y); y} 
                       else {f(prim('-', x, 1), prim('+', y, 1))}})
                    f(3, 0)"
                 true);

      "rec has side effect" >::
        (checkse "rec (f = func(x, y) {
                       if (x === 1) {y} 
                       else {f({prim('pretty', x);prim('-', x, 1)}, prim('+', y, 1))}})
                    f(3, 0)"
                 true);

    ]

let _ =
  run_test_tt_main side_effect_test
    
