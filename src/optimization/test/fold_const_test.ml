open Prelude
open Util
open OUnit2
open Ljs_fold_const

let suite = 
  let cmp before after = cmp before fold_const after in
  let no_change code = no_change code fold_const in
  "Test Const Folding" >:::
    [
      (* ---------------------------- *)
      "op1" >::
        (cmp "prim('typeof', 1)"
             "'number'");

      "op1 given invalid argument" >::
        (no_change "prim('object-to-string', 1)");

      "op1 cannot be optimized" >::
        (no_change "prim('object-to-string', {[]})");

      "op1 has sideeffect" >::
        (no_change "prim('pretty', 1)");

      "if" >::
        (cmp "if (prim('+',1,2)) {1} else {2}" "2");
      "if" >::
        (cmp "if (func(s){s}) {1} else {2}" "2");
      "if" >::
        (cmp "if ({[]}) {1} else {2}" "2");
      "if" >::
        (cmp "if ('') {1} else {2}" "2");
      "if" >::
        (cmp "if (1) {1} else {2}" "2");
      "if" >::
        (cmp "if (0) {1} else {2}" "2");
      "if" >::
        (no_change "if (prim('pretty', 1)) {1} else {2}");
      "if" >::
        (no_change "let (x=1) prim('+', x, 1)");

      "rec" >::
        (no_change "let (r = 1)
                    rec (r = func(t) { r(prim('-',t,1))})
                    r(x)");
      "%EqEq" >::
      (cmp "%EqEq(1, 1)" "true");
      
      "%EqEq" >::
      (no_change "%EqEq(1, '1')");

      "%EqEq" >::
      (cmp "%EqEq('1', '1')" "true");

      "%EqEq" >::
      (cmp "%EqEq(undefined, null)" "true");
      
      "%EqEq" >::
      (no_change "%EqEq(undefined, 1)");

      "%PrimAdd" >::
      (cmp "%PrimAdd(1, 2)" "3");

      "%PrimAdd" >::
      (no_change "%PrimAdd(1, '1')");

      "%PrimSub" >::
      (cmp "%PrimSub(12, 1)" "11");
      
      "%PrimSub" >::
      (no_change "%PrimSub(12, '1')");
    ]

let _ =
  run_test_tt_main suite
