open Prelude
open Util
open OUnit2
open Ljs_deadcode_elimination
module S = Ljs_syntax

 
let unused_id_test =
  let cmp before after = cmp before deadcode_elimination after in
  let no_change code = no_change code deadcode_elimination in
  "Test Unused Id Elimination" >:::
    ["unused at all" >:: 
       (cmp "let (x=1)
             let (y=x)
             let (z=y)
             x"
            "let (x=1) x");

     "chained id" >:: 
       (cmp "let (x=1)
             let (y=x)
             let (z=x)
             z"
            "let (x=1)
             let (z=x)
             z");

     "test setbang" >::
       (no_change "let (x=1)
                   x := 2");

     "let contains other lets" >::
       (cmp "let (x=1)
             let (y={let (z = x)
             x})
             let (z=y)
             y"
            "let (x=1)
             let (y=x)
             y");

     "let contains other lets with side-effect" >::
       (cmp "let (x=1)
             let (y={let(z=10) x:=z})
             let (x=3)
             y"
            "let (x=1)
             let (y={let(z=10) x:=z})
             y");

     (* binding shadows *)
     "let shadow" >::
       (cmp "let (x=1)
             let (y=x)
             let (x=2)
             y"
            "let (x=1)
             let (y=x)
             y");

     "let shadow2" >::
       (cmp "let (x=1)
             let (x=2)
             let (x=3)
             x"
            "let (x=3)
             x");

     "lambda arguments shadow previous binding" >::
       (cmp "let (x=1)
             let (y=func(x){prim('+', x, 1)})
             y(2)"
            "let (y=func(x){prim('+',x,1)})
             y(2)");
     "test lambda" >::
       (cmp "let (x=1)
             let (y=2)
             let (z=3)
             let (t=4)
             z := func(x,y) {f(x);f(y);f(t)}"
            "let (z=3)
             let (t=4)
             z := func(x,y) {f(x);f(y);f(t)}");

     "test lambda 2" >::
       (cmp "let (x=1)
             let (y=2)
             let (z=3)
             let (t=4) {
             f(x); 
             z := func(x,y) {f(x);f(y);f(t)}
             }"
            "let (x=1)
             let (z=3)
             let (t=4) {
             f(x);
             z := func(x,y) {f(x);f(y);f(t)}
             }");

     "let lambda 3" >::
       (no_change "let (mm = undefined)
                   let (fp = {[]})
                   let (ftostr = {[#proto:fp, #code: null]})
                   {
                   let (newval = ftostr) fp['toString' = newval];
                   fp['toString'<#enumerable>=false];
                   {mm := func() {2};
                   1}}");


     "id collection should also be performed in lambda body 1" >::
       (cmp "let (x = 1)
             let (y = func(s) {
             x := s
             })
             y"
            "let (x = 1)
             let (y = func(s) {
             x := s
             })
             y");

     "id collection should also be performed in lambda body 2" >::
       (cmp "let (x = 1)
             let (y = func(s) {
             let (x = 1)
             x := s
             })
             y"
            "let (y = func(s) {
             let (x = 1)
             x := s
             })
             y");
     
     (* side effect *)
     "side effect test 0" >::
       (no_change "let (x = 1)
                   let (y = prim('pretty', x))
                   x");

     "side effect test 1" >::
       (no_change "let (x = 1)
                   let (y = {[] 
                   'fld': {#value prim('print', x), #writable true}})
                   x");

     "side effect test 2" >::
       (cmp  "let (x = 1)
              let (y = {[#proto:null] 'fld': {#value prim('+', x, 1), #writable true}})
              x"
             "let (x = 1)
              x");

     "side effect test 3" >::
       (cmp "let (x = 1)
             let (y = {[]})
             x"
            "let (x = 1)
             x");

     "side effect test 4" >::
       (cmp "let (x = 1)
             let (y = func(t) { prim('print', x) })
             x"
            "let (x = 1)
             x");

     "side effect test 5" >::
       (no_change "let (y = o['field1'])
                   x");


     "eliminate sequence" >::
       (cmp "let (x = 1)
             {x;x;x;x;x}"
            "let (x=1)
             x");

     "test sequence" >::
       (cmp "f['field' = true]; f['field'<#enumerable>=false]"
            "f['field' = true]; f['field'<#enumerable>=false]");

     "test object field" >::
       (no_change "let (%ObjectProto = {[#proto: null]})
                   let (%global = {[#proto: %ObjectProto]})
                   %global")
    ]

let _ =
  run_test_tt_main unused_id_test
                   