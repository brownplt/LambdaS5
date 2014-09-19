open Prelude
open Util
open OUnit2
open Ljs_prim_propagation

let suite = 
  let cmp before after = cmp before prim_propagation after in
  "Test Prim Propagation" >:::
    [
      "propagate number" >::
        (cmp "let (a = 1)
              let (b = a)
              b"
             "let (a = 1)
              let (b = 1)
              1");

      "propagate string" >::
        (cmp "let (a = 'a string')
              let (b = a)
              let (c = b)
              c"
             "let (a = 'a string')
              let (b = 'a string')
              let (c = 'a string')
              'a string'");

      "propagate null and bool" >::
        (cmp "let (a = null)
              let (w = false)
              let (b = {[#proto: a] 'fld': {#value w, #writable true}})
              b"
             "let (a = null)
              let (w = false)
              let (b = {[#proto: null] 'fld': {#value false, #writable true}})
              b");

      "mutation" >::
        (no_change "let (a = 1)
                    let (b = a) {
                    a := 12;
                    b
                    }");
      
      "deeply embeded mutation" >::
        (no_change "let (a = 1)
                    let (b = {[] 'fld': {#getter func(t) {a:=1}, #setter func(x){x:=a}}})
                    b");

      "let shadow" >::
        (cmp "let (x=1)
              let (y=x)
              let (x=2) {
              x := 3; x
              }"
             "let (x=1)
              let (y=1)
              let (x=2){
              x := 3; x
              }");

      "rec shadow" >::
        (cmp "let (x=1)
              let (y=x)
              rec (x = func(t) {t})
              x"
             "let (x=1)
              let (y=1)
              rec (x = func(t) {t})
              x");

      "lambda argument" >::
        (cmp "let (x=1)
              let (y=x)
              let (t = func(x,y) {prim('+',x,y)})
              t(x, y)"
             "let (x=1)
              let (y=1)
              let (t = func(x,y) {prim('+',x,y)})
              t(1,1)");

    ]

let _ =
  run_test_tt_main suite
