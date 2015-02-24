open Prelude
open Util
open OUnit2
open Ljs_propagate_const

let suite = 
  let cmp before after = cmp before propagate_const after in
  let no_change code = no_change code propagate_const in
  "Test Const Propagation" >:::
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

      "do not propagate object(because such an object does not exist in desugared code)" >::
      (no_change
         "let (a = {[#extensible: false]})
          let (b = a)
          b");

      "propagate function" >::
        (cmp "let (a = func(x) {prim('typeof',1)})
              {[#code: a]}"
             "let (a = func(x) {prim('typeof',1)})
              {[#code: func(x) {prim('typeof',1)}]}");

      "propagate function that has side effect" >::
        (cmp "let (a = func(x) {prim('pretty',1)})
              {[#code: a]}"
             "let (a = func(x) {prim('pretty',1)})
              {[#code: func(x) {prim('pretty',1)}]}");

      "don't propagate function(used a too many times)" >::
        (cmp "let (a = func(x) {prim('typeof',1)})
              {[#code: a, #proto: a]}"
             "let (a = func(x) {prim('typeof',1)})
              {[#code: a, #proto: a]}");
      
      "mutation" >::
        (no_change "let (a = 1)
                    let (b = a) {
                    a := 12;
                    b
                    }");

      "const functions" >::
      (cmp "let (f = func(x) { x := 1 })
              let (a = 2) {
                f(a);
                a
              }"
         "let (f = func(x) { x := 1 })
            let (a = 2) {
              func(x){x:=1}(2);
              2
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

      "let shadow 2. the function is used twice" >::
        (no_change "let (t = func(){1})
                    let (a = t)
                    let (b = t)
                    let (t = 1)
                    a;b");

      "rec shadow" >::
        (cmp "let (x=1)
              let (y=x)
              rec (x = func(t) {t})
              x"
             "let (x=1)
              let (y=1)
              rec (x = func(t) {t})
              func(t){t}");

      "lambda argument shadow" >::
        (cmp "let (x=1)
              let (y=x)
              let (t = func(x,y) {prim('+',x,y)})
              t(x, y)"
             "let (x=1)
              let (y=1)
              let (t = func(x,y) {prim('+',x,y)})
              func(x,y){prim('+',x,y)}(1,1)");

      "lambda argument" >::
        (cmp "let (x=1)
              let (y=x)
              let (t = func(x) {prim('+',x,2)})
              t(y)"
             "let (x=1)
              let (y=1)
              let (t = func(x) {prim('+',x,2)})
              func(x){prim('+',x,2)}(1)");

      "rec" >::
        (no_change
           "let (r = 1)
              rec (r = func(t) { r(prim('-',t,1))})
                  r(x)");

    ]

let _ =
  run_test_tt_main suite
