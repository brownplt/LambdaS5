open Prelude
open Util
open OUnit2
open Ljs_const_propagation

let suite = 
  let cmp before after = cmp before const_propagation after in
  let no_change code = no_change code const_propagation in
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

      "propagate object" >::
        (cmp "let (a = {[#extensible: false]})
              let (b = a)
              b"
             "let (a = {[#extensible: false]})
              let (b = {[#extensible: false]})
              {[#extensible: false]}");

      "don't propagate object" >::
        (cmp "let (a = {[#extensible: false]})
              let (b = a)
              let (c = a)
              c"
             "let (a = {[#extensible: false]})
              let (b = a)
              let (c = a)
              c");

      "propagate function" >::
        (cmp "let (a = func(x) {prim('typeof',1)})
              {[#code: a]}"
             "let (a = func(x) {prim('typeof',1)})
              {[#code: func(x) {prim('typeof',1)}]}");

      "propagate function" >::
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

      "let shadow 2" >::
        (no_change "let (t = {[#extensible: false]})
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

      "lambda argument" >::
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
              let (t = func(x) {prim('+',x,y)})
              t(y)"
             "let (x=1)
              let (y=1)
              let (t = func(x) {prim('+',x,1)})
              func(x){prim('+',x,1)}(1)");

      "rec" >::
        (no_change
           "let (r = 1)
              rec (r = func(t) { r(prim('-',t,1))})
                  r(x)");

    ]

let _ =
  run_test_tt_main suite
