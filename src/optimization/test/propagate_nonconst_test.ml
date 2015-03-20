open Prelude
open Util
open OUnit2
open Ljs_propagate_nonconst


let suite =
  let cmp before after = cmp before propagate_nonconst after in
  let no_change code = no_change code propagate_nonconst in
  "Test propagating nonconst" >:::
  [
    "normal propagation" >::
    (cmp
       "let (x=1)
        let (f = func() {x})
        let (g = func() {f()})
        let (t=2)
          g()"
       "let (x=1)
        let (f = func() {x})
        let (g = func() {(func(){x})()})
        let (t=2)
          func(){(func(){x})()}()");


    "propagate and rename" >::
    (cmp
       "let (x=1)
      let (f = func() {x})
      let (g = func() {f()})
      let (x=2)
        g()"
       "let (x=1)
      let (f = func() {x})
      let (g = func() {(func(){x})()})
      let (x0=2)
        func() {(func(){x})()}()");

    "t's free variable is at the formal args: renaming func" >::
    (cmp
       "let (x = 1)
        let (y = 2)
        let (t = func(){prim('+',x,y)})
        func(x) {
           x := t
        }"
       "let (x = 1)
        let (y = 2)
        let (t = func(){prim('+',x,y)})
        func(x0) {
           x0 := func(){prim('+',x,y)}
        }");

    "let bind shadows the formal argument again" >::
    (cmp
       "let (x = 1)
        let (y = 2)
        let (t = func(){prim('+',x,y)})
        func(x) {
           let (x = 2)
              t();
           x
        }"
       "let (x = 1)
        let (y = 2)
        let (t = func(){prim('+',x,y)})
        func(x0) {
          let (x1 = 2)
            func(){prim('+',x,y)}();
          x0
        }");

    "let binding shadows the formal argument again 2" >::
    (cmp
       "let (x = 1)
        let (y = 2)
        let (t = func(){prim('+',x,y)})
        func(x) {
           let (y = 2)
              t();
           x
        }"
       "let (x = 1)
        let (y = 2)
        let (t = func(){prim('+',x,y)})
        func(x0) {
          let (y0 = 2)
            func(){prim('+',x,y)}();
          x0
        }");
  ]

let _ =
  run_test_tt_main suite

