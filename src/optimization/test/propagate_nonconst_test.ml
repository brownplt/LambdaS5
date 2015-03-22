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
        func(x0) {
          let (y0 = 2)
            func(){prim('+',x,y)}();
          x0
        }");

    "propagate single-use object" >::
    (cmp "
       let (x={[]})
       let (y = 1)
         y := x
       "
       "
       let (y = 1)
         y := {[]}
       ");

    "propagate with side effect but only with single use" >::
    (no_change "
       let (x = {[]})
       let (y = 1) {
         y := x;
         y := x
       }");

    "do not propagate if side effect will happen before the use of id" >::
    (no_change "
       let (y = {[]})
       let (f = test(y)) {
         y := 15;
         f
       }");

    "propagate in function" >::
    (cmp "
       func(x, y) {
         label %ret: {
           let (z = y['0'])
             break %ret z
         }}"
       "func(x, y) {
         label %ret: {
             break %ret y['0']
         }}");
       
    "propagating function allows side effect" >::
    (cmp
       "
       let (y = 1)
       let (x = func(t) { y }) {
          y := 2;
          x(1)
       }"
       "
       let (y = 1) {
          y := 2;
          func(t){y}(1)
       }");

    "do not propagate into function if the value will be changed" >::
    (cmp
      "
      let (a = {[]})
      let (b = func(){a}) {
         a := 5;
         b}"
      "
      let (a = {[]}) {
         a := 5;
         func(){a}
      }");

    "propagating non-function does not allow side effect" >::
    (no_change
       "
       let (y = 1)
       let (x = func(t) { y }()) {
          y := 2;
          x(1)
       }");

    "stop propagating if the id is shadowed" >::
    (cmp
      "
      let (context = {[]})
      let (context = func(){1})
         f(context, context)"
      "
      let (context0 = func(){1})
         f(context0, context0)");

    "regression test" >::
    (cmp
       "
       let (py = %ToPrimitiveHint(r, 'number'))
       let (px = %ToPrimitiveHint(l, 'number'))
       rest(px, py)"
       "
       let (py = %ToPrimitiveHint(r, 'number'))
       rest(%ToPrimitiveHint(l, 'number'), py)"
    );

    "side effect takes place" >::
    (* rerun this can shrink more by propagating p *)
    (cmp
       "
       let (p = prim('print', 1))
       let (q = prim('print', 2))
         f(p, q)"
       "
       let (p = prim('print', 1))
         f(p, prim('print', 2))"
    );

  ]

let _ =
  run_test_tt_main suite

