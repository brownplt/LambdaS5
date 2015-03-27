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

    "Let p I I' body: where(body has no mutation of I)" >::
    (cmp "let (a=1) let (b=a) b" "let (a=1) a");

      "[E/I] Let p I I' body" >::
        (cmp "let(b=1)
              let(a=b)
              let(a=c)
              a"
             "let(b=1)
              c
              ");
      
      "[E/I] Let p I' xv body" >::
      (cmp "let (b=1)
            let (a=b)
            let (c=a)
            c"
           "let (b=1)
            b");

      "mutation 1" >::
      (no_change "let (a=1)
                  let (b=a) {
                    b:=1;
                    b}");

      "mutation 2" >::
      (cmp "let (a=1)
            let (b=a) {
              a:=10;
              b}"
           "let (a=1)
            let (b=a) {
              a:=10;
              b}"
      );

      "mutation 3" >::
        (cmp
           "let (a=1)
            let (b=a) {
            a:=1;
            let (a=2)
            let (b=a)
            b}"
           "let(a=1)
            let (b=a) {
              a:=1;
              let (a=2)
                a}");

    "mutation 4" >::
    (*note: here rec is not renamed. An id is renamed only when that
      id is used in propagation. In this case, a and b neither are
      propagated, so rec(a=...) is not renamed *)
        (cmp
           "let(a=1)
            let (b=a) {
            a:=1;
            rec (a=func(){1})
            let (b=a)
            b}"
           "let (a=1)
            let (b=a) {
            a:=1;
            rec (a=func(){1})
            a}");

      "mutation 5 in rec body" >::
      (cmp
           "let(a=1)let (b=a) {
              a:=1;
              rec (a=func(){a:=2}) {
                a();
                let (b=a)
                  b
              }
            }"
            "let(a=1)let (b=a) {
              a:=1;
              rec (a=func(){a:=2}) {
                a();
                a
              }
            }"
      );

      "mutation 5 in rec body" >::
        (cmp
           "let(a=1)
            let (b=a) {
              rec (a=func(){let (x=a) x}) {
                a();
                let (b=a)
                  b
              };
              a:=1
            }"
           "let(a=1)
            let (b=a) {
              rec (a=func(){a}) {
                a();
                a
              };
              a:=1
            }");
             
      "mutate and then copy in lambda" >::
      (cmp
         "let (b=1)
          let (f=func(){b:=2})
          let (f1=func(b){let (x=b) x})
          let (a=b) {
            f();
            a}"
         "let (b=1)
          let (f1=func(b0){b0})
          let (a=b) {
            func(){b:=2}();
            a}");

      "mutate and then copy in lambda 2" >::
      (cmp
         "let (b=1)
          let (f=func(){b:=2})
          let (f1=func(b){let (x=b) {b:=3;x}})
          let (a=b) {
            f();
            a}"
         "let (b=1)
          let (f1=func(b0){let (x=b0) {b0:=3;x}})
          let (a=b) {
            func(){b:=2}();
            a}"
      );
                    
      "potential mutation 3" >::
      (cmp "let (a=1)
            let (b=a) 
            let (t = func(x) {b:=x}) {
              t}"
            
           "let (a=1)
            let (b=a)
            func(x) {b:=x}"
      );

      "bound" >::
      (cmp "let(a=1)
            let (b=a)
            let (b=func(t){b})
              b"
         "let (a=1)
          func(t){a}"
      );

      "shadow 1" >::
      (cmp "let (a=1)
            let (b=a)
            let (a=2)
              b"
         "let (a=1)
          let (a0=2)
            a"
      );

      "shadow 2" >::
        (cmp "let(a=1)
              let (b=a)
              let (t=b)
              let (a=1)
              t"
             "let(a=1)
              let (a0=1)
              a");

      "shadow 3" >::
        (cmp "let (y=1)
              let (b=2)
              let (a=y)
              let (c=b)
              let (d=b)
              let (b=1)
              {a;b;c;d}"
             "let (y=1)
              let (b=2)
              let (b0=1)
              {y;b0;b;b}");

      "shadow 4 by rec" >::
      (cmp "let(y=1)
            let (a=y)
            rec (a=func(){1})
              a"
         "let (y=1)
          rec (a0=func(){1})
            a0"
      );

      "copy in lambda" >::
        (cmp "let(b=1)
              let (a=b)
              let (f=func(x){a}) f"
             "let (b=1)
              func(x){b}");

      "lambda argument shadow copy" >::
        (cmp "let (b=1)
              let (a=b)
              func(a){a:=1}(a)"
             "let (b=1)
              func(a0){a0:=1}(b)");

      "lambda shadow binding" >::
      (cmp "let(b=1)
            let (a=b)
             func(a){a}"
           "let(b=1)
             func(a0){a0}"
      );

      "lambda 2" >::
        (cmp "let (a=1)
              let (c=a)
              func(a){c}(c)"
             "let (a=1)
              func(a0){a}(a)");

      "lambda 3" >::
        (cmp "let (a=1)
              let(b=a)
              let(c=func(x){let (a=x) a:=b})
              c"
             "let (a=1)
              func(x){let (a0=x) a0:=a}
              ");

      "rec" >::
      (cmp "let (a=1)
            let (r = a)
            rec (r = func(t) { r(prim('-',t,1))})
              r(x)"
           "let (a=1)
            rec (r0 = func(t) { r0(prim('-',t,1))})
              r0(x)"
      );
        
      "self copy" >::
      (cmp
         "let (x=1)
          let (a=x)
          let (b=a)
          let (b=b)
            b"
         "let (x=1)
            x");

      "self copy 2" >::
      (cmp
         "let (a=1)
          let (b=a)
          let (b=b)
            b"
         "let (a=1)
            a");

      "assignment" >::
      (cmp
         "let (b=1)
          let (f=func(){b:=2})
          let (a=b) {
            f();
            a
          }"
         "let (b=1) 
          let (a=b) {
            (func(){b:=2})();
            a
          }"         
      );

]
let _ =
  run_test_tt_main suite

