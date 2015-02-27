open Prelude
open Util
open OUnit2
open Ljs_propagate_copy

let suite = 
  let cmp before after = cmp before propagate_copy after in
  let no_change code = no_change code propagate_copy in
  "Test Copy Elimination" >:::
    [
      "simple" >::
        (cmp "let (b=a) b" "let (b=a) a");

      "simple2" >::
        (cmp "let(a=b)
              let(a=c)
              a"
             "let(a=b)
              let(a=c)
              c");
      
      "simple3" >::
      (cmp "let (a=b)
            let (c=a)
            c"
           "let (a=b)
            let (c=b)
            b");

      "mutation 1" >::
        (no_change "let (b=a) {
                    b:=1;
                    b}");

      "mutation 2" >::
        (no_change "let (b=a) {
                    a:=1;
                    b}");

      "mutation 3" >::
        (cmp
           "let (b=a) {
            a:=1;
            let (a=2)
            let (b=a)
            b}"
           "let (b=a) {
            a:=1;
            let (a=2)
            let (b=a)
            a}");

      "mutation 4" >::
        (cmp
           "let(a=1)let (b=a) {
            a:=1;
            rec (a=func(){1})
            let (b=a)
            b}"
           "let (a=1)let (b=a) {
            a:=1;
            rec (a=func(){1})
            let (b=a)
            a}");

      "mutation 5 in rec body" >::
        (no_change
           "let(a=1)let (b=a) {
              a:=1;
              rec (a=func(){a:=2}) {
                a();
                let (b=a)
                  b
              }
            }");

      "mutation 5 in rec body" >::
        (cmp
           "let(a=1)let (b=a) {
              a:=1;
              rec (a=func(){let (x=a) x}) {
                a();
                let (b=a)
                  b
              }
            }"
           "let(a=1)let (b=a) {
              a:=1;
              rec (a=func(){let (x=a) a}) {
                a();
                let (b=a)
                  a
              }
            }");
             
      "mutation and then copy in lambda" >::
      (cmp
         "let (b=1)
          let (f=func(){b:=2})
          let (f1=func(b){let (x=b) x})
          let (a=b) {
            f();
            a}"
         "let (b=1)
          let (f=func(){b:=2})
          let (f1=func(b){let (x=b) b})
          let (a=b) {
            f();
            a}");

      "mutation and then copy in lambda 2" >::
      (no_change
         "let (b=1)
          let (f=func(){b:=2})
          let (f1=func(b){let (x=b) {b:=3;x}})
          let (a=b) {
            f();
            a}");
                    
      "potential mutation 3" >::
        (no_change "let (b=a) 
                    let (t = func(x) {b:=x})
                    b");

      "bound" >::
        (no_change "let (b=a)
                    let (b=func(t){1})
                    b");

      "shadow 1" >::
        (no_change "let (b=a)
                    let (a=2)
                    b");

      "shadow 2" >::
        (cmp "let (b=a)
              let (t=b)
              let (a=1)
              t"
             "let (b=a)
              let (t=a)
              let (a=1)
              t");

      "shadow 3" >::
        (cmp "let (a=y)
              let (c=b)
              let (d=b)
              let (b=1)
              {a;b;c;d}"
             "let (a=y)
              let (c=b)
              let (d=b)
              let (b=1)
              {y;b;c;d}");

      "shadow 4 by rec" >::
        (no_change "let (a=y)
                    rec (a=func(){1})
                    a");

      "copy in lambda" >::
        (cmp "let (a=b)
              let (f=func(x){a}) f"
             "let (a=b)
              let (f=func(x){b}) f");

      "lambda argument shadow copy" >::
        (cmp "let (a=b)
              func(a){a:=1}(a)"
             "let (a=b)
              func(a){a:=1}(b)");

      "lambda shadow binding" >::
        (no_change "let (a=b)
                    func(a){a}");

      "lambda 2" >::
        (cmp "let (c=a)
              func(a){c}(c)"
             "let (c=a)
              func(a){c}(a)");

      "lambda 3" >::
        (cmp "let(b=a)
              let(c=func(x){let (a=x) a:=1})
              b"
             "let(b=a)
              let(c=func(x){let (a=x) a:=1})
              a");

      "rec" >::
        (no_change "let (a=1)
                    let (r = a)
                    rec (r = func(t) { r(prim('-',t,1))})
                    r(x)");
        
      "self copy" >::
      (cmp
         "let (a=x)
          let (b=a)
          let (b=b)
            b"
         "let (a=x)
          let (b=x)
          let (b=x)
            x");

      "self copy 2" >::
      (cmp
         "let (a=1)
          let (b=a)
          let (b=b)
            b"
         "let (a=1)
          let (b=a)
          let (b=a)
            a");

      "assignment" >::
      (no_change
         "let (b=1)
          let (f=func(){b:=2})
          let (a=b) {
            f();
            a
          }");

    ]

let _ =
  run_test_tt_main suite
