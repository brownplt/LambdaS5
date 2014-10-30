open Prelude
open Util
open OUnit2
open Ljs_alias_propagation

let suite = 
  let cmp before after = cmp before alias_propagation after in
  let no_change code = no_change code alias_propagation in
  "Test Alias Elimination" >:::
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

      "mutation 1" >::
        (no_change "let (b=a) {
                    b:=1;
                    b}");

      "mutation 2" >::
        (no_change "let (b=a) {
                    a:=1;
                    b}");
             
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

      "alias in lambda" >::
        (cmp "let (a=b)
              let (f=func(x){a}) f"
             "let (a=b)
              let (f=func(x){b}) f");

      "lambda argument shadow alias" >::
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

        
    ]

let _ =
  run_test_tt_main suite
