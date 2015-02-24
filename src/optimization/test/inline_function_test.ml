open Prelude
open Util
open OUnit2
open Ljs_inline_function

let suite = 
  let cmp before after = cmp before inline_function after in
  let no_change code = no_change code inline_function in 
  "Test Function Inlining Test" >:::
    [
      "inlining for prim arg" >::
        (cmp "func(x){prim('+', x, 1)}(2)"
             "prim('+', 2, 1)");

      "const functions that cannot be inlined" >::
      (no_change
         "let (a = 2) {
          func(x) { x := 1 }(a);
          a
          }");

      "function without def to formal parameter: is inlinable" >::
      (fun _ ->
         (assert_equal true
            (is_inlinable_lambda
               (parse
                  "func(x, y, z) {
                   let (t = 1) t:=2}
              "))));
      
      "inlinable: function without def to formal parameters" >::
      (fun _ ->
         (assert_equal true
            (is_inlinable_lambda
               (parse
                  "func(x, y, z) {
                   let (x = 1) x:=2
               }"))));

      "inlinable: function without def to formal parameters" >::
      (fun _ ->
      (assert_equal true
         (is_inlinable_lambda
            (parse
              "func(x, y, z){
                let (f = func(x,y){x:=1;y:=1})
                   f(1, z)
              }"))));

      "not inlinable: function has def to formal parameters">::
      (fun _ ->
      (assert_equal false
         (is_inlinable_lambda
            (parse
              "func(x, y, z) {
                let (f = func(x){x:=1; y:=2})
                  f(z)}"))));

      "not inlinable: function has def to formal parameters">::
      (fun _ ->
      (assert_equal false
         (is_inlinable_lambda
            (parse
              "func(x, y, z) {
               let (x = 1) y := 2
              }"))));
      
      "not inlinable:">::
      (fun _ ->
      (assert_equal false
        (is_inlinable_lambda
           (parse
             "func(x, y) {
                let (x = func(){x:=1})
                  x}"))));
      
      "inlinable[compared with the previous test]" >::
      (fun _ ->
      (assert_equal true
        (is_inlinable_lambda
           (parse
             "func(x, y) {
                rec (x = func(){x:=1})
                   x}"))));

      "inlining for lambda" >::
        (cmp "func(x){prim('+', x, 1)}(2)"
             "prim('+', 2, 1)");

      "Only inline function that has been propagated" >::
        (no_change "let (a = func(t){1})
                    a(2)");

      "Only inline function that has been propagated" >::
      (cmp "func(t){1}(2)" "1");

      "argument is constant variable" >::
        (cmp "let (a = func(t){t})
              func(x){x;x}(a)"
             "let (a = func(t){t})
              {a;a}");

      "argument can be any variabe" >::
        (cmp "let (b={[]})
              func(x){prim('+', x, 1)}(b)"
             "let (b={[]})
              prim('+', b, 1)");

      (* tests below: side effect occurs in lambda, argument is constant  *)
      "lambda has side effect app()" >::
        (cmp "func(t){t()}(a)"
             "a()");

      "lambda has side effect objsetattr" >::
        (cmp "let (a = {[#extensible: false]})
              func(t){t[<#extensible>=true]}(a)"
           "let (a = {[#extensible: false]})
              a[<#extensible>=true]"
        );

      "don't inline if free vars exists" >::
        (no_change "let (a = func(x) { prim('+',x,t) })
                    let (t=2) {
                    a(t)
                    }");

      "mutation" >::
      (* one of the reason why inline function only applies to
         function in place
      *)
      (no_change "let (a = func(x){1}){
                    a := func(x){2};
                    a(2)
                    }");


      "don't inline if argument is assigned again" >::
        (no_change "let (a = func(x) { let (t = 1) {x:=t}})
                    let (t=2) {
                    a(t);
                    prim('pretty', t)
                    }");
      (*  it is bad to be inlined to:
              let (a = func(x) { let (t = 1) {x:=t}})
              let (t=2) {
                let (%alpha_t=1)
                  {t:=%alpha_t};
                prim('pretty', t)
              } *)


      "inline even if side effect will occur" >::
        (cmp "let (t=func(x){x:=1}) {
                func(x) { let (t = 1) x(t) }(t)
              }"
              "{let (t = func(x) {x := 1.})
                 {let (%alphaconv1 = 1.)
                     t(%alphaconv1)}}"
        );

      "don't inline: arguments are not consts or ids" >::
        (no_change "func(x,y){1}({[]}, 1)");

      "do nothing if the function is not propagated before being used" >::
        (no_change "let (x=func(x){1}) x(1)");

      "recursive function cannot be propagated so cannot be inlined " >::
        (no_change "rec (x=func(t){x(prim('-',t,1))})
              x(5)");

      (* ======================= test alpha conversion =================== *)

      (* x->t in env: t in env should be renamed to %alphaconvN *)
      "alpha conversion" >::
        (cmp "let (t=2) {
               func(x) { let (t = 1) t}(t)
              }"
             "let (t=2) {
                {let (%alphaconv1=1)
                  %alphaconv1}
              }"); 
      "alpha conversion 2" >::
        (cmp "let (a = 1)
              func(x) { let (a=3) {
                          prim('+', x, a);
                          let (a = 2) {
                            prim('+', x, a)
                          };
                          prim('+', x, a)
                      }}(a)"
              "let (a=1)
              { 
                let (%alphaconv1=3) {
                   prim('+', a, %alphaconv1);
                   let (%alphaconv2 = 2) {
                      prim('+', a, %alphaconv2)
                   };
                   prim('+', a, %alphaconv1)
                 }
              }");


      "conversion of rec" >::
        (cmp "let (r = {[#extensible: false]})
              func(x) {
                let (r = 1)
                rec (r = func(t) { r(prim('-',t,1))})
                  r(x)
              }(r)"


             "let (r = {[#extensible: false]})
              {
                let (%alphaconv1 = 1)
                rec (%alphaconv2 = func(t) { %alphaconv2(prim('-', t, 1))})
                  %alphaconv2(r)
              }
              ");           
                        
      "unable to inline invalid code" >::
        (no_change "func(x, y) {x;y}(1)");


    ]

let _ =
  run_test_tt_main suite
