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
        (cmp "let (a = func(x){prim('+', x, 1)})
              a(2)"
             "let (a = func(x){prim('+', x, 1)})
              prim('+', 2, 1)");

      "inlining for const function" >::
        (cmp "let (a = func(x){prim('+', x, 1)})
              a(func(x){x})"
             "let (a = func(x){prim('+', x, 1)})
              prim('+', func(x){x}, 1)");

      "inlining for lambda" >::
        (cmp "func(x){prim('+', x, 1)}(2)"
             "prim('+', 2, 1)");

      "inlining for const objects" >::
        (cmp "let (a = func(x){prim('+', x, 1)})
              let (b=1)
              a({[#extensible: false] 'fld':{#value b, #writable false}})"
             "let (a = func(x){prim('+', x, 1)})
              let (b=1)
              prim('+', {[#extensible: false] 'fld':{#value b, #writable false}}, 1)");

      "function inlining is not propagation" >::
        (no_change "let (a = func(t){1})
                    let (b = a)
                    let (c = b)
                    c(2)");

      "argument is constant variable" >::
        (cmp "let (a = func(t){t})
              let (b = func(x){x;x})
              b(a)"
             "let (a = func(t){t})
              let (b = func(x){x;x})
              {a;a}");

      "argument is const variable" >::
        (cmp "let (a = func(x){prim('+', x, 1)})
              let (b=1)
              let (c={[#extensible: false] 'fld':{#value b, #writable false}})
              a(c)"
             "let (a = func(x){prim('+', x, 1)})
              let (b=1)
              let (c={[#extensible: false] 'fld':{#value b, #writable false}})
              prim('+', c, 1)");

      "argument is constant variable that gets rebound" >::
        (cmp "let (a = func(t){t})
              let (b = func(x){x;x})
              let (a = 1)
              b(a)"
             "let (a = func(t){t})
              let (b = func(x){x;x})
              let (a = 1)
              {a;a}");

      (* even if we can inline in this situation, but the inlined result is 
         not be able to simplified by other phases
       *)
      (* 

      "argument is nonconstant variable" >::
        (cmp "let (a = func(t){t})
              let (b = func(x){x;x})
              let (a = {[]})
              b(a)"
             "let (a = func(t){t})
              let (b = func(x){x;x})
              let (a = {[]})
              {a;a}");

        "it is fine that argument is nonconstant variable" >::
        (cmp "let (x=func(t){prim('typeof', t)})
              x(other_var)"
             "let (x=func(t){t})
              prim('typeof', other_var)");
       *)

      (* tests below: side effect occurs in lambda, argument is constant  *)
      "lambda has side effect app()" >::
        (no_change "rec (x=func(t){t()})
                    let (t=func(a){a})
                    x(a)");

      "lambda has side effect objsetattr" >::
        (no_change "let (x=func(t){t[<#extensible>=true]})
                    let (a = {[#extensible: false]})
                    {x(a)}");

      "lambda has side effect objset fieldattr" >::
        (no_change "let (x=func(t){t['t'<#writable>=true]})
                    let (a = {[#extensible: false]})
                    {x(a)}");

      "lambda has side effect objset delete field" >::
        (no_change "let (x=func(t){t[delete 't']})
                    let (a = {[#extensible: false]})
                    {x(a)}");

      "lambda has side effect objset get field" >::
        (no_change "let (x=func(t){t['t']})
                    let (a = {[#extensible: false]})
                    {x(a)}");


              

      "don't inline if free vars exists" >::
        (no_change "let (a = func(x) { prim('+',x,t) })
                    let (t=2) {
                    a(t)
                    }");

      "mutation" >::
        (no_change "let (a = func(x){1}){
                    a := func(x){2};
                    a
                    }");


      "don't inline if side effect will occur" >::
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

      "don't inline if side effect will occur" >::
        (no_change "rec (a = func(x) { let (t = 1) x[<#extensible>=false]})
                    let (t=2) {
                    a(t);
                    prim('pretty', t)
                    }");

      "don't inline if side effect will occur" >::
        (no_change "rec (a = func(x) { let (t = 1) x(t) })
                    let (t=func(x){x:=1}) {
                    a(t)
                    }");
      
      "let rebind" >::
        (cmp "let (x=func(x){1})
              let (y=x)
              let (x=func(x){2}) {
              x(1)
              }"
             "let (x=func(x){1})
              let (y=x)
              let (x=func(x){2}) {
              2
              }");

      "rec rebind" >::
        (cmp "let (x=func(x){1})
              let (y=x)
              rec (x=func(x){2}) {
              x(1)
              }"
             "let (x=func(x){1})
              let (y=x)
              rec (x=func(x){2}) {
              2
              }");

      (* y is an alias of a const function but still y points to an identifier.
         doing constant propagation and then function inlining will work.
         not considering alias is for simplifying the scope problem like below*)
      "do nothing if alias is used" >::
        (no_change "let (x=func(x){1})
              let (y=x)
              let (x=func(x){2}) {
              y(1)
              }");

      "rec shadow" >::
        (cmp "let (x=func(a){a})
              let (y=x)
              rec (x = func(t) {t;t})
                x({[#extensible: false]})"
             "let (x=func(a){a})
              let (y=x)
              rec (x = func(t) {t;t}) {
                {[#extensible: false]}; {[#extensible: false]}}");

      "if side effect does not occur in the body of recursive function, do inlining" >::
        (cmp  "let (x=func(o){1})
               let (y=x)
               rec (x = func(t) { x(prim('-', t, 1) )})
               x(1)"
              "let (x=func(o){1})
               let (y=x)
               rec (x = func(t) { x(prim('-', t, 1))})
               x(prim('-', 1, 1))");

      "if side effect occurs in the body of recursive function, do not do inlining" >::
        (no_change  "let (x=func(o){1})
                     let (y=x)
                     rec (x = func(t) { x(prim('-', t, 1)); t()})
                     x(1)");

      "if side effect occurs in the body of recursive function, do not do inlining" >::
        (no_change  "let (x=func(o){1})
                     let (y=x)
                     rec (x = func(t) { x(prim('-', t['fld1'], 1))})
                     x(1)");

      "if side effect occurs in the body of recursive function, do not do inlining" >::
        (no_change  "let (x=func(o){1})
                     let (y=x)
                     rec (x = func(t) { x(prim('-', t['fld1'='3'], 1))})
                     x(1)");

      "if side effect occurs in the body of recursive function, do not do inlining" >::
        (no_change  "let (x=func(o){1})
                     let (y=x)
                     rec (x = func(t) { x(prim('-', t[<#extensible>=true], 1))})
                     x(1)");

      "recursive function" >::
        (cmp "rec (x=func(t){x(prim('-',t,1))})
              x(5)"
             "rec (x=func(t){x(prim('-',t,1))})
              x(prim('-', 5, 1))");

      (* ======================= test alpha conversion =================== *)

      (* x->t in env: t in env should be renamed to %alphaconvN *)
      "alpha conversion" >::
        (cmp "let (a = func(x) { let (t = 1) t})
              let (t=2) {
               a(t)
              }"
             "let (a = func(x) { let (t = 1) t})
              let (t=2) {
                {let (%alphaconv1=1)
                  %alphaconv1}
              }"); 
      "alpha conversion 2" >::
        (cmp "let (f=
              func(x) { let (a=3) {
                          prim('+', x, a);
                          let (a = 2) {
                            prim('+', x, a)
                          };
                          prim('+', x, a)
                      }})
              let (a=1)
              f(a)"
             "let (f=
              func(x) { let (a=3) {
                          prim('+', x, a);
                          let (a = 2) {
                            prim('+', x, a)
                          };
                          prim('+', x, a)
                      }})
              let (a=1)
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
        (cmp "let (f=
              func(x) {
                let (r = 1)
                rec (r = func(t) { r(prim('-',t,1))})
                  r(x)
              })
              let (r = {[#extensible: false]})
              f(r)"


             "let (f=
              func(x) {
                let (r = 1)
                rec (r = func(t) { r(prim('-',t,1))})
                  r(x)
              })
              let (r = {[#extensible: false]})
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
