open Prelude
open Util
open OUnit2
open Ljs_function_inlining

let suite = 
  let cmp before after = cmp before function_inlining after in
  let no_change code = no_change code function_inlining in 
  "Test Prim Propagation" >:::
    [
      "simple inlining" >::
        (cmp "let (a = func(){1})
              a(1)"
             "let (a = func(){1})
              func(){1}(1)");

      "simple inlining 2" >::
        (cmp "let (a = func(){1})
              let (b = a)
              let (c = b)
              c"
             "let (a = func(){1})
              let (b = func(){1})
              let (c = func(){1})
              func(){1}");

      "deeply inline" >::
        (cmp "let (a = func(){1})
              let (b = {[] 'fld': {#getter a, #setter a}})
              b"
             "let (a = func(){1})
              let (b = {[] 'fld': {#getter func(){1}, #setter func(){1}}})
              b");

      "mutation" >::
        (no_change "let (a = func(){1})
                    let (b = a) {
                    a := 12;
                    b
                    }");
      
      "let shadow" >::
        (cmp "let (x=func(){1})
              let (y=x)
              let (x=2) {
              x := 3; x
              }"
             "let (x=func(){1})
              let (y=func(){1})
              let (x=2){
              x := 3; x
              }");

      "rec shadow" >::
        (cmp "let (x=func(){1})
              let (y=x)
              rec (x = func(t) {t})
              x"
             "let (x=func(){1})
              let (y=func(){1})
              rec (x = func(t) {t})
              func(t){t}");

      "lambda argument" >::
        (cmp "let (x=func(){1})
              let (y=x)
              let (t = func(x,y) {prim('+',x,y)})
              t(x, y)"
             "let (x=func(){1})
              let (y=func(){1})
              let (t = func(x,y) {prim('+',x,y)})
              func(x,y){prim('+',x,y)}(func(){1},func(){1})");

      "lambda argument 2" >::
        (cmp "let (x=func(){1})
              let (y=x)
              let (t = func(x) {prim('+',x,y)})
              t(y)"
             "let (x=func(){1})
              let (y=func(){1})
              let (t = func(x) {prim('+',x,func(){1})})
              func(x){prim('+',x,func(){1})}(func(){1})");

      "non-freevars lambda has side effect and used many time" >::
        (no_change "let (x=func(x){prim('pretty', x)})
                    {x(1); x(2); x(3)}");

      "non-freevars lambda has side effect but used once" >::
        (cmp "let (x=func(x){prim('pretty', x)})
              x(1)"
             "let (x=func(x){prim('pretty', x)})
              func(x){prim('pretty', x)}(1)");

      "lambda has free vars used once" >::
        (no_change "let (x=func(){y})
                    let (y=1)
                    x()");

      "lambda has free vars used many times" >::
        (no_change "let (x=func(){y})
                    let (y=1) {
                    x();x();x()
                    }");
             
      "constant lambda applies to non-constant vars only once" >::
        (cmp "let (x=func(t){t})
              x(other_var)"
             "let (x=func(t){t})
              func(t){t}(other_var)");
      
      "recursive function" >::
        (cmp "rec (x=func(t){x(prim('-',t,1))})
              x(5)"
             "rec (x=func(t){x(prim('-',t,1))})
              x(5)");

      "constant lambda applies to non-constant vars many times" >::
        (no_change "let (x=func(t){t}) {
                    x(var1); x(var2); x(var3)}");

      (* tests below have side effect and uses x twice. *)
      "lambda has side effect app()" >::
        (no_change "rec (x=func(t){t()})
                    {x();x()}");

      "lambda has side effect app()" >::
        (no_change "let (x=func(t){t()})
                    {x();x()}");

      "lambda has side effect objsetattr" >::
        (no_change "let (x=func(t){t[<#extensible>=true]})
                    {x;x}");

      "lambda has side effect objset fieldattr" >::
        (no_change "let (x=func(t){t['t'<#writable>=true]})
                    {x;x}");

      "lambda has side effect objset delete field" >::
        (no_change "let (x=func(t){t[delete 't']})
                    {x;x}");

      "lambda has side effect objset get field" >::
        (no_change "let (x=func(t){t['t']})
                    {x;x}");


    ]

let _ =
  run_test_tt_main suite
