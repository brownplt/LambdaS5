open Prelude
open Util
open OUnit2
open Ljs_deadcode_elimination

let suite =
  let cmp before after = 
    let test test_ctx =
      let dest = parse after in
      let opted = eliminate_ids (parse before) in
      assert_equal 
        ~printer:ljs_str
        ~cmp:equal_exp
        dest opted
    in
    test
  in 
  let no_change code = cmp code code in
  "Test Unused id elimination" >:::
    ["unused at all" >:: 
       (cmp "let (x=1)
             let (y=x)
             let (z=y)
             x"
            "let (x=1) x");

     "chained id" >:: 
       (cmp "let (x=1)
             let (y=x)
             let (z=x)
             z"
            "let (x=1)
             let (z=x)
             z");

     "test setbang" >::
       (no_change "let (x=1)
                   x := 2");

     "let contains other lets" >::
       (cmp "let (x=1)
             let (y={let (z = x)
                     x})
             let (z=1)
             {z;y}"
            "let (x=1)
             let (y=x)
             let (z=1)
             {z;y}");

     "let contains other lets with side-effect" >::
       (cmp "let (x=1)
             let (y={let(z=10) x:=z})
             let (x=3)
             {x; y}"
            "let (x=1)
             let (y={let(z=10) x:=z})
             let (x=3)
             {x; y}");

     (* binding shadows *)
     "let shadow" >::
       (cmp "let (x=1)
             let (y=x)
             let (x=2)
             y"
            "let (x=1)
             let (y=x)
             y");

     "let shadow2" >::
       (cmp "let (x=1)
             let (x=2)
             let (x=3)
             x"
            "let (x=3)
             x");

     "lambda arguments shadow previous binding" >::
       (cmp "let (x=1)
             let (y=func(x){prim('+', x, 1)})
             y(2)"
            "let (y=func(x){prim('+',x,1)})
             y(2)");

     "id collection should also be performed in lambda body 1" >::
       (cmp "let (x = 1)
             let (y = func(s) {
                          x := s
                      })
                 y"
            "let (x = 1)
             let (y = func(s) {
                          x := s
                      })
                 y");

     "id collection should also be performed in lambda body 2" >::
       (cmp "let (x = 1)
             let (y = func(s) {
                        let (x = 1)
                          x := s
                      })
                 y"
            "let (y = func(s) {
                        let (x = 1)
                          x := s
                      })
                 y");
            
     (* side effect *)
     "side effect test 0" >::
       (no_change "let (x = 1)
                   let (y = prim('pretty', x))
                   x");

     "side effect test 1" >::
       (no_change "let (x = 1)
                   let (y = {[] 
                             'fld': {#value prim('print', x), #writable true}})
                   x");

     "side effect test 2" >::
       (cmp  "let (x = 1)
              let (y = {[#proto:null] 'fld': {#value prim('+', x, 1), #writable true}})
              x"
             "let (x = 1)
              x");

     "side effect test 3" >::
       (cmp "let (x = 1)
             let (y = {[]})
             x"
            "let (x = 1)
             x");

     "side effect test 4" >::
       (cmp "let (x = 1)
             let (y = func(t) { prim('print', x) })
             x"
            "let (x = 1)
             x");

     "side effect test 5" >::
       (no_change "let (y = o['field1'])
                   x");

         
    ]

       

let _ =
  run_test_tt_main suite
    
