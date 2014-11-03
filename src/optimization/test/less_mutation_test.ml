open Prelude
open Util
open OUnit2
open Ljs_less_mutation

let suite =
  let cmp before after = cmp before less_mutation after in
  let no_change code = no_change code less_mutation in
  "Test Less Mutation" >:::
  [
    "transform SetBang to Let" >::
    (cmp 
       "x := 2; let (y = x) y"
       "let (x = 2) let (y=x) y"
    );

    (* todo setbang and recursive function *)
    "setbang x and usage x are in different seq" >::
    (no_change
      "let (x = undefined) {
         {let (y = 2) x := y; x};
         x
       }"
    );

    "let shadow" >::
    (cmp
       "let (x = undefined) {
         {x := 2; x};
         {let (x = 3) x}
       }"
       "let (x = undefined) {
         {let (x = 2) x};
         {let (x = 3) x}
       }"
    );
    
    "js function pattern" >::
    (cmp "{let (fobj16 = {let (proto={[]})
                         let (parent=context)
                         let (thisfunc15 = {[#code: func(){1}]}) {
                            proto['constructor' = thisfunc15];
                            thisfunc15}})
            foo := fobj16};
          let (fun2 = foo)
          use(fun2)"

         "let (foo = {let (proto={[]})
                         let (parent=context)
                         let (thisfunc15 = {[#code: func(){1}]}) {
                            proto['constructor' = thisfunc15];
                            thisfunc15}})
           let (fun2 = foo)
           use(fun2)");

    "js function patterns" >::
    (cmp "{let (fobj16 = {let (proto={[]})
                         let (parent=context)
                         let (thisfunc15 = {[#code: func(){1}]}) {
                            proto['constructor' = thisfunc15];
                            thisfunc15}})
            foo := fobj16};
          {let (fobj17 = {let (proto={[]})
                         let (parent=context)
                         let (thisfunc15 = {[#code: func(){1}]}) {
                            proto['constructor' = thisfunc15];
                            thisfunc15}})
            bar := fobj17};
          {let (fobj18 = {let (proto={[]})
                         let (parent=context)
                         let (thisfunc15 = {[#code: func(){1}]}) {
                            proto['constructor' = thisfunc15];
                            thisfunc15}})
            zoo := fobj18};
          let (fun2 = foo) {use(fun2)};
          let (fun3 = bar) {use(fun3)};
          let (fun4 = zoo) {use(fun4)}
          "
       "{let (foo = {let (proto={[]})
                         let (parent=context)
                         let (thisfunc15 = {[#code: func(){1}]}) {
                            proto['constructor' = thisfunc15];
                            thisfunc15}})
          {let (bar = {let (proto={[]})
                         let (parent=context)
                         let (thisfunc15 = {[#code: func(){1}]}) {
                            proto['constructor' = thisfunc15];
                            thisfunc15}})
          {let (zoo = {let (proto={[]})
                         let (parent=context)
                         let (thisfunc15 = {[#code: func(){1}]}) {
                            proto['constructor' = thisfunc15];
                            thisfunc15}})
          {let (fun2 = foo) {use(fun2)};
           let (fun3 = bar) {use(fun3)};
           let (fun4 = zoo) {use(fun4)}}}}}
          ");

    "js function patterns nested" >::
    (cmp "{let (fobj16 = 
            {let (proto={[]})
             let (parent=context)
             let (thisfunc15 = {[#code: func(){

                    {let (fobj17 = {let (proto={[]})
                         let (parent=context)
                         let (thisfunc15 = {[#code: func(){1}]}) {
                            proto['constructor' = thisfunc15];
                            thisfunc15}})
                     bar := fobj17};
                     use(bar)

             }]})
             {proto['constructor' = thisfunc15]; thisfunc15}})
            foo := fobj16};
            let (fun2 = foo)
            use(fun2)"

         "let (foo = 
            {let (proto={[]})
             let (parent=context)
             let (thisfunc15 = {[#code: func(){

                    {let (bar = {let (proto={[]})
                         let (parent=context)
                         let (thisfunc15 = {[#code: func(){1}]}) {
                            proto['constructor' = thisfunc15];
                            thisfunc15}})
                     use(bar)}

             }]})
             {proto['constructor' = thisfunc15]; thisfunc15}})
            let (fun2 = foo)
            use(fun2)"
    );
    "js function patterns. function is defined but not used" >::
    (cmp 
      "let (fobj16 = {let (proto={[]})
                         let (parent=context)
                         let (thisfunc15 = {[#code: func(){1}]}) {
                            proto['constructor' = thisfunc15];
                            thisfunc15}})
        foo := fobj16"
      "let (foo = {let (proto={[]})
                         let (parent=context)
                         let (thisfunc15 = {[#code: func(){1}]}) {
                            proto['constructor' = thisfunc15];
                            thisfunc15}})
        undefined"
    );
  ]

let _ =
  run_test_tt_main suite
