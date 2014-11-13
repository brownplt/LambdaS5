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

    "setbang x in let x_v" >::
    (cmp
       "let (x = {let (y = 3)
          let (w = 4) 
          let (z = {let (q = w) {T:=w; w}})
            z})
        {T := 12; T}"
      "let (x = {let (y = 3)
          let (w = 4) 
          let (z = {let (q = w) {T:=w; w}})
            z})
       {let (T = 12) T}"
    );

    "setbang in function" >::
    (no_change
      "let (T = undefined)
       let (bar = func() {T})
       let (foo = func() { T:=3; undefined })
       {
         foo();
         bar()
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

    "js func pattern" >::
    (cmp
      "let (foo = undefined)
         {let (#strict=true)
          {'use strict';
           {let (%fobj = {let (x = 1) x})
              foo := %fobj};
           use(foo)}}"
      "let (foo = undefined)
         {let (#strict=true)
          {'use strict';
           {let (foo = {let (x = 1) x})
             use(foo)}}}"
    );

    "js func pattern 2: function with strict mode" >::
    (cmp 
      "let (foo = undefined)
       {let (#strict=true)
        {let (%fobj = {let (x = 1) x}) foo := %fobj};
        use(foo)}"
      "let (foo = undefined)
       {let (#strict=true)
        {let (foo = {let (x = 1) x})
        use(foo)}}"
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

    "js recursive function pattern" >::
    (no_change
       "{let (fobj16 = {let (proto={[]})
                         let (parent=context)
                         let (thisfunc15 = {[#code: func(this, args){
                                  foo(undefined, mkargs())
                            }]}) {
                            proto['constructor' = thisfunc15];
                            thisfunc15}})
            foo := fobj16};
          let (fun2 = foo)
          use(fun2)"
    );

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
    (cmp "let (foo = undefined){
          {let (fobj16 = 
            {let (proto={[]})
             let (parent=context)
             let (thisfunc15 = {[#code: func(){
                    let (bar = undefined){
                    {let (fobj17 = {let (proto={[]})
                         let (parent=context)
                         let (thisfunc16 = {[#code: func(){1}]}) {
                            proto['constructor' = thisfunc16];
                            thisfunc16}})
                     bar := fobj17};
                     use(bar)}

             }]})
             {proto['constructor' = thisfunc15]; thisfunc15}})
            foo := fobj16};
            let (fun2 = foo)
            use(fun2)}"

         "let (foo = undefined){
          let (foo = 
            {let (proto={[]})
             let (parent=context)
             let (thisfunc15 = {[#code: func(){
                    let (bar = undefined){
                    {let (bar = {let (proto={[]})
                         let (parent=context)
                         let (thisfunc16 = {[#code: func(){1}]}) {
                            proto['constructor' = thisfunc16];
                            thisfunc16}})
                     use(bar)}}

             }]})
             {proto['constructor' = thisfunc15]; thisfunc15}})
            let (fun2 = foo)
            use(fun2)}"
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
    
    (* a in b's scope is the top-level a *)
    "variable scope" >::
    (no_change
      "let (a = 1) {
        let (b = func() {a}) {
        a := 2;
        b();
        a
        } }");

    "variable scope" >::
    (no_change
      "let (a = 1) {
        let (b = func() {a:=2}) {
        a := 3;
        b();
        a
        } }");

    "variable scope" >::
    (cmp
      "let (a = 1) let (f = undefined) {
        {let (b = func() {a:=2}) f:=b};
        a := 3;
        f();
        a
        }"
      "let (a = 1) let (f = undefined) {
        let (f = func() {a:=2}) {
        a := 3;
        f();
        a}
        }"      
    );



  ]

let _ =
  run_test_tt_main suite
