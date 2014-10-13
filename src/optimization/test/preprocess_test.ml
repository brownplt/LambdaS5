open Prelude
open Util
open OUnit2
open Ljs_preprocess
open Sys

let jsparser_path = "../tests/jsparser.sh"

let desugar (s : string) : Ljs_syntax.exp =
  try
    Ljs_desugar.parse_and_desugar jsparser_path s
  with Ljs_values.PrimErr (t, v) -> 
    failwith ("Error while desugaring: " ^ Ljs_values.pretty_value v ^ "\n")
  
let suite = 
  (* eval to the same value *)
  let eq before after = cmp before preprocess after in
  let eligible_test (jscode : string) (expected : bool) = 
    fun test_ctx ->
      let s5code = desugar jscode in
      assert_equal expected (eligible_for_preprocess s5code)
        ~printer: (fun x -> if x then "eligible" else "not eligible")
  in 
  "Test Preprocess" >:::
  [
    (* find user code *)
    "eligible1" >::
    (eligible_test "'use strict'; var i = 1" true);

    "eligible2" >::
    (eligible_test "'use strict'; function foo() {window['x'] = 1}" false);
    
    "eligible3 alias this" >::
    (eligible_test 
       "'use strict';
        a = this;
        a.x = 1;" false);

    "eligible4 passing this to a function" >::
    (eligible_test
      "'use strict';
       function foo(a) { a.x = 15; }
       foo(this)
     " false);

    "eligible5 with(o)" >::
    (eligible_test
      "'use strict';
       var o = {'a':1};
       var a = 2;
       var b = -1;
       with(o) {
         b = a;
       }
       b;
      " false);

    "eligible6 nonstrict mode is not eligible anyway" >::
    (eligible_test 
      "var bar = 2;
        function foo() { this.bar = 1 }
        foo();
        bar" false)
    
     
    
  ]       
  

let _ = 
  (* make sure the working directory is in src *)
  run_test_tt_main suite
  
