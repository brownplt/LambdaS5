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
  let eligible_test (jscode : string) (expected : bool) = 
    fun test_ctx ->
      let s5code = desugar jscode in
      assert_equal expected (eligible_for_preprocess s5code)
        ~printer: (fun x -> if x then "eligible" else "not eligible")
  in 
  let window_free_test (jscode : string) (expected : bool) =
    fun test_ctx ->
      let s5code = desugar jscode in
        assert_equal expected (window_free s5code)
          ~printer: (fun x -> if x then "window free" else "not window free")
  in
  let eq (jscode : string) (expected : string) =
    (* this function will first assert the code is eligible for preprocessing.
       and evaluate the jscode and expected, and compare the result with that of 
       expected *)
    fun text_ctx ->
      let es5env = Ljs.parse_es5_env (open_in "../envs/es5.env") "../envs/es5.env" in
      let s5code = desugar jscode in
      let s5expected = desugar expected in
      assert_equal true (eligible_for_preprocess s5code)
        ~printer: (fun x -> if x then "eligible" else "not eligible");
      let s5value = Ljs_eval.eval_expr (es5env s5code) desugar true in
      let expectedv = Ljs_eval.eval_expr (es5env s5expected) desugar true in
      match s5value, expectedv with
      | Ljs_eval.Answer(_,value,_,_), Ljs_eval.Answer(_,value2,_,_) ->
        assert_equal value2 value
          ~printer: (Ljs_values.pretty_value)
  in 
  let is_window_free (jscode : string) =
    window_free_test jscode true
  in
  let not_window_free (jscode : string) =
    window_free_test jscode false
  in
  let eligible (jscode : string) =
    eligible_test jscode true
  in 
  let not_eligible (jscode : string) =
    eligible_test jscode false
  in 
  "Test Preprocess" >:::
  [
    (* ------- test window free ------- *)
    "not window free: window reference" >::
    (not_window_free "this.window");

    "not window free: window def" >::
    (not_window_free "this.window.x = 1");

    "not window free: window reference" >::
    (not_window_free "this.window['x']");

    "not window free: window reference" >::
    (not_window_free "this['window']");

    "not window free: window reference" >::
    (not_window_free "window");

    "not window free: window def" >::
    (not_window_free "window.x = 1");

    "not window free: window reference" >::
    (not_window_free "window['x']");

    "not window free: directly refer to window in functions" >::
    (not_window_free "function foo() { var a = window }");

    "not window free: directly refer to window in functions" >::
    (not_window_free "function foo() { window['x'] = 1 }");

    "not window free: directly refer to window in functions" >::
    (not_window_free "function foo() { window.x = 1 }");

    "not window free: passing window " >::
    (not_window_free "function foo() { bar(window);}");

    "window free: window in functions" >::
    (is_window_free "function foo() { this.window }");

    "window free: window in functions" >::
    (is_window_free "function foo() { this.window.x = 1 }");

    "window free: window in functions" >::
    (is_window_free "function foo() { this.window['x'] = 1 }");

    "window free: window in functions" >::
    (is_window_free "function foo(a) { a.window['x'] = 1 }");

    (* todo: find user code *)
    "eligible" >::
    (eligible "'use strict'; var i = 1");

    "eligible" >::
    (eligible "'use strict'; function foo() {var a = 1}; foo()");

    "eligible" >::
    (eligible "'use strict'; function foo() {this.a = 1}");

    "not eligible: assignment through window" >::
    (not_eligible "'use strict'; function foo() {var a = 1; window['x'] = a}");

    "not eligible: assignment through window" >::
    (not_eligible "'use strict'; function foo() {window.x = 1;}");
    
    "not eligible: assignment through window" >::
    (not_eligible "'use strict'; this.window['x'] = 1");

    "not eligible: assignment through window" >::
    (not_eligible "'use strict'; this.window.x = 1;");

    (* the top level this can always be tranformed correctly if
       no computation string field exists *)
    "eligible: assignment through this, with declaration" >::
    (eligible "'use strict'; var x = 2; this.x = 1;");

    "eligible: assignment through this, without declare" >::
    (eligible "'use strict'; this.x = 1;");

    "eligible: assignment through this, with declaration" >::
    (eligible "'use strict'; var x = 2; this['x'] = 1;");

    "eligible: assignment through this, without declaration" >::
    (eligible "'use strict'; this['x'] = 1;");

    "not eligible alias this" >::
    (not_eligible
       "'use strict';
        a = this;
        a.x = 1;");

    "not eligible alias window" >::
    (not_eligible 
       "'use strict';
        a = window;
        a.x = 1;");

    "not eligible alias this.window" >::
    (not_eligible 
       "'use strict';
        a = this.window;
        a.x = 1;");

    "not eligible alias this[window]" >::
    (not_eligible 
       "'use strict';
        a = this['window'];
        a.x = 1;");

    "tricky" >::
    (not_eligible
       "'use strict';
         var o = {'a' : this; 'b' : 1};
         var x = 2;
         function foo(t) { t.a['x'] = 1 }     
         foo(o); x");

    "not eligible passing window" >::
    (not_eligible 
       "'use strict';
        function foo(a) {a.x = 14}
        foo(this.window);");

    "not eligible passing window" >::
    (not_eligible 
       "'use strict';
        function foo(a) {a.x = 14}
        foo(window);");

    "not eligible passing this to a function" >::
    (not_eligible
      "'use strict';
       var x = 1;
       function foo(a) { a.x = 15; }
       foo(this)
     ");

    "eligible passing this to a function in a function" >::
    (eligible
      "'use strict';
       function foo(a) { return a(this); }
       foo(1)
     ");

    "not eligible passing this to a function" >::
    (not_eligible
      "'use strict';
       function foo(a,b,c,d,e,f) { f.x = 15; }
       foo(1,2,3,4,5, this)
     ");

    "not eligible passing this to a function" >::
    (not_eligible
      "'use strict';
       function foo(a) {a.x = 15}
       foo(1, bar(zar(this)))");

    "not eligible nonstrict mode is not eligible" >::
    (not_eligible 
      "var bar = 2;
        function foo() { this.bar = 1 }
        foo();
        bar");

    "not eligible: computation string field" >::
    (not_eligible 
      "'use strict';
       var bar = 2;
       this['b'+'bar'] = 3;
       bar");

    "not eligible: computation string field" >::
    (not_eligible 
      "'use strict';
       var bar = 2;
       this.window['b'+'bar'] = 3;
       bar");
    
    "not eligible: computation string field" >::
    (not_eligible 
      "'use strict';
       var bar = 2;
       window['b'+'bar'] = 3;
       bar");

    "not eligible: computation string field" >::
    (not_eligible 
      "'use strict';
       var bar = 2;
       var foo = window['ba'+'r'];
       foo");

    "not eligible: computation string field" >::
    (not_eligible 
      "'use strict';
       var bar = 2;
       var foo = this['ba'+'r'];
       foo");

    "not eligible: computation string field" >::
    (not_eligible 
      "'use strict';
       var bar = 2;
       var foo = this.window['ba'+'r'];
       boo");

    "eligible: computation string field on normal object" >::
    (eligible
      "'use strict';
       var bar = {'a1' : console};
       var foo = bar['a'+'1'];
       foo");

    "not eligible: computation string field on global alias" >::
    (not_eligible 
      "'use strict';
       var bar = window;
       var foo = bar['a'+'1'];
       foo");

    (* todo: use arguments keyword *)
    (* todo: use ++, -- *)
    (* todo: make preprocess works over environment *)

    "test this" >::
    (eq  "'use strict'; 
          var x = 1; 
          this.x = 2; x" "2");
    
    "test this" >::
    (eq "'use strict'; var x = 1; this['x'] = 3; x" "3");

    "test global scope" >::
    (eq "'use strict'; var x = 1; function foo(a) {return a + x}; foo(10)" "11");

    "test global scope shadowed" >::
    (eq "'use strict'; var x = 1; function foo(a) {var x = 100; return a + x;}; foo(10)" "110");

    "process arguments" >::
    (eq "'use strict'; function foo(a) {arguments[0] = 2; return a}; foo(1)" "1");

    "computation on normal object" >::
    (eq "'use strict';
         var bar = {'a1' : 100};
         var foo = bar['a'+'1'];
         foo" "100");

    "assignment through on top-level this" >::
    (eq "'use strict';
         var bar = 1;
         var foo = this.bar;
         foo" "1");

    "computation field in function" >::
    (eq "'use strict';
         function foo() { this['b'+'ar'] = 1 };
         var o = {'bar' : 2};
         o.foo = foo;
         o.foo(); o.bar" "1");

    "redefine global variables" >::
    (eq "'use strict';
         var console = {'log' : 1};
         console.log" "1");

    "redefine global variables. testing context in function" >::
    (eq "'use strict';
         function foo() { return console.log };
         var console = {'log' : 1 };
         foo()" "1");

    "redefine global variables in function" >::
    (eq "'use strict';
         function foo() { var console = {'log' : 1}; return console.log };
         foo(); console.log" "console.log");
  ]       
  

let _ = 
  (* make sure the working directory is in src *)
  run_test_tt_main suite

