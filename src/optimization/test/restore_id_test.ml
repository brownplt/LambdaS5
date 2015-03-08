open Prelude
open Util
open OUnit2
open Ljs_restore_id
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
      assert_equal expected (eligible_for_restoration s5code)
        ~printer: (fun x -> if x then ("eligible:\n" ^ jscode)
                    else ("not eligible:\n" ^ jscode))
  in 
  let window_free_test ?(td=false) (jscode : string) (expected : bool) =
    fun test_ctx ->
      let s5code = desugar jscode in
      (if td then todo "todo" else ());
      assert_equal expected (window_free s5code)
        ~printer: (fun x -> if x then "window free" else "not window free")
  in
  let eq ?(nyi=false) (jscode : string) (expected : string) =
    (* this function will first assert the code is eligible for restoreing.
       and evaluate the jscode and expected, and compare the result with that of 
       expected *)
    fun text_ctx ->
      (if nyi then todo "not implemented"
       else ());
      let es5env = Ljs.parse_es5_env (open_in "../envs/es5.env") "../envs/es5.env" in
      let s5code = desugar jscode in
      let s5expected = desugar expected in
      assert_equal true (eligible_for_restoration s5code)
        ~printer: (fun x -> if x then "eligible" else "not eligible");
      let s5value = Ljs_eval.eval_expr (restore_id (es5env s5code)) desugar true in
      let expectedv = Ljs_eval.eval_expr (es5env s5expected) desugar true in
      match s5value, expectedv with
      | Ljs_eval.Answer(_,value,_,_), Ljs_eval.Answer(_,value2,_,_) ->
        assert_equal value2 value
          ~printer: (Ljs_values.pretty_value)
  in 
  let is_window_free ?(td=false) (jscode : string) =
    window_free_test ~td jscode true
  in
  let not_window_free ?(td=false) (jscode : string) =
    window_free_test ~td jscode false
  in
  let eligible (jscode : string) =
    eligible_test jscode true
  in 
  let not_eligible (jscode : string) =
    eligible_test jscode false
  in 
  "Test Restore" >:::
  [
    (* ------- test window free ------- *)
    "not window free: window reference" >::
    (not_window_free "this.window");

    "not window free: window def" >::
    (not_window_free "this.window.x = 1");

    "is window free: window reference" >::
    (is_window_free ~td:true "this.window['x']");

    "not window free: window reference" >::
    (not_window_free "this['window']");

    "not window free: window reference" >::
    (not_window_free "window");

    "not window free: window def" >::
    (not_window_free "window.x = 1");

    "is window free: use property of window" >::
    (is_window_free ~td:true "window['x']");

    "is window free: use property of window" >::
    (is_window_free ~td:true "window['x']()");

    "is window free: use property of window" >::
    (is_window_free ~td:true "if (window.var == 1) {1} else {2}");

    "is window free: use property of window" >::
    (is_window_free ~td:true "var x = window.var");

    "not window free: directly refer to window in functions" >::
    (not_window_free "function foo() { var a = window }");

    "not window free: directly refer to window in functions" >::
    (not_window_free "function foo() { window['x'] = 1 }");

    "not window free: directly refer to window in functions" >::
    (not_window_free "function foo() { window.x = 1 }");

    "not window free: passing window " >::
    (not_window_free "function foo() { bar(window);}");

    "not window free: return window" >::
    (not_window_free "function foo() { return window }");

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

    "getter and setter: o.x will create o.y" >::
    (eligible
      "'use strict'; var o = {get x() { this['y'] = 1}}; o.x");

    "alias in the object field" >::
    (not_eligible
       "'use strict';
         var o = {'a' : this, 'b' : 1};
         ");

    "alias in the array field" >::
    (not_eligible
       "'use strict';
         var o = [this];
         ");

    "eligible: alias in the object field in function" >::
    (eligible
       "'use strict';
         function foo() {var o = {'a' : this, 'b' : 1};}
         ");

    "tricky alias this in the object field" >::
    (not_eligible
       "'use strict';
         var o = {'a' : f(g(z(this))), 'b' : 1};
         var x = 2;
         function foo(t) { t.a['x'] = 1 }     
         foo(o); x");

    "tricky checking" >::
    (eligible
       "'use strict';
         var o = {'a' : function foo() { this.bar = 1 }, 'b' : 1};");

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

    "eligible" >::
    (eligible
      "'use strict';
       var x = 1;
       function foo(a) { a.x = 15; }
       foo(function(){this})
     ");

    "eligible passing this to a function in a function" >::
    (eligible
      "'use strict';
       function foo(a) { return a(this); }
       foo(1)
     ");
    
    "not eligible delete field from this" >::
    (not_eligible
      "'use strict';
        var x = 1;
        function foo() {return delete this.x}
        var o = {'x' : 1, 'f' : foo};
        o.f()");

    "not eligible delete field from this" >::
    (not_eligible
      "'use strict';
        var x = 1;
        function foo() {return delete this.x}
        foo()");


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
    
    "not eligible: iterate through toplevel this keyword" >::
    (not_eligible
      "'use strict';
       for (i in this) { i }");

    "eligible: iterate through this keyword in function" >::
    (eligible
      "'use strict';
       function foo() { for(i in this) {i}}");

    "not eligible nonstrict mode is not eligible" >::
    (fun ctx ->
       skip_if (Ljs_restore_id.only_strict = false) "only strict mode is off";
       let s5code = desugar "var bar = 2; bar" in
       assert_equal false (eligible_for_restoration s5code));

    "not eligible nonstrict mode is not eligible" >::
    (fun ctx ->
       todo "this case should not be thought as alias this";
       let s5code = desugar "var f = function () {return 1}
                             var o = {'v1' : this['f']()}
                             o.v1" in
       assert_equal true (eligible_for_restoration s5code));


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

    (* uncomment this when window is able to be analyzed
    "eligible: use window property by computation string field" >::
    (eligible 
      "'use strict';
       var bar = 2;
       var foo = window['ba'+'r'];
       foo");*)

    "not eligible: computation string field" >::
    (not_eligible 
      "'use strict';
       var bar = 2;
       var foo = this['ba'+'r'];
       foo");
    (* uncomment this when window is able to be analyzed
    "eligible: use window property by computation string field" >::
    (eligible 
      "'use strict';
       var bar = 2;
       var foo = this.window['ba'+'r'];
       boo");*)

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
    (* todo: make restore works over environment *)

    "test this" >::
    (eq  "'use strict'; 
          var x = 1; 
          this.x = 2; x" "2");
    
    "test this" >::
    (eq "'use strict'; var x = 1; this['x'] = 3; x" "3");

    (* this['f'] in this case will desugar to let(t=%this) ToObject(t)... *)
    "test alias this" >::
    (eq "'use strict'; var f = function () {return 1;}; this['f']()" "1");

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

    "directly add variable in this" >::
    (eq "'use strict';
         this.count = 0;
         ++count" "1");

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

    "typeof desugar to typeof(context, id)" >::
    (eq "'use strict';
         var x = function() {}; typeof x"
        "'function'");

    "global var scope" >::
    (eq "'use strict';
         var x = 1;
         function foo() {var y = 2; x = y;}
         foo();
         x" "2");

    "global var scope" >::
    (eq "'use strict';
         var x = 1;
         function foo() {var x = 2; x = 3;}
         foo();
         x" "1");

    (* test ++, -- *)
    "test++" >::
    (eq "'use strict'; var i = 1; var j = (i++); if (i == 2 && j == 1) {true} else {false}"
        "true");

    "test--" >::
    (eq "'use strict'; var i = 1; var j = (i--); if (i == 0 && j == 1) {true} else {false}"
        "true");

    "test++" >::
    (eq "'use strict'; var i = 1; var j = (++i); if (i == 2 && j == 2) {true} else {false}"
        "true");

    "test--" >::
    (eq "'use strict'; var i = 1; var j = (--i); if (i == 0 && j == 0) {true} else {false}"
        "true");

    "test-- on non-number" >::
    (eq "'use strict'; function foo(){}; var j = (--foo); if (isNaN(foo) && isNaN(j)) {true} else {false}"
        "true");

    "test-- on non-number" >::
    (eq "'use strict'; function foo(){}; var j = (foo--); if (isNaN(foo) && isNaN(j)) {true} else {false}"
        "true");

    "test++ on non-number" >::
    (eq "'use strict'; function foo(){}; var j = (++foo); if (isNaN(foo) && isNaN(j)) {true} else {false}"
        "true");

    "test++ on non-number" >::
    (eq "'use strict'; function foo(){}; var j = (foo++); if (isNaN(foo) && isNaN(j)) {true} else {false}"
        "true");
    
    (* NaN and undefined are values, they are also defined in %global. careless substitution will return
       in let (NaN = NaN)..., previous NaN is id, the latter is Num *)
    "use NaN" >::
    (eq "'use strict'; undefined" "undefined");
    
    "use undefined" >::
    (eq "'use strict'; isNaN(NaN)" "true");

    "assign to unwritable field" >::
    (eq "'use strict'; try {NaN=1;false} catch (e) {e instanceof TypeError}" "true");

    "assign to unwritable field" >::
    (eq "'use strict'; try {this.NaN=1;false} catch (e) {e instanceof TypeError}" "true");

    "assign to unwritable field" >::
    (eq "'use strict'; try {this['NaN']=1;false} catch (e) {e instanceof TypeError}" "true");

    "assign to unwritable field" >::
    (eq "'use strict'; try {undefined=1;false} catch (e) {e instanceof TypeError}" "true");

    "assign to unwritable field" >::
    (eq "'use strict'; try {Infinity=1;false} catch (e) {e instanceof TypeError}" "true");

    "reassign unwritable field" >::
    (eq "'use strict'; try {var NaN=1;false} catch (e) {e instanceof TypeError}" "true");

    "assign unwritable field in function" >::
    (eq "'use strict'; function foo() {var NaN=1;return NaN}; try {foo()} catch (e) {false}" "1");

  ]       
  

let _ = 
  (* make sure the working directory is in src *)
  run_test_tt_main suite

