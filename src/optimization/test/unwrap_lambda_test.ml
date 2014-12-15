open Prelude
open Util
open OUnit2
open Ljs_unwrap_lambda
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
      assert_equal expected (eligible_for_unwrap_lambda s5code)
        ~printer: (fun x -> if x then "eligible" else "not eligible")
  in 
  let eq ?(nyi=false) (jscode : string) (expected : string) =
    (* this function will first assert the code is eligible for preprocessing.
       and evaluate the jscode and expected, and compare the result with that of 
       expected *)
    fun text_ctx ->
      (if nyi then todo "not implemented"
       else ());
      let es5env = Ljs.parse_es5_env (open_in "../envs/es5.env") "../envs/es5.env" in
      let s5code = desugar jscode in
      let s5expected = desugar expected in
      assert_equal true (eligible_for_unwrap_lambda s5code)
        ~printer: (fun x -> if x then "eligible" else "not eligible");
      let s5value = Ljs_eval.eval_expr (es5env (unwrap_lambda s5code)) desugar true in
      let expectedv = Ljs_eval.eval_expr (es5env s5expected) desugar true in
      match s5value, expectedv with
      | Ljs_eval.Answer(_,value,_,_), Ljs_eval.Answer(_,value2,_,_) ->
        assert_equal value2 value
          ~printer: (Ljs_values.pretty_value)
  in 
  let eligible (jscode : string) =
    eligible_test jscode true
  in 
  let not_eligible (jscode : string) =
    eligible_test jscode false
  in 
  "Test Preprocess" >:::
  [
    (eligible "function foo(a) {return a}
       foo(1)");


    (* function arity does not match, but it is fine for unwrapping lambda *)
    (eligible "function foo(a,b,c,d) {return a}
       foo(1);");
    
    (* use the function as constructor *)
    (not_eligible "function foo(){}
       var f = new foo()");

    (* the function has alias *)
    (not_eligible "function foo() {}
       var f = foo;
       var o = new f();");
    
    (* function is used as object property *)
    (not_eligible "function foo() {}
       var o = {'f' : foo};
       o.f()");

  ]  

let _ = 
  (* make sure the working directory is in src *)
  run_test_tt_main suite
