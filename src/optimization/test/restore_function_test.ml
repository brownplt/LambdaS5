open Prelude
open Util
open OUnit2
open Ljs_restore_function
open Sys

let jsparser_path = "../tests/jsparser.sh"

let desugar (s : string) : Ljs_syntax.exp =
  try
    Ljs_desugar.parse_and_desugar jsparser_path s
  with Ljs_values.PrimErr (t, v) -> 
    failwith ("Error while desugaring: " ^ Ljs_values.pretty_value v ^ "\n")
  

let suite = 
  (* eval to the same value *)
  let eq ?(nyi=false) (s5code : string) (s5expected : string) =
    (* this function will first assert the code is eligible for restoreing.
       and evaluate the s5code and expected, and compare the result with that of 
       expected *)
    fun text_ctx ->
      (if nyi then todo "not implemented"
       else ());
      let es5env = Ljs.parse_es5_env (open_in "../envs/es5.env") "../envs/es5.env" in
      let s5value = Ljs_eval.eval_expr (restore_function (es5env (parse s5code))) desugar true in
      let expectedv = Ljs_eval.eval_expr (es5env (parse s5expected)) desugar true in
      match s5value, expectedv with
      | Ljs_eval.Answer(_,value,_,_), Ljs_eval.Answer(_,value2,_,_) ->
        assert_equal value2 value
          ~printer: (Ljs_values.pretty_value)
  in 
  let cmp before after = cmp before restore_function after in
  let no_change code = no_change code restore_function in

  (*NOTE: use %this, rather than 'this' in the test case! *)
  "Test restore function" >:::
  [
    "restore object 1" >::
    (cmp
       "let (prototype={[#proto: %ObjectProto]})
           {[#code: func(%this, x, y, z) {x}]}"
       "func(%this, x, y, z){x}");

    "restore object 2" >::
    (cmp
      "let (prototype={[#proto: %ObjectProto]})
         let (extra = 1)
           {[#code: func(%this) {extra}]}"
      "let (extra=1)
         func(%this){extra}");

    "restore object 3" >::
    (no_change
      "let (prototype={[#proto: %ObjectProto]})
         let (extra = 1)
           {[]}");

    "restore in getter" >::
    (cmp
      "{[]
         'foo' : {#getter {let (p={[#proto: %ObjectProto]})
                            {[#code: func(%this){1}]}},
                  #setter {let (p={[#proto: %ObjectProto]})
                            {[#code: func(%this){1}]}}}}"
      "{[] 'foo' : {#getter func(%this){1},
                    #setter func(%this){1}}}");

    "dont restore this" >::
    (no_change
      "let (extra = 1)
        {[#code: func(%this) {extra}]}");
      
      
    "restore in assignment" >::
    (cmp
      "obj := {let (prototype={[#proto: %ObjectProto]})
           {[#code: func(%this, x, y, z) {x}]}}"
      "obj := func(%this, x, y, z) {x}");
  ]


let _ = 
  run_test_tt_main suite

