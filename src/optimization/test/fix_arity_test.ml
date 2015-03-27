open Prelude
open Util
open OUnit2
open Ljs_fix_arity


let suite =
  let cmp before after = cmp before fix_arity after in
  let no_change code = no_change code fix_arity in
  "Test fixing arity" >:::
  [
    "getter's arity should not change!" >::
    (no_change
      "{[] 'foo': {#getter func(%this,%args){1},
                   #setter undefined}}");

    "clean args" >::
    (cmp
      "func(%this, %args) { 1 }"
      "func(%this) {1}");

    "get formal arguments from desugared pattern" >::
    (cmp
      "func(%this, %args) {
         let (%context = {let (a=%args['0'])
                          let (b=%args['1'])
                          let (c=%args['2'])
                            {[]}})
             undefined
       }"
      "func(%this, a, b, c) {
         let (%context = {[]})
             undefined
       }");

    "get 0 arguments">::
    (cmp
      "func(%this, %args) {
        let (%context = {[]})
          undefined}"
      "func(%this) {
        let (%context = {[]})
          undefined}");

    "get formal arguments even if other expressions occur before the bindings" >::
    (cmp
      "func(%this, %args) {
         undefined;
         undefined;
         let (%context = {let (a=%args['0'])
                          let (b=%args['1'])
                          let (c=%args['2'])
                            {[]}})
             undefined}"
      "func(%this, a, b, c) {
         undefined;
         undefined;
         let (%context = {[]})
             undefined}");

    "clean again should not change the code" >::
    (no_change
      "func(%this, x, y) {
           prim('+', x, y)
       }");
    
    "clean %args will also clean all expressions related to %args" >::
    (cmp
      "func(%this, %args) {
        %args[delete '%new'];
        undefined
       }"
      "func(%this) {
        undefined
       }");

    (* patterns is that %args[delete '%new'] always presents. Otherwise leaves
       the function body untouched.
    *)
    "clean %args will also clean all expressions related to %args 2" >::
    (cmp
      "func(%this, %args) {
        %args[delete '%new'];
        let (%context = {[]
                         'arguments' : {#value %args, #writable true}})
          undefined
       }"
      "func(%this) {
        let (%context = {[]})
          undefined
       }");

  ]

let _ =
  run_test_tt_main suite
