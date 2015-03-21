open Prelude
open Util
open OUnit2
open Exp_util

(* tips: do everything in function test instead of in cmp *)
let exp_util_test = 
  let test_no_side_effect_prior_use (id : id) (code : string) (result : bool) = 
    let test test_ctxt = 
      assert_equal result (no_side_effect_prior_use id (parse code))
    in
    test
  in 
  "Test Exp Util" >:::
  [
    "test_no_side_effect_prior_use 1" >::
    (test_no_side_effect_prior_use
       "y"
       "{x(); y}"
       false);

    "test_no_side_effect_prior_use 2" >::    
    (test_no_side_effect_prior_use
       "x"
       "{y:=t; fobj:=x}"
       false);

    "test_no_side_effect_prior_use 3" >::    
    (test_no_side_effect_prior_use
       "x"
       "{undefined; fobj:=x}"
       true);

    "test_no_side_effect_prior_use 4" >::    
    (test_no_side_effect_prior_use
       "x"
       "{undefined; fobj:={y:=t; x}}"
       false);

    "test_no_side_effect_prior_use 5" >::    
    (test_no_side_effect_prior_use
       "x"
       "fobj := x"
       true);

    "test_no_side_effect_prior_use 6" >::    
    (test_no_side_effect_prior_use
       "x"
       "let (f = func(t){prim('print',t)})
          y:=x"
       true);
    
  ]

let _ =
  run_test_tt_main exp_util_test
