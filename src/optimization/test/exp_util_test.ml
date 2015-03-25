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
  let test_multiple_usages (id : id) (code : string) (result : bool) = 
    let test test_ctxt = 
      assert_equal result (multiple_usages id (parse code))
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

    "test_no_side_effect_prior_use 7" >::
    (test_no_side_effect_prior_use
       "px"
       "let (py = %ToPrimitiveHint(r, 'number'))
        rest(px, py)"
       false
     );

   "test_no_side_effect_prior_use 7" >::
    (test_no_side_effect_prior_use
       "py"
       "let (px = %ToPrimitiveHint(l, 'number'))
        rest(px, py)"
       false
     );
    
    "test mutliple usages" >::
    (test_multiple_usages
       "%context0"
       "prim('!', prim('stx=', %instanceof(%context0['e' , {[#proto: null,
                                                      #class: 'Object',
                                                      #extensible: true,]}],
                                    %context0['TypeError' , {[#proto: null,
                                                              #class: 'Object',
                                                              #extensible: true,]}]) , true))"
       (*"f(%context0['e'], %context0['TypeError'])"*)
       true);
    
  ]

let _ =
  run_test_tt_main exp_util_test
