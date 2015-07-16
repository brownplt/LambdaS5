open Prelude
open Util
open OUnit2
open Ljs_clean_assertion

let suite =
  let cmp before after = cmp before clean_assertion after in
  let no_change code = no_change code clean_assertion in
  "Test Type Infer" >:::
  [
    "simple number" >::
    (cmp "prim('typeof', 12)" "'number'");

    "simple object" >::
    (cmp "prim('typeof', {[]})" "'object'");

    "simple function object" >::
    (cmp "prim('typeof', {[#proto: null, #code: func(){1}]})" "'function'");

    "get id type from env" >::
    (cmp "let (x = {[]})
          prim('typeof', x)"
         "let (x = {[]}) 'object'"
     );

    "let shadow" >::
    (cmp
       "let (x = 1) let (x = {[]}) prim('typeof', x)"
       "let (x = 1) let (x = {[]}) 'object'");

    "function shadow" >::
    (no_change
      "let (x = 1) func(x, y) {prim('typeof', x)} (3,4)");

    "function shadow" >::
    (cmp
      "let (z = 1) func(x) {prim('typeof', z)} (3)"
      "let (z = 1) func(x) {'number'} (3)"
    );


    "get id from complicated exp" >::
    (cmp "let (x = {let (x1 = 1) let (x2 = {[]}) let (x3 = {[#code: func(){1}]}) {x1;x2;x3}})
          prim('typeof', x)"
         "let (x = {let (x1 = 1) let (x2 = {[]}) let (x3 = {[#code: func(){1}]}) {x1;x2;x3}})
          'function'"
    );

    "undecidable type" >::
    (no_change "let (x = {if (f) {1} else {'1'}}) prim('typeof', x)");

    "undecidable type" >::
    (no_change "let (x = {let (y={[]}) y['fld'=1]}) prim('typeof', x)");

    "mutation makes type undecidable" >::
    (no_change "let (x = 1) {x := {[]}; prim('typeof', x)}");

    "test %ToObject applied to obj" >::
    (cmp
       "let (x = {[]}) {%ToObject(x)}"
       "let (x = {[]}) {x}"
    );

    "test %ToObject applied to function" >::
    (cmp
       "let (x = {[#code: func(x) {x}]}) %ToObject(x)"
       "let (x = {[#code: func(x) {x}]}) x"
    );

    "test other" >::
    (no_change "let (x = 1) %ToObject(x)");

    "%PropAccessorCheck" >::
    (no_change "prim('typeof', %PropAccessorCheck(nan))");

    "%PropAccessorCheck" >::
    (no_change "prim('typeof', %PropAccessorCheck(%this['NaN']))");

  ]

let _ =
  run_test_tt_main suite
