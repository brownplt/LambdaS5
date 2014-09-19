open Prelude
open Util
open OUnit2
open Ljs_prim_propagation

let suite = 
  let cmp before after = cmp before prim_propagation after in
  "Test Prim Propagation" >:::
    ["simple 1" >::
       (cmp "let (a = 1)
             let (b = a)
             b"
            "let (a = 1)
             let (b = 1)
             1");
    ]

let _ =
  run_test_tt_main suite
