open Ljs_clean_sequence
open Util
open OUnit2
open Ljs_clean_sequence

let clean_sequence_test =
  let cmp before after = cmp before clean_sequence after in
  let no_change code = no_change code clean_sequence in
  "Test Cleaning Sequence" >:::
    [
    "clean an expression that has no side effect" >::
    (cmp "{1;2}" "2");

    "clean an exp that has no side effect" >::
    (cmp "{{{2; 3}; 4}; 5}" "5");

    "clean an exp that has no side effect" >::
    (cmp "{let (x = 1) x}; 5" "5");

    "clean an exp that has no side effect" >::
    (cmp "{undefined; 2}" "2");

    (* elimination can be only applied on e1. e2 may be the return value *)
    "clean sequence" >::
      (cmp "let (x = 1)
            {x;x;x;x;x}"
           "let (x=1)
            x");
            
    "break cuts the sequence">::
    (cmp
      "lable %ret : {
        break %ret 1;
        prim('print', 'unreachable');
        undefined;
       }"
       "lable %ret : {
         break %ret 1
         }");


    ]
