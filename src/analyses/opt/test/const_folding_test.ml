open Ljs
open Prelude
open Util
open Ljs_const_folding

(* regression test for const folding *)

let test_const_folding () =
  let cmp (from : string) (expected : string) =
      assert_equal const_folding from expected;
  in
  let const_obj = "{[#extensible: false] 
                    'field1': {#value 1, #writable false, #configurable false}}"
  in
  begin
    cmp "prim('+', 1, 2)" "3";

    cmp (const_obj ^ "['field1']") "1";
    cmp (const_obj ^ "['field2']") "undefined";

    cmp (const_obj ^ "[<#extensible>]") "false";
    cmp "{[]}[<#extensible>]" "true";

    cmp (const_obj ^ "['field1'<#writable>]") "false";
    cmp (const_obj ^ "['field1'<#configurable>]") "false";
                                         
    cmp "prim('pretty', 1)" "prim('pretty', 1)";

    (*
    cmp "if (func(x){1}) {1} else {2}" "2";
    cmp "if ({[]})"
     *)

    cmp "if (prim('+',1,2)) {1} else {2}" "1";

    cmp "let (x=1) prim('+', x, 1)" "let (x=1) prim('+', x, 1)";
    
    
            
  end

let _ = 
  test_const_folding ()
  
