open Ljs
open Prelude
open Util
open Ljs_const_propagation

(* regression test for const folding *)

let test_const_propagation () =
  let cmp (from : string) (expected : string) =
      assert_equal const_propagation from expected;
      
  in
  begin
    cmp "let (x=1)
         let (y=x)
         let (z=y) {z}" 
        "1";

    cmp "let (x=prim('+',1,1))
         let (y=x)
         let (z=y) {z}" 
        "2";

    (* x should not be a const, no substitution should apply *)
    cmp "let (y={[]})
         let (x=func(s){y})
         let (y=1)
         x(y)"

        "let (y={[]})
         let (x=func(s){y})
         x(1)";

    cmp "let (x={[#extensible: false]}) x"
        "{[#extensible: false]}";

    cmp "{let (x = {[#extensible: false,]})
           {x; x; x;
            {let (y = x) {y;y;y}}}}"
        "{let (x = {[#extensible: false]})
           {x; x; x; {x; x; x}}}";

    cmp "let (x={[#extensible: false]})
         let (y={[#proto: x, #extensible: false]
                 'f1': {#value x, #writable false},
                 'f2': {#value x, #writable false}})
          y"

        "let (x={[#extensible: false]})
         {[#proto: x, #extensible: false]
          'f1': {#value x, #writable false},
          'f2': {#value x, #writable false}}";


    cmp "let (x={[#extensible: false]})
         let (y={[#proto: x, #extensible: false]
                 'f1': {#value x, #writable false},
                 'f2': {#value x, #writable false}})
            y[<#proto>]"
        "{[#extensible: false]}";

  end

let _ = 
  test_const_propagation ()
  
