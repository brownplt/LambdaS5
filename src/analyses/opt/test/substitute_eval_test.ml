open Ljs_substitute_eval
open Ljs_syntax
open Util
open Prelude

(* test cases for substitute evaluation *)

(* test multiple usage *)
let multiple_usages_test_true = [
"{x;x}";

"let (y = x)
 let (z = x) x";

"rec (z=func(y){prim('+',x,x)}) z";
"let (z=func(y){prim('+',x,x)}) z";

"let (s={[#proto:x]}) x";

"let (s={[#primval:x]}) x";

"let (s={[] 'field1': {#value x,#writable true}}) x";

"let (s={[]}) s[x = x]";

"app(x,x,x)";

"x(x)";

]

let multiple_usages_test_false = [
"1";
"x";
"let (y=x)
 let (x=2) x";
"let (y=x)
 rec (x=func(s){s}) x";
"rec (z=func(x){prim('+',x,x)}) z";
"let (z=func(x){prim('+',x,x)}) z";
]

let test_multiple_usages (prog : string) (expected : bool) =
  let ljs = parse prog in
  if ((multiple_usages "x" ljs) = expected) then succeed()
  else fail prog

let can_drop_test_true = [
]

let can_drop_test_false = [
  "let (x = {[#extensible: true]})
   let (y = x) y";

  "let (x = {[#extensible: false]})
   {x; x}";

  "let (x=1)
   x := 2";
   
]

let test_substitute_const () =
  let optfunc (e : exp) : exp =
    let result, modified = substitute_const e in result
  in
  let cmp (from : string) (expected : string) =
    assert_equal optfunc from expected
  in
  begin
     cmp "let (x=1) let (y = x) y" 
             "1.";
     cmp "let (x=1) {x;x}" 
             "{1.;1.}";

     (* x is not a constant *)
     cmp "let (x={[]}) {x}" 
             "let (x={[]}) {x}";

     cmp "let (x=1) {x; x:=1}" 
             "let (x=1) {x; x:=1}";

     cmp "let (x=1)
              let (y=x)
              let (x=func(t){x}) x(y)"
             "func(t){1}(1)";

     cmp "let (x=1)
              let (y=x) {
                x := 2;
                let (x=func(t){x}) x(y)
              }"
             "let (x=1)
              let (y=x) {
                x := 2;
                let (x=func(t){x}) x(y)
              }";

     (* const object used once *)
     cmp "let (x={[#extensible: false]}) x"
             "{[#extensible: false]}";

     (* const object used once but mutation occurs *)
     cmp "let (x={[#extensible: false]}) {x:=1;x}"
             "let (x={[#extensible: false]}) {x:=1;x}";

     (* non-scalar used twice *)
     cmp "let (x={[#extensible: false]}) {x;x}"
             "let (x={[#extensible: false]}) {x;x}";

     (* binding has the same name as x *)
     cmp "let (x=1)
              let (f=func(x) {x;x;x}) {
              f(x); f(x)}"
             "let (f=func(x) {x;x;x}) {
              f(1); f(1)}";

     cmp "let (x=1)
              let (f=func(y) {y;x;x}) {
              f(x); f(x)}"
             "let (f=func(y) {y;1;1}) {
              f(1); f(1)}";

     cmp "let (x = {[#extensible: true]})
          let (y = x) y"
         "let (x = {[#extensible: true]})
          let (y = x) y";

     cmp "let (x = {[#extensible: false]})
          let (y = x) y"
         "{[#extensible: false]}";

     cmp "let (x = {[#extensible: false]})
          let (y = 1) y := x"

         "let (y = 1)
          y := {[#extensible: false]}";
  

  end
    

let _ = 
  List.map (fun (p) -> test_multiple_usages p true) multiple_usages_test_true;
  List.map (fun (p) -> test_multiple_usages p false) multiple_usages_test_false;
  test_substitute_const()
  
