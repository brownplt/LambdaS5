open Prelude
open Util
open OUnit2
open Ljs_alpha_rename

let suite =
  let rename (space : id list) before after =
    (* space: a list of id as the whole name space,
       before: code before renaming
       after: the expect code
    *)
    let idset = IdSet.from_list space in
    cmp before (fun exp -> alpha_rename exp idset) after in
  let no_change (space : id list) code =
    no_change code (rename space) in
  "Test Alpha renaming" >:::

  [(rename
      ["x"; "y"; "t"]
      "func(x) { x := t }"
      "func(x1) { x1 := t }");
   
   (rename
      ["x"; "y"; "t"]
      "func(x) {
         let (x = 2)
            t();
         x
       }"
      "func(x1) {
         let (x2 = 2)
            t();
         x1
       }");

   (rename
      ["x"; "y"; "t"]
      "func(x) {
         let (y = 2)
           t();
         x
       }"
      "func(x1) {
         let (y1 = 2)
           t();
         x1
       }");
  ]

let _ =
  run_test_tt_main suite
