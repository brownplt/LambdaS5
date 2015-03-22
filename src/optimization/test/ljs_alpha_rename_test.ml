open Prelude
open Util
open OUnit2
open Ljs_alpha_rename


let suite =
  let cmp (space : id list) before after =
    let space = IdSet.from_list space in
    cmp before (fun e -> alpha_rename e space) after in
  let no_change (space : id list) code = 
    let space = IdSet.from_list space in
    no_change code (fun e -> alpha_rename e space) in 
  let test_fresh (old_name : id) (space : id list) (expect_name : id) =
    fun _ ->
      let new_name, _ = fresh_name old_name (IdSet.from_list space) in
      assert_equal expect_name new_name
        ~printer: (fun s ->(sprintf "%s" s))
  in
  let test_rename_list (old_names : id list) (space : id list) (expect_names : id list) =
    fun _ ->
      let new_names, _ = make_new_name old_names (IdSet.from_list space) in
      assert_equal expect_names new_names
  in
  "Test Alpha renaming" >:::
  [
    "test fresh_name, no change" >::
    (test_fresh "name1" ["x"; "y"; "z"] "name1");

    "test fresh_name" >::
    (test_fresh "x" ["x"; "x0"; "x1"; "x2"] "x3");

    "test fresh_name" >::
    (test_fresh "%123var" ["%123var"] "%123var0");

    "not all list needs to rename" >::
    (test_rename_list
       ["x"; "y"; "z"] (* args *)
       ["y"; "z"; "t"] (* space *)
       ["x"; "y0"; "z0"] (* new names *)
    );

    "rename1" >::
    (cmp
       ["x"; "y"; "t"]
       "func(x) { x := t }"
       "func(x0) { x0 := t }");
    
    "rename when let rebinds" >::
    (cmp
       ["x"; "y"; "t"]
       "func(x) {
         let (x = 2)
            t();
         x
       }"
       "func(x0) {
         let (x1 = 2)
            t();
         x0
       }");
    
    "rebind names in the namespace 1" >::
    (cmp
       ["x"; "y"; "t"]
       "func(x) {
         let (y = 2)
           t();
         x
       }"
       "func(x0) {
         let (y0 = 2)
           t();
         x0
       }");
    
    "rebind names in the namespace 2" >::
    (cmp
       ["x"; "y"; "t"]
       "func(x) {
         let (y = 2)
         let (y = 3)
         let (y = 4)
           t();
         x
       }"
       "func(x0) {
         let (y0 = 2)
         let (y1 = 3)
         let (y2 = 4)
           t();
         x0
       }");

    "func in func" >::
    (cmp
      ["n1"; "n2"; "n3"]
      "func(n1, n2) {
        n1;
        func(n1, n2) {
          prim('+', n1, n3)
        }(n1, n2)
       }"
      "func(n4, n5) {
        n4;
        func(n6, n7) {
          prim('+', n6, n3)
        }(n4, n5)
       }");

    "rename let bindings" >::
    (cmp
       ["a"]
       "
       let (a = {[#proto: a]})
        prim('!', prim('stx=', %instanceof(a['e'],
                                           a['TypeError']),
                               true))
       "
       "
       let (a0 = {[#proto: a]})
        prim('!', prim('stx=', %instanceof(a0['e'],
                                           a0['TypeError']),
                               true))
       ");
    
  ]

let _ =
  run_test_tt_main suite

  
