open Prelude
open Ljs_sym_gc
open Ljs_sym_values
open OUnit

let mt_id = IdMap.empty
let attrs k ploc =
  { code = None; proto = ploc; extensible = BTrue;
    klass = SString k; primval = None; }
let prop vloc =
  (Data ({ value = vloc; writable = BTrue }, BTrue, BTrue))

let locs_of s = map fst (Store.bindings s)

let locs get_one_store mstore =
  let marked, unmarked =
    Store.partition (fun _ (_, mkd) -> mkd) (get_one_store mstore) in
  (locs_of marked, locs_of unmarked)

let vlocs = locs (fun msto -> msto.vals)
let olocs = locs (fun msto -> msto.objs)

let sto vs os = mstore_of_store { vals = vs; objs = os }
let mt = Store.empty

let string_of_list = String.concat ", "
let string_of_locs locs = string_of_list (map Store.print_loc locs)

let sort = List.sort compare

let assert_equal_locs locs1 locs2 =
  assert_equal ~printer: string_of_locs
    (sort locs1) (sort locs2)

let assert_equal_locs_pair (l11, l12) (l21, l22) =
  assert_equal ~printer: (fun (l1, l2) ->
    "(marked: " ^ string_of_locs l1
    ^ ", unmarked: " ^ string_of_locs l2 ^ ")")
    (sort l11, sort l12) (sort l21, sort l22)

let vloc1, vals1 = Store.alloc (String "v1") Store.empty
let vloc2, vals2 = Store.alloc (String "v2") vals1
let vloc3, vals3 = Store.alloc Undefined vals2
let vloc4, vals4 = Store.alloc Null vals3

let basic_mark_tests = "Basic mark tests" >::: [
  ("basic1" >:: fun () ->
     assert_equal_locs_pair
       ([vloc1], [])
       (vlocs (mark_val vloc1
                 (sto vals1 mt))));
  ("basic2" >:: fun () ->
     assert_equal_locs_pair
       ([vloc1], [vloc2])
       (vlocs (mark_val vloc1
                 (sto vals2 mt))));
  ("basic3" >:: fun () ->
     assert_equal_locs_pair
       ([vloc1; vloc2], [])
       (vlocs (mark_val vloc1
                 (mark_val vloc2
                    (sto vals2 mt)))));
  ("basic4" >:: fun () ->
     assert_equal_locs_pair
       ([vloc1; vloc3], [vloc2])
       (vlocs (mark_val vloc3
                 (mark_val vloc1
                    (sto vals3 mt)))));
]

let oloc5, objs5 = Store.alloc
  (ConObj { attrs = attrs "co5" vloc1; conps = mt_id; symps = mt_id }, false)
  Store.empty
let ptrloc5, vals5 = Store.alloc (ObjPtr oloc5) vals1

let oloc6, objs6 = Store.alloc
  (ConObj { attrs = attrs "so5" vloc3;
    conps = IdMap.add "prop1" (prop vloc1) IdMap.empty;
    symps = IdMap.add "prop2" (prop vloc2) IdMap.empty; }, false)
  objs5
let ptrloc6, vals6 = Store.alloc (ObjPtr oloc6) vals4

let obj_ptr_mark_tests = "ObjPtr mark tests" >::: [
  ("ptr1" >:: fun () ->
     assert_equal_locs_pair
       ([oloc5], [])
       (olocs (mark_val ptrloc5
                 (sto vals5 objs5))));
  ("ptr2 - through props and proto" >:: fun () ->
     assert_equal_locs_pair
       ([vloc1; vloc2; vloc3; ptrloc6], [vloc4])
       (vlocs (mark_val ptrloc6
                 (sto vals6 objs6))));
]

let oloc7, objs7 = Store.alloc
  (SymObj ({ attrs = attrs "so3" vloc1; conps = mt_id; symps = mt_id },
          [oloc5; oloc6]), false)
  objs6
let ptrloc7, vals7 = Store.alloc (ObjPtr oloc7) vals4

let oloc8, objs8 = Store.alloc (NewSymObj [oloc5], false) objs6
let ptrloc8, vals8 = Store.alloc (ObjPtr oloc8) vals6

let ptrloc9, vals9 = Store.alloc (NewSym ("v8", [oloc6])) vals6

let sym_mark_tests = "Sym loc lists mark tests" >::: [
  (* Following sym loc lists *)
  ("sym1 - SymObj loc list" >:: fun () ->
     assert_equal_locs_pair
       ([oloc5; oloc6; oloc7], [])
       (olocs (mark_val ptrloc7
                 (sto vals7 objs7))));
  ("sym2 - NewSymObj loc list" >:: fun () ->
     assert_equal_locs_pair
       ([oloc5; oloc8], [oloc6])
       (olocs (mark_val ptrloc8
                 (sto vals8 objs8))));
  ("sym3 - NewSym loc list" >:: fun () ->
     assert_equal_locs_pair
       ([vloc1; vloc2; vloc3; ptrloc9], [vloc4; ptrloc6])
       (vlocs (mark_val ptrloc9
                 (sto vals9 objs8))));
]

let env1 = env_add "v1" vloc1 mt_envs
let env2 = env_add "v2" vloc2 env1
let env3 = env_add "v2" vloc3 env2
let env4 = env_add "v3" vloc1 env2

let root_set_tests = "Root set tests" >::: [
  ("root0" >:: fun () ->
     assert_equal_locs [] (root_set mt_envs));
  ("root1" >:: fun () ->
     assert_equal_locs [vloc1] (root_set env1));
  ("root2" >:: fun () ->
     assert_equal_locs [vloc1; vloc2] (root_set env2));
  ("root3 - shadowing" >:: fun () ->
     assert_equal_locs [vloc1; vloc2; vloc3] (root_set env3));
  ("root4 - dup locs" >:: fun () ->
     assert_equal_locs [vloc1; vloc2] (root_set env4));
]

let val_locs sto = locs_of sto.vals
let obj_locs sto = locs_of sto.objs

(* These assume the basic tests for mark passed *)
let sweep_tests = "Sweep tests" >::: [
  ("sweep1" >:: fun () ->
     assert_equal_locs []
       (val_locs (sweep (sto vals1 mt))));
  ("sweep2" >:: fun () ->
     assert_equal_locs [vloc1]
       (val_locs (sweep (mark_val vloc1 (sto vals1 mt)))));
  ("sweep3" >:: fun () ->
     assert_equal_locs [vloc1]
       (val_locs (sweep (mark_val vloc1 (sto vals2 mt)))));
  ("sweep4" >:: fun () ->
     assert_equal_locs [oloc6]
       (obj_locs (sweep (mark_val ptrloc6 (sto vals6 objs6)))));
]

let undef = Ljs_syntax.Undefined Pos.dummy
let cloc10, vals10 = Store.alloc (Closure ([], undef, cur_env env1)) vals1
let env11 = env_add "f" cloc10 env1
let vals11 = Store.update cloc10 (Closure ([], undef, cur_env env11)) vals10

(* These assume that root set tests passed *)
let closure_tests = "Closure tests" >::: [
  ("closure1" >:: fun () ->
     assert_equal_locs_pair
       ([vloc1; cloc10], [])
       (vlocs (mark_val cloc10
                 (sto vals10 mt))));
  ("closure2 - recursive" >:: fun () ->
     assert_equal_locs_pair
       ([vloc1; cloc10], [])
       (vlocs (mark_val cloc10
                 (sto vals11 mt))));
]

let tests = "All GC tests" >::: [
  basic_mark_tests;
  obj_ptr_mark_tests;
  sym_mark_tests;
  root_set_tests;
  sweep_tests;
  closure_tests;
]

let _ = run_test_tt_main tests
