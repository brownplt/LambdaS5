open Prelude
open Ljs_sym_gc
open Ljs_sym_values
open OUnit

let vloc1, vals1 = Store.alloc (String "v1") Store.empty
let vloc2, vals2 = Store.alloc (String "v2") vals1
let vloc3, vals3 = Store.alloc Undefined vals2

let mt_obj k = {
  attrs = { code = None; proto = vloc1; extensible = BTrue;
            klass = SString k; primval = None; };
  conps = IdMap.empty; symps = IdMap.empty }

let oloc1, objs1 = Store.alloc (ConObj (mt_obj "co1")) Store.empty
let vloc4, vals4 = Store.alloc (ObjPtr oloc1) vals3

let oloc2, objs2 = Store.alloc (SymObj (mt_obj "so2", [])) objs1
let vloc5, vals5 = Store.alloc (ObjPtr oloc2) vals4

let oloc3, objs3 = Store.alloc (SymObj (mt_obj "so3", [oloc1; oloc2])) objs2
let vloc6, vals6 = Store.alloc (ObjPtr oloc3) vals5

let oloc4, objs4 = Store.alloc (NewSymObj [oloc3]) objs3
let vloc7, vals7 = Store.alloc (ObjPtr oloc4) vals6

let vloc8, vals8 = Store.alloc (NewSym ("v8", [oloc1])) vals7

let env1 = env_add "v1" vloc1 mt_env
let env2 = env_add "v2" vloc2 env1
let env3 = env_add "v3" vloc3 env2 
let env3' = env_add "v3" vloc1 env3 (* shadowing *)
let env4 = env_add "ptr4" vloc4 env3
let env5 = env_add "ptr5" vloc5 env4
let env6 = env_add "ptr6" vloc6 env5 
let env7 = env_add "ptr7" vloc7 env6
let env8 = env_add "v8" vloc8 env7

let marked_locs mstore =
  let marked, unmarked =
    Store.partition (fun _ (_, mkd) -> mkd) mstore.vals in (* TODO objects too *)
  let locs_of s = map fst (Store.bindings s) in
  (locs_of marked, locs_of unmarked)

let sto vs os = { vals = vs; objs = os }
let mt = Store.empty

let tests = "All GC tests" >::: [

  "Mark tests" >::: [  
    (* Basic checks for marking vals *)
    ("1" >:: fun () -> assert_equal
                         (marked_locs (mark_val
                                        (init_mstore (sto vals1 mt))
                                        vloc1))
                         ([vloc1], []));

    ("2" >:: fun () -> assert_equal
                         (marked_locs (mark_val
                                        (init_mstore (sto vals2 mt))
                                        vloc1))
                         ([vloc1], [vloc2]));
  ];

]

(*  assert_eq (marked_locs (mark_val vloc1*)
(*                            (mark_val vloc2) (init_mstore (sto vals2 mt)))))*)
(*            ([vloc1, vloc2], []);*)
(*] in*)
let _ = run_test_tt_main tests
