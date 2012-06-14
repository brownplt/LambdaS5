open Prelude
open Ljs_sym_values

let print_gc_stats = true

(* Each value and object has an extra boolean marker *)
type marked_store = (value * bool, (objlit * bool) * bool) sto

(* Everything in a store is initially marked false *)
let mstore_of_store (store : sto_type) : marked_store =
  let mark_false v = (v, false) in
  { vals = Store.map mark_false store.vals;
    objs = Store.map mark_false store.objs; }

(* Simply drops the markers. *)
let store_of_mstore (mstore : marked_store) : sto_type =
  { vals = Store.map fst mstore.vals;
    objs = Store.map fst mstore.objs; }

(* The root set is the *set* of all locs in the envs.
 * We'll represent it with a list with no duplicates. *)
let root_set envs = nub (List.rev_map snd (envs_bindings envs))
let env_root_set env = root_set (push_env env mt_envs)

let mark_true loc v sto = Store.update loc (v, true) sto

let rec mark_val vloc mstore : marked_store =
  let (v, marked) = Store.lookup vloc mstore.vals in
  if marked then mstore else (* already marked, so skip *)
  let mstore = { mstore with vals = mark_true vloc v mstore.vals } in
  match v with
  | ObjPtr oloc ->
      mark_obj oloc mstore
  | Closure (arg_ids, _, env) ->
      fold_left (flip mark_val) mstore (env_root_set env) (* TODO take arg_ids into account? *)
  | NewSym (id, olocs) ->
      fold_left (flip mark_obj) mstore olocs
  | _ -> mstore

and mark_obj oloc mstore =
  let (o, marked) = Store.lookup oloc mstore.objs in
  if marked then mstore else (* already marked, so skip *)
  let mstore = { mstore with objs = mark_true oloc o mstore.objs } in

  let fields_helper ofields mstore =
    (mark_props ofields.symps
      (mark_props ofields.conps
        (mark_attrs ofields.attrs mstore))) in

  match fst o with
  | ConObj ofields -> fields_helper ofields mstore
  | SymObj (ofields, locs) ->
      fold_left (flip mark_obj)
        (fields_helper ofields mstore)
        locs
  | NewSymObj locs -> fold_left (flip mark_obj) mstore locs

and mark_props props mstore =
  IdMap.fold
    (fun _ prop mstore -> match prop with
      | Data ({ value = vloc; }, _, _) -> mark_val vloc mstore 
      | Accessor ({ getter = gloc; setter = sloc; }, _, _) ->
        mark_val sloc (mark_val gloc mstore))
    props mstore

and mark_attrs attrs mstore =
  let opt_helper attr_opt mstore = match attr_opt with
  | None -> mstore
  | Some vloc -> mark_val vloc mstore
  in
  opt_helper attrs.code
    (mark_val attrs.proto
       (opt_helper attrs.primval mstore))

let mark (envs : env_stack) (store : sto_type) : marked_store =
  fold_left (flip mark_val) (mstore_of_store store) (root_set envs)

let sweep (mstore : marked_store) : sto_type =
  let is_marked _ (_, mkd) = mkd in
  store_of_mstore 
    { vals = Store.filter is_marked mstore.vals;
      objs = Store.filter is_marked mstore.objs; }

let garbage_collect (envs : env_stack) (store : sto_type) : sto_type =
  if print_gc_stats then
    let v = Store.cardinal store.vals in
    let o = Store.cardinal store.objs in
    let t = v + o in
    let start_time = Sys.time() in
    printf "-------------\n";
    printf "START GC\n";
    printf "Current time: %f secs\n" start_time;
    printf "Store size: %d (%d vals, %d objs)\n" t v o;
    print_newline();

    let new_store = sweep (mark envs store) in

    let v' = Store.cardinal new_store.vals in
    let o' = Store.cardinal new_store.objs in
    let t' = v' + o' in
    let end_time = Sys.time() in
    printf "END GC\n";
    printf "Current time: %f secs\n" end_time;
    printf "Store size: %d (%d vals, %d objs)\n" t' v' o';
    print_newline();
    printf "RESULTS\n";
    printf "Time taken: %f secs\n" (end_time -. start_time);
    printf "Items collected: %d (%d vals, %d objs)\n" (t - t') (v - v') (o - o');
    print_newline();

    new_store

  else
    sweep (mark envs store)
