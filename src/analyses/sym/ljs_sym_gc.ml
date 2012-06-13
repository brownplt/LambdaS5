open Prelude
open Ljs_sym_values

(* Each value and object has an extra boolean marker *)
type marked_store = (value * bool, (objlit * bool) * bool) sto

let init_mstore (store : sto_type) : marked_store =
  let mark_false v = (v, false) in
  { vals = Store.map mark_false store.vals;
    objs = Store.map mark_false store.objs; }

(* The root set is the *set* of all locs in the env.
 * We'll represent it with a list with no duplicates. *)
let root_set env = nub (map snd (env_bindings env))

let mark_true loc v sto = Store.update loc (v, true) sto

let flip f = (fun a b -> f b a)

let rec mark_val vloc mstore : marked_store =
  let (v, marked) = Store.lookup vloc mstore.vals in
  if marked then mstore else (* already marked, so skip *)
  let mstore = { mstore with vals = mark_true vloc v mstore.vals } in
  match v with
  | ObjPtr oloc ->
      mark_obj oloc mstore
  | Closure (arg_ids, _, env) ->
      fold_left (flip mark_val) mstore (root_set env) (* TODO take arg_ids into account? *)
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
      fold_left (flip mark_obj) (fields_helper ofields mstore) locs
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

let mark (env : env) (store : sto_type) : marked_store =
  let root_locs = root_set env in
  fold_left (flip mark_val) (init_mstore store) root_locs

(*let sweep mstore *) (* TODO *)

(*let garbage_collect (env : env) (store : sto_type) : sto_type = sweep (mark env store)*)
