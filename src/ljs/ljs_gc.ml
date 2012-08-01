open Prelude
open Ljs_values

module LocSet = Store.LocSet

let unions sets = List.fold_left LocSet.union LocSet.empty sets

let locs_of_env env =
  List.fold_left (flip LocSet.add) LocSet.empty (map snd (IdMap.bindings env))

let locs_of_value value = match value with
  | ObjLoc loc -> LocSet.singleton loc
  | Closure (env, _, _) -> locs_of_env env
  | _ -> LocSet.empty

let option_to_list opt = match opt with
  | None -> []
  | Some x -> [x]

let locs_of_obj (attrs, prop_map) =
  let vals_of_attrs {code=code; proto=proto; extensible=_;
                     klass=_; primval=primval} =
    [proto] @ (option_to_list code) @ (option_to_list primval) in
  let vals_of_prop prop = match prop with
    | Data ({value=value; writable=_}, _, _) ->
      [value]
    | Accessor ({getter=getter; setter=setter}, _, _) ->
      [getter; setter] in
  let vals_of_props prop_map =
    List.concat (map vals_of_prop (map snd (IdMap.bindings prop_map))) in
  let locs_of_value value = match value with
    | ObjLoc loc -> LocSet.singleton loc
    | _ -> LocSet.empty in
  unions (map locs_of_value (vals_of_attrs attrs @ vals_of_props prop_map))

let collect_garbage store root_set =
  match store with
  | (obj_store, val_store) ->
    let next_reachables loc =
      let val_locs = match get_maybe_var store loc with
        | None -> LocSet.empty
        | Some v -> locs_of_value v in
      let obj_locs = match get_maybe_obj store loc with
        | None -> LocSet.empty
        | Some obj -> locs_of_obj obj in
      LocSet.union obj_locs val_locs in
    let rec fix_point gen set =
      let set' = unions (set :: map gen (LocSet.elements set)) in
      if LocSet.equal set set'
      then set
      else fix_point gen set' in
    let reachables = fix_point next_reachables root_set in
    let reachable loc _ = LocSet.mem loc reachables in
    (Store.filter reachable obj_store, Store.filter reachable val_store)
