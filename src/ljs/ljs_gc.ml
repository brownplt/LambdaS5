open Prelude
open Ljs_values

module LocSet = Store.LocSet

let locs_of_env env =
  LocSet.from_list (map snd (IdMap.bindings env))

let locs_of_value value = match value with
  | ObjLoc loc -> LocSet.singleton loc
  | Closure (env, _, _) -> locs_of_env env
  | _ -> LocSet.empty

let locs_of_obj (attrs, prop_map) =
  let vals_of_attrs {code=code; proto=proto; extensible=_;
                     klass=_; primval=primval} =
    [proto] @ (list_of_option code) @ (list_of_option primval) in
  let vals_of_prop prop = match prop with
    | Data ({value=value; writable=_}, _, _) ->
      [value]
    | Accessor ({getter=getter; setter=setter}, _, _) ->
      [getter; setter] in
  let vals_of_props prop_map =
    List.concat (map vals_of_prop (map snd (IdMap.bindings prop_map))) in
  LocSet.unions (map locs_of_value
                   (vals_of_attrs attrs @ vals_of_props prop_map))

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
    let reachables = LocSet.fix_point next_reachables root_set in
    let reachable loc _ = LocSet.mem loc reachables in
    (Store.filter reachable obj_store, Store.filter reachable val_store)
