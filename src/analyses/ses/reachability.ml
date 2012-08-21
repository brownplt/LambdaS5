open Prelude
open Ljs_values

module LocSet = Store.LocSet
module LocMap = Store.LocMap


type attr_type = Code | Proto | PrimVal

type prop_attr_type = Value | Getter | Setter

type node =
  | IdNode of id
  | VarNode of Store.loc * value
  | ObjNode of Store.loc * objectv
  | PropNode of id
  | AttrNode of attr_type
  | PropAttrNode of prop_attr_type
  | ClosureNode of env * id list * Ljs_syntax.exp


let string_of_attr_type attr_type = match attr_type with
  | Code -> "code"
  | Proto -> "proto"
  | PrimVal -> "primval"

let string_of_prop_attr_type attr_type = match attr_type with
  | Value -> "value"
  | Getter -> "getter"
  | Setter -> "setter"


type reachability_graph = node list list LocMap.t

type traversal_filter = {
  traverse_hidden_props : bool;
  traverse_closures: bool;
  primordials: LocSet.t
}

let make_reachability_graph store env filter : reachability_graph =

  let insert path loc map =
    if LocMap.mem loc map
    then LocMap.add loc (path :: LocMap.find loc map) map
    else LocMap.add loc [path] map in

  let rec walk_value path value =   
    match value with
    | Closure (env, args, exp) ->
      if filter.traverse_closures
      then walk_env (ClosureNode(env, args, exp) :: path) env
      else identity
    | ObjLoc loc -> insert path loc
    | _ -> identity

  and walk_maybe_value path mv =
    match mv with
    | None -> identity
    | Some v -> walk_value path v

  and walk_env path env =
    let insert_binding (id, loc) =
      insert (IdNode id :: path) loc in
    compose (List.map insert_binding (IdMap.bindings env))

  and walk_attrs path attrs =
    match attrs with
    | {code=code; proto=proto; extensible=_; klass=_; primval=primval} ->
      compose [walk_value (AttrNode Proto :: path) proto;
               walk_maybe_value (AttrNode Code :: path) code;
               walk_maybe_value (AttrNode PrimVal :: path) primval]

  and walk_prop path (prop_name, prop) =
    if not filter.traverse_hidden_props && prop_name = "ident:4___"
    then identity
    else let path = PropNode prop_name :: path in
         match prop with
         | Data ({value=value; writable=_}, _, _) ->
           walk_value (PropAttrNode Value :: path) value
         | Accessor ({getter=getter; setter=setter}, _, _) ->
           compose [walk_value (PropAttrNode Getter :: path) getter;
                    walk_value (PropAttrNode Setter :: path) setter]

  and walk_props path props =
    compose (List.map (walk_prop path) (IdMap.bindings props))

  and walk_obj_binding path (loc, obj) =
    let path = ObjNode (loc, obj) :: path in
    match obj with
    | (attrs, props) ->
      compose [walk_props path props;
               walk_attrs path attrs] in

  let walk_var_binding path (loc, value) =
    let path = VarNode (loc, value) :: path in
    walk_value path value in

  let walk_store path (obj_store, var_store) =
    compose (List.map (walk_obj_binding path) (LocMap.bindings obj_store)
             @ List.map (walk_var_binding path) (LocMap.bindings var_store)) in

  let size reachables =
    List.fold_left (+) 0 (List.map List.length (LocMap.values reachables)) in

  let rec fix_point reachables locs =
    match store with
    | (obj_store, var_store) ->
      let unexplored_store =
        let unexplored loc _ = LocSet.mem loc locs in
        (LocMap.filter unexplored obj_store,
         LocMap.filter unexplored var_store) in
      let reachables' = walk_store [] unexplored_store reachables in
      let locs' =
        let is_new loc = not (LocMap.mem loc reachables) in
        LocSet.from_list (List.filter is_new (LocMap.keys reachables')) in
      if size reachables = size reachables'
      then reachables'
      else fix_point reachables' locs' in

  let direct_reachables = walk_env [] env LocMap.empty in
  fix_point direct_reachables (LocSet.from_list (LocMap.keys direct_reachables))
