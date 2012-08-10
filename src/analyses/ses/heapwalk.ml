open Prelude
open Ljs_values

module Marshal = Marshal

module LocMap = Store.LocMap

type answer = Ljs_eval.answer

let save_answer (answer : answer) chan =
  Marshal.to_channel chan answer []

let load_answer chan : answer =
  Marshal.from_channel chan

type node =
  | ValueNode of value
  | ObjNode of Store.loc * objectv

let fold_heap (f : 'a -> node -> 'a) (init : 'a) store : 'a =
  let rec fold_value ans value =
    let ans = f ans (ValueNode value) in
    match value with
    | Closure (env, _, _) -> fold_env ans env
    | _ -> ans
  and fold_env ans env = ans
  and fold_attrs ans attrs =
    match attrs with
    | {code=code; proto=proto; extensible=_; klass=_; primval=primval} ->
      let attr_vals = [proto] @ list_of_option code @ list_of_option primval in
      List.fold_left fold_value ans attr_vals
  and fold_prop ans prop =
    match prop with
    | Data ({value=value; writable=_}, _, _) ->
      fold_value ans value
    | Accessor ({getter=getter; setter=setter}, _, _) ->
      fold_value (fold_value ans getter) setter
  and fold_props ans props =
    List.fold_left fold_prop ans (map snd (IdMap.bindings props))
  and fold_obj ans (loc, obj) =
    let ans = f ans (ObjNode (loc, obj)) in
    match obj with
    | (attrs, props) ->
      fold_props (fold_attrs ans attrs) props
  and fold_store ans (obj_store, val_store) =
    let ans = List.fold_left fold_obj ans (LocMap.bindings obj_store) in
    List.fold_left fold_value ans (LocMap.values val_store) in

  fold_store init store


let direct_reachables (obj_store, var_store) =
  (LocMap.values obj_store, LocMap.values var_store)


let reachables store =
  let f (objs, values) node = match node with
    | ValueNode value -> (objs, value :: values)
    | ObjNode (loc, obj) -> ((loc, obj) :: objs, values) in
  fold_heap f ([], []) store


let fold_heap_values f init store =
  fold_heap (fun ans node ->  match node with
    | ValueNode value -> f ans value
    | ObjNode _ -> ans)
    init store

let fold_heap_objs f init store =
  fold_heap (fun ans node -> match node with
    | ValueNode _ -> ans
    | ObjNode (loc, obj) -> f ans loc obj)
    init store


(********************************)

let is_frozen obj =
  let prop_is_frozen prop = match prop with
    | Data ({writable=false}, _, false) -> true
    | Accessor (_, _, false) -> true
    | _ -> false in
  let attrs_are_frozen attrs = match attrs with
  | {extensible=true} -> false
  | {extensible=false} -> true in
  match obj with
  | (attrs, props) ->
    attrs_are_frozen attrs && List.for_all prop_is_frozen (IdMap.values props)

let find_unfrozen_objs store =
  let f objs loc obj =
    if is_frozen obj
    then objs
    else (loc, obj) :: objs in
  fold_heap_objs f [] store

let find_frozen_objs store =
  let f objs loc obj =
    if is_frozen obj
    then (loc, obj) :: objs
    else objs in
  fold_heap_objs f [] store

let ses_check init_ans ses_ans =
  let Ljs_eval.Answer (init_exps, init_value, init_envs,
                       (init_obj_store, init_var_store)) = init_ans in
  let Ljs_eval.Answer (ses_exps, ses_value, ses_envs,
                       (ses_obj_store, ses_var_store)) = ses_ans in
  let init_env = last init_envs in
  let ses_env = last ses_envs in
  let env_changes =
    let changed id loc =
      if IdMap.mem id init_env
      then loc <> IdMap.find id init_env
      else true in
    IdMap.filter changed ses_env in
  let accessible_primordials =
    LocMap.filter (fun loc _ -> LocMap.mem loc init_obj_store) ses_obj_store in
  let unfrozen_accessible_primordials =
    LocMap.from_list (find_unfrozen_objs (accessible_primordials, LocMap.empty)) in
  print_endline "[[[ENVIRONMENT CHANGES (new or modified ids in ses)]]]";
  print_endline (Ljs_pretty_value.string_of_env env_changes);
  print_endline "[[[UNFROZEN ACCESSIBLE PRIMORDIALS (these are bad)]]]";
  Ljs_pretty_value.print_objects (unfrozen_accessible_primordials, LocMap.empty)

(*
type env_diff = {
  introduced: env; (* things in new but not in old *)
  deleted: env; (* things in old but not in new *)
  modified: env; (* things in both old and new, but modified *)
  unchanged: env (* things the same in old and new *)
}

type store_diff = {
  introduced: store; (* things in new but not in old *)
  deleted: store; (* things in old but not in new *)
  modified: store; (* things in both old and new, but modified *)
  unchanged: store (* things the same in old and new *)
}

let take_env_diff (new_env: env) (old_env: env) : env_diff =
  let introduced id _ = not (IdMap.mem id old_env) in
  let deleted id _ = not (IdMap.mem id new_env) in
  let modified id _ = IdMap.mem id old_env &&
    IdMap.find id old_env <> IdMap.find id new_env in
  let unchanged id _ = IdMap.mem id old_env &&
    IdMap.find id old_env = IdMap.find id new_env in
  {introduced = IdMap.filter introduced new_env;
   deleted = IdMap.filter deleted old_env;
   modified = IdMap.filter modified new_env;
   unchanged = IdMap.filter unchanged new_env}
*)
(*
let take_store_diff new_store old_store : store_diff =
  let introduced id _ = !(LocMap.mem id old_store) in
  let deleted id _ = !(LocMap.mem id new_store) in
  let modified id _ = LocMap.mem id old_store &&
    LocMap.find id old_store <> LocMap.find id new_store in
  let unchanged id _ = LocMap.mem id old_store &&
    LocMap.find id old_store = LocMap.find id new_store in
  {introduced = LocMap.filter introduced new_store;
   deleted = LocMap.filter deleted old_store;
   modified = LocMap.filter modified new_store;
   unchanged = LocMap.filter unchanged new_store}
*)
(*
let take_answer_diff (new_ans : answer) (old_ans : answer) : answer =
  let env_diff new_env old_env =
    let changed id loc =
      if IdMap.mem id old_env
      then loc <> IdMap.find id old_env
      else true in
    IdMap.filter changed new_env in
  let store_diff new_store old_store =
    let changed loc v =
      if LocMap.mem loc old_store
      then v <> LocMap.find loc old_store
      else true in
    LocMap.filter changed new_store in
  match new_ans with
  | Ljs_eval.Answer (exps, value, new_env, (new_obj_store, new_var_store)) ->
    match old_ans with
    | Ljs_eval.Answer (_, _, old_env, (old_obj_store, old_var_store)) ->
      let env = [env_diff (last new_env) (last old_env)] in
      let obj_store = store_diff new_obj_store old_obj_store in
      let var_store = store_diff new_var_store old_var_store in
      Ljs_eval.Answer (exps, value, env, (obj_store, var_store))
*)
