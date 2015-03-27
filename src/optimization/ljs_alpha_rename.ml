open Prelude
open Ljs_syntax
open Ljs_opt

(* given a lambda definition, and a set of potential conflict ids,
   alpha rename the lambda formal arguments to be distinguishing from
   the given ids set.
*)

let is_empty_inter s1 s2 =
  IdSet.is_empty (IdSet.inter s1 s2)

(* env is used for name replacement: old name => new name *)
type env = id IdMap.t

let env_lookup id env : id = 
  IdMap.find id env
let env_mem id env = IdMap.mem id env
let env_drop id env = IdMap.filter (fun x _ -> not (x = id)) env
let env_extend k v env = IdMap.add k v env
let rec build_env oldnames newnames env =
  match oldnames, newnames with
  | [], [] -> env
  | hd1 :: tl1, hd2 :: tl2 ->
    build_env tl1 tl2 (env_extend hd1 hd2 env)
  | _ -> failwith "build env failed: arity mismatch"
  
(* renaming strategy: ?*numeric => ?*(numeric+1) *)
(* identifier always has non-numeric + numeric as its name *)
let split_number (name : id) : (string * int) option =
  if Str.string_match (Str.regexp "\\(.*[^0-9]\\)\\([0-9]+\\)$") name 0 then
    let alphabet = Str.matched_group 1 name in
    let num = Str.matched_group 2 name in
    Some (alphabet, int_of_string num)
  else
    None

(* give an old name, return a fresh name as well a new space *)
let rec fresh_name (name : id) (space : IdSet.t) : id * IdSet.t =
  if not (IdSet.mem name space) then
    name, IdSet.add name space
  else
    match split_number name with
    | None -> fresh_name (name ^ "0") space
    | Some (alphabet, num) ->
      fresh_name (alphabet ^ (string_of_int (num + 1))) space

let rec make_new_name (xs : id list) (namespace : IdSet.t) : id list * IdSet.t =
  (* give a list of id, for each create a new one if necessary *)
  match xs with
  | [] -> [], namespace
  | hd :: tl ->
    if IdSet.mem hd namespace then (* name exists *)
      let new_name, new_namespace = fresh_name hd namespace in
      let _ = assert (not (IdSet.mem new_name namespace)) in
      let new_tl, new_namespace = make_new_name tl new_namespace in
      new_name :: new_tl, new_namespace
    else
      let new_namespace = IdSet.add hd namespace in
      let new_tl, new_namespace = make_new_name tl new_namespace in
      hd :: new_tl, new_namespace

let alpha_rename (func : exp) (namespace : IdSet.t) : exp =
  let rec resolve (exp : exp) (env : env) (namespace : IdSet.t) : exp =
    let resolve_helper e = resolve e env namespace in
    match exp with
    | Id (p, id) when env_mem id env ->
      Id (p, IdMap.find id env)
    | SetBang (p, x, v) when env_mem x env ->
      SetBang (p, env_lookup x env, resolve_helper v)
    (*| Let (p, x, xv, body) when env_mem x env ->
      (* old name is rebound, so just leave it along *)
      let new_xv = resolve xv env namespace in
      let new_env = env_drop x env in
      let new_body = resolve body new_env namespace in
      Let (p, x, new_xv, new_body)*)
    | Let (p, x, xv, body) when IdSet.mem x namespace ->
      let new_xv = resolve xv env namespace in
      let new_x, new_namespace = fresh_name x namespace in
      let new_env = env_extend x new_x env in
      let new_body = resolve body new_env new_namespace in
      Let (p, new_x, new_xv, new_body)
    (*| Rec (p, x, xv, body) when env_mem x env ->
      (* old name is rebound, so just leave it along *)
      (* the x in xv is bound to a new one, not the one we want to replace *)
      let new_env = env_drop x env in
      let new_xv = resolve xv new_env namespace in
      let new_body = resolve body new_env namespace in
      Rec (p, x, new_xv, new_body) *)
    | Rec (p, x, xv, body) when IdSet.mem x namespace ->
      let new_x, new_namespace = fresh_name x namespace in
      let new_env = env_extend x new_x env in
      let new_xv = resolve xv new_env new_namespace in
      let new_body = resolve body new_env new_namespace in
      Rec (p, new_x, new_xv, new_body)
    | Lambda (p, xs, body) ->
      (* rename xs in body to avoid conflict with namespace *)
      let new_ids, new_namespace = make_new_name xs namespace in
      let new_env = build_env xs new_ids env in
      Lambda (p, new_ids, resolve body new_env new_namespace)
    | _ -> optimize resolve_helper exp
  in
  resolve func IdMap.empty namespace
