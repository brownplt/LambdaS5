open Prelude
open Ljs_syntax
module EU = Exp_util

type env = exp IdMap.t

let ljs_str ljs =
  Ljs_pretty.exp ljs Format.str_formatter; Format.flush_str_formatter()

let debug_on = true

let dprint, dprint_string, dprint_ljs = Debug.make_debug_printer ~on:debug_on "env-clean"

let dprint_set set =
  dprint "set {%s}\n" (String.concat ", " (IdSet.to_list set))

let is_context_id id : bool =
  match id with
  | "%context"
  | "%global"
  | "%globalContext"
  | "%strictContext"
  | "%nonstrictContext" -> true
  | _ -> false

type bindings_t = exp IdMap.t

(* todo: make this a def point, just like let *)
let rec useless_def_point f args (unused_bindings : bindings_t) : bool =
  match f, args with
  | Id(_, "%defineOwnProperty"), [Id(_, "%global"); String(_, func_name); Object(_,_,_)] ->
    (* field of %global(global var) is not used *)
    IdMap.mem func_name unused_bindings
  | Id(_, "%defineNYIProperty"), [Id(_, proto); String(_, func_name)] ->
    (* proto is not used *)
    IdMap.mem proto unused_bindings
  | Id(_, "%define15Property"), [Id(_, obj); String(_, func_name);_] ->
    (* obj is not used *)
    (IdMap.mem obj unused_bindings)
  | Id(_, "%defineOwnProperty"), [Id(_, obj); String(_, func_name); _] ->
    (* obj is not used *)
    (IdMap.mem obj unused_bindings)
  | _ -> false

let useless_obj_set obj field unused_bindings : bool =
  match obj, field with
  | Id(_, "%global"), String(_, fld) ->
    (* always special case the obj field of %global, because it is actually a def point *)
    IdMap.mem fld unused_bindings
  | Id (_, o), String(_,_) ->
    (* in env, if the object is not used(directly or indirectly) in user code, we can clean it *)
    (* todo: side effect: unused_obj["hello" = {..prim('pretty', 1)}] *)
    IdMap.mem o unused_bindings
  | _ -> false

let rec mark_id_usage id (unused_bindings : bindings_t) : bindings_t =
  try
    let exp = IdMap.find id unused_bindings in
    let unused_bindings = IdMap.remove id unused_bindings in
    let ids = free_vars exp in
    IdSet.fold (fun elm old_set->
        mark_id_usage elm old_set
      ) ids unused_bindings
  with _ -> unused_bindings

let mark_ids_usage (ids : IdSet.t) (unused_bindings : bindings_t) : bindings_t =
  IdSet.fold (fun elm old_set ->
      mark_id_usage elm old_set)
    ids unused_bindings

(* eliminate unused ids in environment *)
let new_env_clean (exp : exp) : exp =
  let rec env_clean_rec (e : exp) (unused_bindings : bindings_t) : (exp * bindings_t) = 
    let rec handle_option (opt : exp option) unused_bindings: exp option * bindings_t = 
      match opt with
      | Some (e) -> 
        let new_e, unused_bindings = env_clean_rec e unused_bindings in
        Some (new_e), unused_bindings
      | None -> None, unused_bindings
    in 
    match e with
    | Null _ 
    | Undefined _
    | String (_,_)
    | Num (_,_)
    | True _
    | False _ -> e, unused_bindings
    | Id (_,id) ->
      (* if we are visiting an id like %StringProto, we need to visit the id's value add unused_bindings in that value *)
      let curr_unused_bindings = (mark_id_usage id unused_bindings) in
      (*printf "visit %s. current unused ids:\n%!" id;
      IdMap.iter (fun k v -> printf "%s, " k) curr_unused_bindings; printf "\n%!";*)
      e, curr_unused_bindings
    | Object (p, attrs, strprop) ->
      let primval, unused_bindings = handle_option attrs.primval unused_bindings in
      let code, unused_bindings = handle_option attrs.code unused_bindings in
      let proto, unused_bindings = handle_option attrs.proto unused_bindings in
      let new_attrs = { primval = primval; code = code;
                        proto = proto; klass = attrs.klass;
                        extensible = attrs.extensible } in
      let handle_prop (p : 'a) unused_bindings : ('a * bindings_t) = match p with
        | (s, Data(data, enum, config)) ->
          let value, unused_bindings = env_clean_rec data.value unused_bindings in
          (s, Data({value = value; writable = data.writable}, 
                   enum, config)), unused_bindings
        | (s, Accessor (acc, enum, config)) ->
          let getter, unused_bindings = env_clean_rec acc.getter unused_bindings in
          let setter, unused_bindings = env_clean_rec acc.setter unused_bindings in
          (s, Accessor ({getter = getter; setter = setter}, 
                        enum, config)), unused_bindings
      in 
      let rec handle_prop_list strprops unused_bindings = match strprops with
        | [] -> strprops, unused_bindings
        | fst :: rest ->
          let p, unused_bindings = handle_prop fst unused_bindings in
          let rest_p, rest_ids = handle_prop_list rest unused_bindings in
          p :: rest_p, rest_ids
      in 
      let prop_list, unused_bindings = handle_prop_list strprop unused_bindings in
      Object (p, new_attrs, prop_list), unused_bindings

    | GetAttr (p, pattr, obj, field) ->
      let o, unused_bindings = env_clean_rec obj unused_bindings in
      let fld, unused_bindings = env_clean_rec field unused_bindings in
      GetAttr (p, pattr, o, fld), unused_bindings

    | SetAttr (p, attr, obj, field, newval) -> 
      if useless_obj_set obj field unused_bindings then begin
        dprint "clean SetAttr: %s\n" (EU.ljs_str e);
        Undefined Pos.dummy, unused_bindings
      end else 
        let o, unused_bindings = env_clean_rec obj unused_bindings in
        let f, unused_bindings = env_clean_rec field unused_bindings in
        let v, unused_bindings = env_clean_rec newval unused_bindings in
        SetAttr (p, attr, o, f, v), unused_bindings

    | GetObjAttr (p, oattr, obj) ->
      let o, unused_bindings = env_clean_rec obj unused_bindings in
      GetObjAttr(p, oattr, o), unused_bindings

    | SetObjAttr (p, oattr, obj, attre) ->
      let o, unused_bindings = env_clean_rec obj unused_bindings in
      let attr, unused_bindings = env_clean_rec attre unused_bindings in
      SetObjAttr (p, oattr, o, attr), unused_bindings

    | GetField (p, obj, fld, args) ->
      let o, unused_bindings = env_clean_rec obj unused_bindings in
      let f, unused_bindings = env_clean_rec fld unused_bindings in
      let a, unused_bindings = env_clean_rec args unused_bindings in
      let unused_bindings = match obj, fld with
        | Id (_, "%context"), String (_, id) -> 
          (dprint "use point %s\n" id; IdMap.remove id unused_bindings)
        | _ -> unused_bindings
      in 
      GetField (p, o, f, a), unused_bindings

    | SetField (p, obj, fld, newval, args) ->
      if useless_obj_set obj fld unused_bindings then begin
        dprint "clean SetField: %s\n" (EU.ljs_str e);
        Undefined Pos.dummy, unused_bindings
      end 
      else
        let o, unused_bindings = env_clean_rec obj unused_bindings in
        let f, unused_bindings = env_clean_rec fld unused_bindings in
        let v, unused_bindings = env_clean_rec newval unused_bindings in
        let a, unused_bindings = env_clean_rec args unused_bindings in
        SetField (p, o, f, v, a), unused_bindings
        
    | DeleteField (p, obj, fld) ->
      let o, unused_bindings = env_clean_rec obj unused_bindings in
      let f, unused_bindings = env_clean_rec fld unused_bindings in
      DeleteField (p, o, f), unused_bindings

    | OwnFieldNames (p, obj) -> 
      let o, unused_bindings = env_clean_rec obj unused_bindings in
      OwnFieldNames (p, o), unused_bindings

    | SetBang (p, x, x_v) ->
      let x_v, unused_bindings = env_clean_rec x_v unused_bindings in
      let unused_bindings = IdMap.remove x unused_bindings in
      dprint "find usage point at SetBang %s\n" x;
      SetBang (p, x, x_v), unused_bindings

    | Op1 (p, op, e) ->
      let e, unused_bindings = env_clean_rec e unused_bindings in
      Op1 (p, op, e), unused_bindings

    | Op2 (p, op, e1, e2) ->
      let e1, unused_bindings = env_clean_rec e1 unused_bindings in
      let e2, unused_bindings = env_clean_rec e2 unused_bindings in
      Op2 (p, op, e1, e2), unused_bindings

    | If (p, cond, thn, els) -> (* more optimization in constant folding *)
      let cond, unused_bindings = env_clean_rec cond unused_bindings in
      let thn, unused_bindings = env_clean_rec thn unused_bindings in
      let els, unused_bindings = env_clean_rec els unused_bindings in
      If (p, cond, thn, els), unused_bindings

    | App (p, f, args) ->
      let is_global_accessor () : id option =  match f, args with
        | Id (_, "%definedGlobalAccessors"), [Id(_, ctx); String(_, global_var)] 
          when is_context_id ctx ->
          Some global_var
        | _ -> None
      in
      let unused_bindings = match is_global_accessor () with
        | Some (id) -> IdMap.remove id unused_bindings
        | None -> unused_bindings
      in 
      if useless_def_point f args unused_bindings then begin
        dprint "clean app: %s\n" (EU.ljs_str e);
        Undefined Pos.dummy, unused_bindings
      end else 
        let f, unused_bindings = env_clean_rec f unused_bindings in
        let rec handle_args args unused_bindings = match args with
          | [] -> args, unused_bindings
          | fst :: rest ->
            let v, new_ids = env_clean_rec fst unused_bindings in
            let rest_v, rest_ids = handle_args rest new_ids in
            v :: rest_v, rest_ids
        in 
        let args, unused_bindings = handle_args args unused_bindings in
        App (p, f, args), unused_bindings

    | Seq (p, e1, e2) ->
      (* todo: e1 may be a def point like defineOwnProperty, before entering
         e2, add e1's def into potential unused set *)
      let new_e2, e2_unused_bindings = env_clean_rec e2 unused_bindings in
      let new_e1, e1_unused_bindings = env_clean_rec e1 e2_unused_bindings in
      let e1_is_lambda = match new_e1 with Lambda (_,_,_) -> true | _ -> false in
      if e1_is_lambda || not (EU.has_side_effect new_e1) then
        new_e2, e2_unused_bindings
      else 
        Seq (p, new_e1, new_e2), e1_unused_bindings

    | Let (p, x, x_v, body) ->
      let potential_unused_bindings = IdMap.add x x_v unused_bindings in
      let new_body, body_unused_bindings = env_clean_rec body potential_unused_bindings in
      if IdMap.mem x body_unused_bindings then begin
        dprint "Clean Let(%s=..)\n" x;
        new_body, IdMap.remove x body_unused_bindings
      end else 
        let xv_used_id = free_vars x_v in
        let new_unused_bindings = mark_ids_usage xv_used_id body_unused_bindings in
        Let (p, x, x_v, new_body), new_unused_bindings

    | Rec (p, x, lambda, body) ->
      let potential_unused_bindings = IdMap.add x lambda unused_bindings in
      let new_body, body_unused_bindings = env_clean_rec body potential_unused_bindings in
      if IdMap.mem x body_unused_bindings then begin
        dprint "Clean Rec(%s=..)\n" x;
        new_body, IdMap.remove x body_unused_bindings
      end else 
        (* x is recursive function def, so remove x from lambda's unused_bindings *)
        let lambda_ids = IdSet.remove x (free_vars lambda) in 
        let new_unused_bindings = mark_ids_usage lambda_ids body_unused_bindings in
        Rec (p, x, lambda, new_body), new_unused_bindings

    | Label (p, l, e) ->
      let new_e, unused_bindings = env_clean_rec e unused_bindings in
      Label (p, l, new_e), unused_bindings

    | Break (p, l, e) ->
      let new_e, unused_bindings = env_clean_rec e unused_bindings in
      Break (p, l, new_e), unused_bindings

    | TryCatch (p, body, catch) ->
      let b, unused_bindings = env_clean_rec body unused_bindings in
      let c, unused_bindings = env_clean_rec catch unused_bindings in
      TryCatch (p, b, c), unused_bindings

    | TryFinally (p, body, fin) ->
      let b, unused_bindings = env_clean_rec body unused_bindings in
      let f, unused_bindings = env_clean_rec fin unused_bindings in
      TryFinally (p, b, f), unused_bindings

    | Throw (p, e) ->
      let e, unused_bindings = env_clean_rec e unused_bindings in
      Throw(p, e), unused_bindings

    | Lambda (p, xs, body) ->
      (* lambda is only for collecting free vars *)
      let freevars = free_vars e in
      let unused_bindings = mark_ids_usage freevars unused_bindings in
      e, unused_bindings

    | Hint (p, id, e) ->
      let new_e, unused_bindings = env_clean_rec e unused_bindings in
      Hint (p, id, new_e), unused_bindings

  in 
  let new_exp, new_ids = env_clean_rec exp IdMap.empty in
  new_exp
