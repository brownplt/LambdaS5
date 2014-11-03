open Prelude
open Ljs_syntax
module EU = Exp_util

let ljs_str ljs =
  Ljs_pretty.exp ljs Format.str_formatter; Format.flush_str_formatter()

let debug_on = false

let dprint, dprint_string, dprint_ljs = Debug.make_debug_printer ~on:debug_on "env-clean"

let set_str idset : string = 
  let rec lst_str lst : string =
    match lst with
    | [] -> " )"
    | hd :: [] -> sprintf "%s )" hd
    | hd :: tl -> let rest = lst_str tl in sprintf "%s, %s" hd rest
  in 
  "( " ^ lst_str (IdSet.elements idset)

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

type env = exp IdMap.t

let rec useless_def_point f args (env : env) (used_ids : IdSet.t) : bool =
  match f, args with
  | Id(_, "%defineOwnProperty"), [Id(_, "%global"); String(_, func_name); Object(_,_,_)] ->
    (* field of %global(global var) is not used *)
    not (IdSet.mem func_name used_ids)
  | Id(_, "%defineNYIProperty"), [Id(_, proto); String(_, func_name)] ->
    (* proto is not used *)
    not (IdSet.mem proto used_ids)
  | Id(_, "%define15Property"), [Id(_, obj); String(_, func_name);_] ->
    (* obj is not used *)
    not (IdSet.mem obj used_ids)
  | Id(_, "%defineOwnProperty"), [Id(_, obj); String(_, func_name); _] ->
    (* obj is not used *)
    not (IdSet.mem obj used_ids)
  | _ -> false

let useless_obj_set obj field env used_ids : bool =
  match obj, field with
  | Id(_, "%global"), String(_, fld) ->
    (* always special case the obj field of %global, because it is actually a def point *)
    not (IdSet.mem fld used_ids)
  | Id (_, o), String(_,_) ->
    (* in env, if the object is not used(directly or indirectly) in user code, we can clean it *)
    (* todo: side effect: unused_obj["hello" = {..prim('pretty', 1)}] *)
    not (IdSet.mem o used_ids)
  | _ -> false

let rec related_ids id (env : env) (curr_used : IdSet.t) : IdSet.t =
  try
    if IdSet.mem id curr_used then
      curr_used
    else begin
      let exp = IdMap.find id env in
      let rest_ids = free_vars exp in
      let curr_used = IdSet.add id curr_used in
      IdSet.fold (fun elm old_set ->
          related_ids elm env old_set)
        rest_ids curr_used
    end 
  with _ -> IdSet.add id curr_used

(* eliminate unused ids in environment *)
let new_env_clean (exp : exp) : exp =
  let rec env_clean_rec (e : exp) (env : env) (used_ids : IdSet.t) : (exp * IdSet.t) = 
    let rec handle_option (opt : exp option) env used_ids : exp option * IdSet.t = 
      match opt with
      | Some (e) -> 
        let new_e, used_ids = env_clean_rec e env used_ids in
        Some (new_e), used_ids
      | None -> None, used_ids
    in 
    match e with
    | Null _ 
    | Undefined _
    | String (_,_)
    | Num (_,_)
    | True _
    | False _ -> e, used_ids
    | Id (_,id) ->
      begin
        let used_ids = related_ids id env used_ids in
        dprint_string (sprintf "visit %s. related ids are %s\n" id (set_str used_ids));
        e, used_ids
      end 
    | Object (p, attrs, strprop) ->
      let primval, used_ids = handle_option attrs.primval env used_ids in
      let code, used_ids = handle_option attrs.code env used_ids in
      let proto, used_ids = handle_option attrs.proto env used_ids in
      let new_attrs = { primval = primval; code = code;
                        proto = proto; klass = attrs.klass;
                        extensible = attrs.extensible } in
      let handle_prop (p : 'a) env used_ids : ('a * IdSet.t) = match p with
        | (s, Data(data, enum, config)) ->
          let value, used_ids = env_clean_rec data.value env used_ids in
          (s, Data({value = value; writable = data.writable}, 
                   enum, config)), used_ids
        | (s, Accessor (acc, enum, config)) ->
          let getter, used_ids = env_clean_rec acc.getter env used_ids in
          let setter, used_ids = env_clean_rec acc.setter env used_ids in
          (s, Accessor ({getter = getter; setter = setter}, 
                        enum, config)), used_ids
      in 
      let rec handle_prop_list strprops env used_ids = match strprops with
        | [] -> strprops, used_ids
        | fst :: rest ->
          let p, used_ids = handle_prop fst env used_ids in
          let rest_p, used_ids = handle_prop_list rest env used_ids in
          p :: rest_p, used_ids
      in 
      let prop_list, used_ids = handle_prop_list strprop env used_ids in
      Object (p, new_attrs, prop_list), used_ids

    | GetAttr (p, pattr, obj, field) ->
      let o, used_ids= env_clean_rec obj env used_ids in
      let fld, used_ids = env_clean_rec field env used_ids in
      GetAttr (p, pattr, o, fld), used_ids

    | SetAttr (p, attr, obj, field, newval) -> 
      if useless_obj_set obj field env used_ids then begin
        dprint "clean SetAttr: %s\n" (EU.ljs_str e);
        Undefined Pos.dummy, used_ids
      end else 
        let o, used_ids = env_clean_rec obj env used_ids in
        let f, used_ids = env_clean_rec field env used_ids in
        let v, used_ids = env_clean_rec newval env used_ids in
        SetAttr (p, attr, o, f, v), used_ids

    | GetObjAttr (p, oattr, obj) ->
      let o, used_ids = env_clean_rec obj env used_ids in
      GetObjAttr(p, oattr, o), used_ids

    | SetObjAttr (p, oattr, obj, attre) ->
      let o, used_ids = env_clean_rec obj env used_ids in
      let attr, used_ids = env_clean_rec attre env used_ids in
      SetObjAttr (p, oattr, o, attr), used_ids

    | GetField (p, obj, fld, args) ->
      let o, used_ids = env_clean_rec obj env used_ids in
      let f, used_ids = env_clean_rec fld env used_ids in
      let a, used_ids = env_clean_rec args env used_ids in
      let used_ids = match obj, fld with
        | Id (_, "%context"), String (_, id) -> 
          (dprint "use point %s\n" id; IdSet.add id used_ids)
        | _ -> used_ids
      in 
      GetField (p, o, f, a), used_ids

    | SetField (p, obj, fld, newval, args) ->
      if useless_obj_set obj fld env used_ids then begin
        dprint "clean SetField: %s\n" (EU.ljs_str e);
        Undefined Pos.dummy, used_ids
      end 
      else
        let o, used_ids = env_clean_rec obj env used_ids in
        let f, used_ids = env_clean_rec fld env used_ids in
        let v, used_ids = env_clean_rec newval env used_ids in
        let a, used_ids = env_clean_rec args env used_ids in
        SetField (p, o, f, v, a), used_ids
        
    | DeleteField (p, obj, fld) ->
      let o, used_ids = env_clean_rec obj env used_ids in
      let f, used_ids = env_clean_rec fld env used_ids in
      DeleteField (p, o, f), used_ids

    | OwnFieldNames (p, obj) -> 
      let o, used_ids = env_clean_rec obj env used_ids in
      OwnFieldNames (p, o), used_ids

    | SetBang (p, x, x_v) ->
      let x_v, used_ids = env_clean_rec x_v env used_ids in
      let used_ids = IdSet.add x used_ids in
      dprint "find usage point at SetBang %s\n" x;
      SetBang (p, x, x_v), used_ids

    | Op1 (p, op, e) ->
      let e, used_ids = env_clean_rec e env used_ids in
      Op1 (p, op, e), used_ids

    | Op2 (p, op, e1, e2) ->
      let e1, used_ids = env_clean_rec e1 env used_ids in
      let e2, used_ids = env_clean_rec e2 env used_ids in
      Op2 (p, op, e1, e2), used_ids

    | If (p, cond, thn, els) -> (* more optimization in constant folding *)
      let cond, used_ids = env_clean_rec cond env used_ids in
      let thn, used_ids = env_clean_rec thn env used_ids in
      let els, used_ids = env_clean_rec els env used_ids in
      If (p, cond, thn, els), used_ids

    | App (p, f, args) ->
      let is_global_accessor () : id option =  match f, args with
        | Id (_, "%defineGlobalAccessors"), [Id(_, ctx); String(_, global_var)] 
          when is_context_id ctx ->
          Some global_var
        | _ -> None
      in
      let used_ids = match is_global_accessor () with
        | Some (id) -> IdSet.add id used_ids
        | None -> used_ids
      in 
      if useless_def_point f args env used_ids then begin
        dprint "clean app: %s\n" (EU.ljs_str e);
        Undefined Pos.dummy, used_ids
      end else 
        let f, used_ids = env_clean_rec f env used_ids in
        let rec handle_args args env used_ids = match args with
          | [] -> args, used_ids
          | fst :: rest ->
            let v, used_ids = env_clean_rec fst env used_ids in
            let rest_v, used_ids = handle_args rest env used_ids in
            v :: rest_v, used_ids
        in 
        let args, used_ids = handle_args args env used_ids in
        App (p, f, args), used_ids

    | Seq (p, e1, e2) ->
      let new_e2, e2_used_ids = env_clean_rec e2 env used_ids in
      let new_e1, e1_used_ids = env_clean_rec e1 env e2_used_ids in
      let e1_is_lambda = match new_e1 with Lambda (_,_,_) -> true | _ -> false in
      if e1_is_lambda || not (EU.has_side_effect new_e1) then
        new_e2, e1_used_ids
      else 
        Seq (p, new_e1, new_e2), e1_used_ids

    | Let (p, x, x_v, body) ->
      let new_env = IdMap.add x x_v env in
      let new_body, used_ids = env_clean_rec body new_env used_ids in
      if not (IdSet.mem x used_ids) then begin
        dprint "Clean Let(%s=..)\n" x;
        new_body, used_ids
      end else 
        let xv_used_id = free_vars x_v in
        let used_ids = IdSet.remove x used_ids in
        Let (p, x, x_v, new_body), IdSet.union xv_used_id used_ids

    | Rec (p, x, lambda, body) ->
      let new_env = IdMap.add x lambda env in
      let new_body, used_ids = env_clean_rec body new_env used_ids in
      if not (IdSet.mem x used_ids) then begin
        dprint "Clean Rec(%s=..)\n" x;
        new_body, used_ids
      end else 
        (* x is recursive function def, so remove x from lambda's env *)
        let lambda_ids = IdSet.remove x (free_vars lambda) in 
        let used_ids = IdSet.remove x used_ids in
        Rec (p, x, lambda, new_body), IdSet.union lambda_ids used_ids

    | Label (p, l, e) ->
      let new_e, used_ids = env_clean_rec e env used_ids in
      Label (p, l, new_e), used_ids

    | Break (p, l, e) ->
      let new_e, used_ids = env_clean_rec e env used_ids in
      Break (p, l, new_e), used_ids

    | TryCatch (p, body, catch) ->
      let b, used_ids = env_clean_rec body env used_ids in
      let c, used_ids = env_clean_rec catch env used_ids in
      TryCatch (p, b, c), used_ids

    | TryFinally (p, body, fin) ->
      let b, used_ids = env_clean_rec body env used_ids in
      let f, used_ids = env_clean_rec fin env used_ids in
      TryFinally (p, b, f), used_ids

    | Throw (p, e) ->
      let e, used_ids = env_clean_rec e env used_ids in
      Throw(p, e), used_ids

    | Lambda (p, xs, body) ->
      (* lambda is only for collecting free vars. however,
         `with` expression will be desugared to fun(e) and the
         lambda contains variables like %context['TypeError']  *)
      let body, used_ids = env_clean_rec body env used_ids in
      let used_ids = IdSet.diff used_ids (IdSet.from_list xs) in
      e, used_ids

    | Hint (p, id, e) ->
      let new_e, used_ids = env_clean_rec e env used_ids in
      Hint (p, id, new_e), used_ids

  in 
  let new_exp, new_ids = env_clean_rec exp IdMap.empty IdSet.empty in
  new_exp
