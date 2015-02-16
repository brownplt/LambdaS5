open Prelude
open Ljs_syntax
module EU = Exp_util

(* this optimize phase will try to convert mutation(SetBang in S5, x := 1 in S5 syntax) to let bindings.
*)
let debug_on = false

let dprint, dprint_string, dprint_ljs = Debug.make_debug_printer ~on:debug_on "less_mutation"
let dprint_set set =
  dprint "set {%s}\n" (String.concat ", " (IdSet.to_list set))

let set_str idset : string = 
  let rec lst_str lst : string =
    match lst with
    | [] -> " )"
    | hd :: [] -> sprintf "%s )" hd
    | hd :: tl -> let rest = lst_str tl in sprintf "%s, %s" hd rest
  in 
  "( " ^ lst_str (IdSet.elements idset)

let ljs_str ljs =
  Ljs_pretty.exp ljs Format.str_formatter; Format.flush_str_formatter()

let js_func_pattern exp : exp * bool = match exp with
  | Let (pos, tmp_name, func, SetBang(_, real_name, Id(_, tmp_name2)))
    when tmp_name = tmp_name2 ->
    Let (pos, real_name, func, Undefined Pos.dummy), true
  | e -> e, false

let is_setBang = function
  | SetBang (_, _, _) -> true
  | _ -> false

let get_setBang_id = function
  | SetBang (_, x, _) -> x
  | _ -> failwith "called on exp not setBang"

type env = exp IdMap.t

(*
(* convert mutation to let bindings *)
let less_mutation (exp : exp) : exp =
  let rec less_rec (e : exp) (env : env) (ids : IdSet.t) : (exp * IdSet.t) = 
    let rec handle_option (opt : exp option) ids : exp option * IdSet.t = 
      match opt with
      | Some (e) -> 
         let new_e, new_ids = less_rec e ids in
         Some (new_e), new_ids
      | None -> None, ids
    in 
    match e with
    | Null _ 
    | Undefined _
    | String (_,_)
    | Num (_,_)
    | True _
    | False _ -> (e, ids)
    | Id (_,id) -> (e, IdSet.add id ids)
    | Object (p, attrs, strprop) ->
     let primval, ids = handle_option attrs.primval ids in
     let code, ids = handle_option attrs.code ids in
     let proto, ids = handle_option attrs.proto ids in
     let new_attrs = { primval = primval; code = code;
                       proto = proto; klass = attrs.klass;
                       extensible = attrs.extensible } in
     let handle_prop (p : 'a) ids : ('a * IdSet.t) = match p with
       | (s, Data(data, enum, config)) ->
          let value, ids = less_rec data.value ids in
          (s, Data({value = value; writable = data.writable}, 
                   enum, config)), ids
       | (s, Accessor (acc, enum, config)) ->
          let getter, ids = less_rec acc.getter ids in
          let setter, ids = less_rec acc.setter ids in
          (s, Accessor ({getter = getter; setter = setter}, 
                        enum, config)), ids
     in 
     let rec handle_prop_list strprops ids = match strprops with
       | [] -> strprops, ids
       | fst :: rest ->
          let p, ids = handle_prop fst ids in
          let rest_p, rest_ids = handle_prop_list rest ids in
          p :: rest_p, rest_ids
     in 
     let prop_list, ids = handle_prop_list strprop ids in
     Object (p, new_attrs, prop_list), ids

    | GetAttr (p, pattr, obj, field) ->
       let o, ids = less_rec obj ids in
       let fld, ids = less_rec field ids in
       GetAttr (p, pattr, o, fld), ids

    | SetAttr (p, attr, obj, field, newval) ->
       let o, ids = less_rec obj ids in
       let f, ids = less_rec field ids in
       let v, ids = less_rec newval ids in
       SetAttr (p, attr, o, f, v), ids

    | GetObjAttr (p, oattr, obj) ->
       let o, ids = less_rec obj ids in
       GetObjAttr(p, oattr, o), ids

    | SetObjAttr (p, oattr, obj, attre) ->
       let o, ids = less_rec obj ids in
       let attr, ids = less_rec attre ids in
       SetObjAttr (p, oattr, o, attr), ids

    | GetField (p, obj, fld, args) -> 
       let o, ids = less_rec obj ids in
       let f, ids = less_rec fld ids in
       let a, ids = less_rec args ids in
       GetField (p, o, f, a), ids

    | SetField (p, obj, fld, newval, args) ->
       let o, ids = less_rec obj ids in
       let f, ids = less_rec fld ids in
       let v, ids = less_rec newval ids in
       let a, ids = less_rec args ids in
       SetField (p, o, f, v, a), ids

    | DeleteField (p, obj, fld) ->
       let o, ids = less_rec obj ids in
       let f, ids = less_rec fld ids in
       DeleteField (p, o, f), ids

    | OwnFieldNames (p, obj) -> 
       let o, ids = less_rec obj ids in
       OwnFieldNames (p, o), ids

    | SetBang (p, x, x_v) ->
       let x_v, ids = less_rec x_v ids in
       let ids = IdSet.add x ids in
       SetBang (p, x, x_v), ids

    | Op1 (p, op, e) ->
       let e, ids = less_rec e ids in
       Op1 (p, op, e), ids

    | Op2 (p, op, e1, e2) ->
       let e1, ids = less_rec e1 ids in
       let e2, ids = less_rec e2 ids in
       Op2 (p, op, e1, e2), ids

    | If (p, cond, thn, els) -> (* more optimization in constant folding *)
       let cond, ids = less_rec cond ids in
       let thn, ids = less_rec thn ids in
       let els, ids = less_rec els ids in
       If (p, cond, thn, els), ids

    | App (p, f, args) ->
       let f, ids = less_rec f ids in
       let rec handle_args args ids = match args with
         | [] -> args, ids
         | fst :: rest ->
            let v, new_ids = less_rec fst ids in
            let rest_v, rest_ids = handle_args rest new_ids in
            v :: rest_v, rest_ids
       in 
       let args, ids = handle_args args ids in
       App (p, f, args), ids

    | Seq (p, e1, e2) ->
      (* apply to e2 and then e1 *)
      dprint "seq visiting %s. The id set is:\n" (ljs_str e1);
      dprint_set ids;

      begin match e1 with
        | SetBang (p, x, x_v) when IdSet.mem x ids ->
          (* we haven't visit e2 yet, but used ids already contains x. That means
            x is used outside the execution path. we cannot do the transformation *)
          let new_e2, ids = less_rec e2 ids in
          let new_e1, ids = less_rec e1 ids in
          Seq (p, e1, new_e2), ids
        | SetBang (p, x, x_v) ->
          (* x may only be used in e2, so transform it! *)
          let x_v, ids = less_rec x_v ids in
          let new_e2, ids = less_rec e2 ids in
          Let (p, x, x_v, new_e2), ids
        | Let (pos, tmp_name, func, SetBang(p1, real_name, Id(p2, tmp_name2)))
          when tmp_name = tmp_name2 && 
               not (IdSet.mem real_name ids) ->
          (* desugared js function *)
          let new_func, ids = less_rec func ids in
          if IdSet.mem real_name ids then
            (* if the func contains the real_name, this function definition is a recursive function.
               We cannot do the transformation *)
            let _ = dprint "recursive function %s. keep it as it was" real_name in
            let new_e1 = Let(pos, tmp_name, new_func, SetBang(p1, real_name, Id(p2, tmp_name2))) in
            let new_e2, ids = less_rec e2 ids in
            Seq (p, new_e1, new_e2), ids
          else
            let new_e2, ids = less_rec e2 ids in
            Let(pos, real_name, new_func, new_e2), IdSet.remove real_name ids
        | _ ->
          let new_e2, ids = less_rec e2 ids in
          let new_e1, ids = less_rec e1 ids in
          Seq (p, new_e1, new_e2), ids
      end 

    | Let (pos, tmp_name, func, SetBang(p1, real_name, Id(p2, tmp_name2)))
      (* this exp is a standalone js function definition *)
      when tmp_name = tmp_name2 && 
           not (IdSet.mem real_name ids) ->
      let func, ids = less_rec func ids in
      if IdSet.mem real_name ids then
        (* recursive, leave it as it was *)
        Let (pos, tmp_name, func, SetBang(p1, real_name, Id(p2, tmp_name2))),
             IdSet.remove real_name ids
      else 
        Let (pos, real_name, func, Undefined Pos.dummy), ids

    | Let (p, x, x_v, body) -> 
      (* let should visit body first, to prevent SetBang in x_v gets wrong transformation *)
      let _ = dprint "about to visit body: %s\n; current set is\n" (ljs_str body) in
      let _ = dprint_set ids in
      let body, ids = less_rec body ids in
      let ids = IdSet.remove x ids in
      let x_v, ids = less_rec x_v ids in
      Let (p, x, x_v, body), ids
                                          
    | Rec (p, x, lambda, body) ->
      let body, ids = less_rec body ids in
      let lambda, ids = less_rec lambda ids in
      Rec (p, x, lambda, body), IdSet.remove x ids

    | Label (p, l, e) ->
       let new_e, ids = less_rec e ids in
       Label (p, l, new_e), ids

    | Break (p, l, e) ->
       let new_e, ids = less_rec e ids in
       Break (p, l, new_e), ids

    | TryCatch (p, body, catch) ->
       let b, ids = less_rec body ids in
       let c, ids = less_rec catch ids in
       TryCatch (p, b, c), ids

    | TryFinally (p, body, fin) ->
       let b, ids = less_rec body ids in
       let f, ids = less_rec fin ids in
       TryFinally (p, b, f), ids

    | Throw (p, e) ->
       let e, ids = less_rec e ids in
       Throw(p, e), ids

    | Lambda (p, xs, body) ->
       let freevars = free_vars e in
       let new_body, _ = less_rec body ids in
       Lambda (p, xs, new_body), IdSet.union freevars ids

    | Hint (p, id, e) ->
       let new_e, ids = less_rec e ids in
       Hint (p, id, new_e), ids
                              
  in 
  let new_exp, new_ids = less_rec exp IdSet.empty in
  new_exp

                   *)

(* similar to env, but only app() will enlarge the used id set *)
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

let id_used_in_env_lambda x env : bool =
  let rec search_id ?(in_lambda=false) x exp : bool = 
    match exp with
    | Id (_, id) when in_lambda -> id = x
    | SetBang (_, id, v) when in_lambda -> id = x || search_id ~in_lambda x v
    | Lambda (_, xs, body) ->
      if List.mem x xs then false
      else search_id ~in_lambda:true x body
    | Let (_, letx, _, _) when letx = x -> false
    | Rec (_, recx, _, _) when recx = x -> false
    | _ -> List.exists (fun e->search_id ~in_lambda x e)
             (child_exps exp)
  in
  let used = ref false in
  IdMap.iter (fun k v ->
      if search_id x v then used := true
    ) env;
  ! used

(* only collect free vars that are in lambda, excluding those bindings in exp *)
let rec free_vars_in_lambda exp : IdSet.t =
  match exp with
  | Let (_, var, defn, body) ->
    IdSet.union (free_vars_in_lambda defn) (IdSet.remove var (free_vars_in_lambda body))
  | Rec (_, var, defn, body) ->
    IdSet.remove var (IdSet.union (free_vars_in_lambda defn) (free_vars_in_lambda body))
  | Lambda (_, _, _) -> free_vars exp
  | exp -> List.fold_left IdSet.union IdSet.empty (map free_vars_in_lambda (child_exps exp))
    
(**  new **)
let convert_assignment (exp : exp) : exp =
  let rec convert_rec (e : exp) (env : env) (used_ids : IdSet.t) : (exp * IdSet.t) = 
    let rec handle_option (opt : exp option) env used_ids : exp option * IdSet.t = 
      match opt with
      | Some (e) -> 
        let new_e, used_ids = convert_rec e env used_ids in
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
    | Id (_,id) -> e, related_ids id env used_ids (*IdSet.add id used_ids*)
    | Object (p, attrs, strprop) ->
      let primval, used_ids = handle_option attrs.primval env used_ids in
      let code, used_ids = handle_option attrs.code env used_ids in
      let proto, used_ids = handle_option attrs.proto env used_ids in
      let new_attrs = { primval = primval; code = code;
                        proto = proto; klass = attrs.klass;
                        extensible = attrs.extensible } in
      let handle_prop (p : 'a) env used_ids : ('a * IdSet.t) = match p with
        | (s, Data(data, enum, config)) ->
          let value, used_ids = convert_rec data.value env used_ids in
          (s, Data({value = value; writable = data.writable}, 
                   enum, config)), used_ids
        | (s, Accessor (acc, enum, config)) ->
          let getter, used_ids = convert_rec acc.getter env used_ids in
          let setter, used_ids = convert_rec acc.setter env used_ids in
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
      let o, used_ids= convert_rec obj env used_ids in
      let fld, used_ids = convert_rec field env used_ids in
      GetAttr (p, pattr, o, fld), used_ids

    | SetAttr (p, attr, obj, field, newval) -> 
        let o, used_ids = convert_rec obj env used_ids in
        let f, used_ids = convert_rec field env used_ids in
        let v, used_ids = convert_rec newval env used_ids in
        SetAttr (p, attr, o, f, v), used_ids

    | GetObjAttr (p, oattr, obj) ->
      let o, used_ids = convert_rec obj env used_ids in
      GetObjAttr(p, oattr, o), used_ids

    | SetObjAttr (p, oattr, obj, attre) ->
      let o, used_ids = convert_rec obj env used_ids in
      let attr, used_ids = convert_rec attre env used_ids in
      SetObjAttr (p, oattr, o, attr), used_ids

    | GetField (p, obj, fld, args) ->
      let o, used_ids = convert_rec obj env used_ids in
      let f, used_ids = convert_rec fld env used_ids in
      let a, used_ids = convert_rec args env used_ids in
      GetField (p, o, f, a), used_ids

    | SetField (p, obj, fld, newval, args) ->
        let o, used_ids = convert_rec obj env used_ids in
        let f, used_ids = convert_rec fld env used_ids in
        let v, used_ids = convert_rec newval env used_ids in
        let a, used_ids = convert_rec args env used_ids in
        SetField (p, o, f, v, a), used_ids
        
    | DeleteField (p, obj, fld) ->
      let o, used_ids = convert_rec obj env used_ids in
      let f, used_ids = convert_rec fld env used_ids in
      DeleteField (p, o, f), used_ids

    | OwnFieldNames (p, obj) -> 
      let o, used_ids = convert_rec obj env used_ids in
      OwnFieldNames (p, o), used_ids

    | SetBang (p, x, x_v) ->
      let x_v, used_ids = convert_rec x_v env used_ids in
      let used_ids = IdSet.add x used_ids in
      dprint "find usage point at SetBang %s\n" x;
      SetBang (p, x, x_v), used_ids

    | Op1 (p, op, e) ->
      let e, used_ids = convert_rec e env used_ids in
      Op1 (p, op, e), used_ids

    | Op2 (p, op, e1, e2) ->
      let e1, used_ids = convert_rec e1 env used_ids in
      let e2, used_ids = convert_rec e2 env used_ids in
      Op2 (p, op, e1, e2), used_ids

    | If (p, cond, thn, els) -> (* more optimization in constant folding *)
      let cond, used_ids = convert_rec cond env used_ids in
      let thn, used_ids = convert_rec thn env used_ids in
      let els, used_ids = convert_rec els env used_ids in
      If (p, cond, thn, els), used_ids

    | App (p, f, args) ->
      (*let used_ids = match f with
        | Id (_, id) ->  related_ids id env used_ids
        | _ -> used_ids
      in *)
      let f, used_ids = convert_rec f env used_ids in
      let rec handle_args args env used_ids = match args with
        | [] -> args, used_ids
        | fst :: rest ->
          let v, used_ids = convert_rec fst env used_ids in
          let rest_v, used_ids = handle_args rest env used_ids in
          v :: rest_v, used_ids
      in 
      let args, used_ids = handle_args args env used_ids in
      App (p, f, args), used_ids

    | Seq (p, e1, e2) ->
      (* apply to e2 and then e1 *)
      dprint "seq visiting %s. The id set is:\n" (ljs_str e1);
      dprint_set used_ids;
      begin match e1 with
        | SetBang (p, x, x_v) when IdSet.mem x used_ids || id_used_in_env_lambda x env ->
          let _ = dprint "%s of setBang is used elsewhere. no change\n" x in
          (* we haven't visit e2 yet, but used used_ids already contains x. That means
            x is used outside the execution path. we cannot do the transformation *)
          let new_e2, used_ids = convert_rec e2 env used_ids in
          let new_e1, used_ids = convert_rec e1 env used_ids in
          Seq (p, e1, new_e2), used_ids
        | SetBang (p, x, x_v) ->
          let _ = dprint "transform %s" (ljs_str e1) in
          (* x may only be used in e2, so transform it! *)
          let x_v, used_ids = convert_rec x_v env used_ids in
          let new_e2, used_ids = convert_rec e2 env used_ids in
          Let (p, x, x_v, new_e2), used_ids
        | Let (pos, "#strict", v, Let (p, tmp_name, func, SetBang(p1, real_name, Id(p2, tmp_name2))))
          when tmp_name = tmp_name2 ->
          dprint_string "find js function pattern\n";
          (* desugared js function *)
          let new_func, used_ids = convert_rec func env used_ids in
          if IdSet.mem real_name used_ids then
            (* if the func contains the real_name, this function definition is a recursive function.
               We cannot do the transformation *)
            let _ = dprint "recursive function %s. keep it as it was\n" real_name in
            let new_e1 = Let (pos, "#strict", v, Let(pos, tmp_name, new_func, SetBang(p1, real_name, Id(p2, tmp_name2)))) in
            let new_e2, used_ids = convert_rec e2 env used_ids in
            Seq (p, new_e1, new_e2), used_ids
          else
            let _ = dprint "convert js function def pattern %s to let\n" (ljs_str e1) in
            let new_e2, used_ids = convert_rec e2 env used_ids in
            Let (pos, "#strict", v, Let(pos, real_name, new_func, new_e2)), IdSet.remove real_name used_ids
        | Let (pos, tmp_name, func, SetBang(p1, real_name, Id(p2, tmp_name2)))
          when tmp_name = tmp_name2 ->
          dprint_string "find js function pattern\n";
          (* desugared js function *)
          let new_func, used_ids = convert_rec func env used_ids in
          if IdSet.mem real_name used_ids then
            (* if the func contains the real_name, this function definition is a recursive function.
               We cannot do the transformation *)
            let _ = dprint "recursive function %s. keep it as it was\n" real_name in
            let new_e1 = Let(pos, tmp_name, new_func, SetBang(p1, real_name, Id(p2, tmp_name2))) in
            let new_e2, used_ids = convert_rec e2 env used_ids in
            Seq (p, new_e1, new_e2), used_ids
          else
            let _ = dprint "convert js function def pattern %s to let\n" (ljs_str e1) in
            let new_e2, used_ids = convert_rec e2 env used_ids in
            Let(pos, real_name, new_func, new_e2), IdSet.remove real_name used_ids
        | _ ->
          let _ = dprint_string "normal seq\n" in
          let used_ids = IdSet.union (free_vars_in_lambda e1) used_ids in
          let new_e2, used_ids = convert_rec e2 env used_ids in
          let new_e1, used_ids = convert_rec e1 env used_ids in
          Seq (p, new_e1, new_e2), used_ids
      end 

    | Let (pos, tmp_name, func, SetBang(p1, real_name, Id(p2, tmp_name2)))
      (* this exp is a standalone js function definition *)
      when tmp_name = tmp_name2 ->
      let func, used_ids = convert_rec func env used_ids in
      if IdSet.mem real_name used_ids then
        (* recursive, leave it as it was *)
        Let (pos, tmp_name, func, SetBang(p1, real_name, Id(p2, tmp_name2))),
             IdSet.remove real_name used_ids
      else 
        Let (pos, real_name, func, Undefined Pos.dummy), used_ids

    | Let (p, x, x_v, body) ->
      let new_env = IdMap.add x x_v env in
      let used_ids = IdSet.union used_ids (free_vars_in_lambda x_v) in 
      let new_body, used_ids = convert_rec body new_env used_ids in
      let x_v, used_ids = convert_rec x_v env used_ids in
      let used_ids = IdSet.remove x used_ids in
      Let (p, x, x_v, new_body), used_ids

    | Rec (p, x, lambda, body) ->
      let new_env = IdMap.add x lambda env in
      let new_body, used_ids = convert_rec body new_env used_ids in
      (* x is recursive function def, so remove x from lambda's env *)
      let lambda, used_ids = convert_rec lambda env used_ids in
      let used_ids = IdSet.remove x used_ids in 
      Rec (p, x, lambda, new_body), used_ids

    | Label (p, l, e) ->
      let new_e, used_ids = convert_rec e env used_ids in
      Label (p, l, new_e), used_ids

    | Break (p, l, e) ->
      let new_e, used_ids = convert_rec e env used_ids in
      Break (p, l, new_e), used_ids

    | TryCatch (p, body, catch) ->
      let b, used_ids = convert_rec body env used_ids in
      let c, used_ids = convert_rec catch env used_ids in
      TryCatch (p, b, c), used_ids

    | TryFinally (p, body, fin) ->
      let b, used_ids = convert_rec body env used_ids in
      let f, used_ids = convert_rec fin env used_ids in
      TryFinally (p, b, f), used_ids

    | Throw (p, e) ->
      let e, used_ids = convert_rec e env used_ids in
      Throw(p, e), used_ids

    | Lambda (p, xs, body) ->
      (* lambda is only for collecting free vars. however,
         `with` expression will be desugared to fun(e) and the
         lambda contains variables like %context['TypeError']  *)
      let body, used_ids = convert_rec body env used_ids in
      let used_ids = IdSet.diff used_ids (IdSet.from_list xs) in
      Lambda (p, xs, body), used_ids

    | Hint (p, id, e) ->
      let new_e, used_ids = convert_rec e env used_ids in
      Hint (p, id, new_e), used_ids

  in 
  let new_exp, new_ids = convert_rec exp IdMap.empty IdSet.empty in
  new_exp
