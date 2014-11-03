open Prelude
open Ljs_syntax
module EU = Exp_util

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

(* eliminate unused ids, sequence *)
let less_mutation (exp : exp) : exp =
  let rec less_rec (e : exp) (ids : IdSet.t) : (exp * IdSet.t) = 
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
        | Let (pos, tmp_name, func, SetBang(_, real_name, Id(_, tmp_name2)))
          when tmp_name = tmp_name2 && 
               not (IdSet.mem real_name ids) ->
          (* js function desugared out *)
          let func, ids = less_rec func ids in
          let new_e2, ids = less_rec e2 ids in
          Let (pos, real_name, func, new_e2), ids
        | _ ->
          let new_e2, ids = less_rec e2 ids in
          let new_e1, ids = less_rec e1 ids in
          Seq (p, new_e1, new_e2), ids
      end 

    | Let (pos, tmp_name, func, SetBang(_, real_name, Id(_, tmp_name2)))
      when tmp_name = tmp_name2 && 
           not (IdSet.mem real_name ids) ->
      let func, ids = less_rec func ids in
      Let (pos, real_name, func, Undefined Pos.dummy), ids

    | Let (p, x, x_v, body) -> 
      let x_v, ids = less_rec x_v ids in
      let ids = IdSet.add x ids in
      let body, ids = less_rec body ids in
      Let (p, x, x_v, body), IdSet.remove x ids
                                          
    | Rec (p, x, lambda, body) ->
      let x_v, ids = less_rec lambda ids in
      let ids = IdSet.add x ids in
      let body, ids = less_rec body ids in
      Rec (p, x, x_v, body), IdSet.remove x ids

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
