open Prelude
open Ljs_syntax
module EU = Exp_util

type env = exp IdMap.t

let ljs_str ljs =
  Ljs_pretty.exp ljs Format.str_formatter; Format.flush_str_formatter()

(* eliminate unused ids, sequence *)
let deadcode_elimination (exp : exp) : exp =
  let rec eliminate_ids_rec (e : exp) (ids : IdSet.t) : (exp * IdSet.t) = 
    let rec handle_option (opt : exp option) ids : exp option * IdSet.t = 
      match opt with
      | Some (e) -> 
         let new_e, new_ids = eliminate_ids_rec e ids in
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
          let value, ids = eliminate_ids_rec data.value ids in
          (s, Data({value = value; writable = data.writable}, 
                   enum, config)), ids
       | (s, Accessor (acc, enum, config)) ->
          let getter, ids = eliminate_ids_rec acc.getter ids in
          let setter, ids = eliminate_ids_rec acc.setter ids in
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
       let o, ids = eliminate_ids_rec obj ids in
       let fld, ids = eliminate_ids_rec field ids in
       GetAttr (p, pattr, o, fld), ids

    | SetAttr (p, attr, obj, field, newval) ->
       let o, ids = eliminate_ids_rec obj ids in
       let f, ids = eliminate_ids_rec field ids in
       let v, ids = eliminate_ids_rec newval ids in
       SetAttr (p, attr, o, f, v), ids

    | GetObjAttr (p, oattr, obj) ->
       let o, ids = eliminate_ids_rec obj ids in
       GetObjAttr(p, oattr, o), ids

    | SetObjAttr (p, oattr, obj, attre) ->
       let o, ids = eliminate_ids_rec obj ids in
       let attr, ids = eliminate_ids_rec attre ids in
       SetObjAttr (p, oattr, o, attr), ids

    | GetField (p, obj, fld, args) -> 
       let o, ids = eliminate_ids_rec obj ids in
       let f, ids = eliminate_ids_rec fld ids in
       let a, ids = eliminate_ids_rec args ids in
       GetField (p, o, f, a), ids

    | SetField (p, obj, fld, newval, args) ->
       let o, ids = eliminate_ids_rec obj ids in
       let f, ids = eliminate_ids_rec fld ids in
       let v, ids = eliminate_ids_rec newval ids in
       let a, ids = eliminate_ids_rec args ids in
       SetField (p, o, f, v, a), ids

    | DeleteField (p, obj, fld) ->
       let o, ids = eliminate_ids_rec obj ids in
       let f, ids = eliminate_ids_rec fld ids in
       DeleteField (p, o, f), ids

    | OwnFieldNames (p, obj) -> 
       let o, ids = eliminate_ids_rec obj ids in
       OwnFieldNames (p, o), ids

    | SetBang (p, x, x_v) ->
       let x_v, ids = eliminate_ids_rec x_v ids in
       let ids = IdSet.add x ids in
       SetBang (p, x, x_v), ids

    | Op1 (p, op, e) ->
       let e, ids = eliminate_ids_rec e ids in
       Op1 (p, op, e), ids

    | Op2 (p, op, e1, e2) ->
       let e1, ids = eliminate_ids_rec e1 ids in
       let e2, ids = eliminate_ids_rec e2 ids in
       Op2 (p, op, e1, e2), ids

    | If (p, cond, thn, els) -> (* more optimization in constant folding *)
       let cond, ids = eliminate_ids_rec cond ids in
       let thn, ids = eliminate_ids_rec thn ids in
       let els, ids = eliminate_ids_rec els ids in
       If (p, cond, thn, els), ids

    | App (p, f, args) ->
       let f, ids = eliminate_ids_rec f ids in
       let rec handle_args args ids = match args with
         | [] -> args, ids
         | fst :: rest ->
            let v, new_ids = eliminate_ids_rec fst ids in
            let rest_v, rest_ids = handle_args rest new_ids in
            v :: rest_v, rest_ids
       in 
       let args, ids = handle_args args ids in
       App (p, f, args), ids

(*
    | Seq (p, e1, e2) ->
       (* sequence can either first visit e1 or e2 *)
       (* if e1 is lambda or has no side effect, e1 can be eliminated *)
       let new_e1, e1_ids = eliminate_ids_rec e1 ids in
       let e1_is_lambda = match new_e1 with Lambda (_,_,_) -> true | _ -> false in
       if (e1_is_lambda || not (EU.has_side_effect new_e1)) then
         eliminate_ids_rec e2 e1_ids
       else 
         let new_e2, ids = eliminate_ids_rec e2 e1_ids in
         Seq (p, new_e1, new_e2), ids
 *)

    | Seq (p, e1, e2) ->
       let new_e2, e2_ids = eliminate_ids_rec e2 ids in
       let new_e1, e1_ids = eliminate_ids_rec e1 ids in
       let e1_is_lambda = match new_e1 with Lambda (_,_,_) -> true | _ -> false in
       if e1_is_lambda || not (EU.has_side_effect new_e1) then
         new_e2, e2_ids
       else 
         Seq (p, new_e1, new_e2), IdSet.union e1_ids e2_ids
     

(*
    | Seq (p, e1, e2) ->
       let new_e2, e2_ids = eliminate_ids_rec e2 ids in
       let new_e1, e1_ids = eliminate_ids_rec e1 ids in
       let e1_is_lambda = match new_e1 with Lambda (_,_,_) -> true | _ -> false in
       if (e1_is_lambda || not (EU.has_side_effect new_e1)) then
         new_e2, e2_ids
       else 
         Seq (p, new_e1, new_e2), IdSet.union e1_ids e2_ids
 *)     
       
    (* to retain this let,
       1. x is used in body, or
       2. x_v will be evaluated to have side effect
       NOTE: this means that if x_v is lambda(or x_v has no side effect), and x is
       not used in body, this let should be eliminated 
     *)
    (* TODO: we can maintain a list to contains the internal function that does not have side effect,
       so that we can eliminate more code like `let %this = %resolveThis(true, %this)...`
    *)
    | Let (p, x, x_v, body) -> 
       let xv_is_lambda = match x_v with Lambda (_,_,_) -> true | _ -> false in
       let new_body, body_ids = eliminate_ids_rec body ids in
       if not (IdSet.mem x body_ids) && (xv_is_lambda || not (EU.has_side_effect x_v))
       then begin
           (*printf "not include [%s] collect ids:" x;
         IdSet.iter (fun s->printf "%s," s) body_ids; print_newline();*)
         new_body, body_ids
         end 
       else 
         let new_x_v, v_ids = eliminate_ids_rec x_v IdSet.empty in
         let new_ids = IdSet.union (IdSet.remove x body_ids) v_ids in
         (*printf "include [%s]. collect ids:" x; 
         IdSet.iter (fun s->printf "%s," s) new_ids; print_newline();*)
         Let (p, x, new_x_v, new_body), new_ids
                                          
    | Rec (p, x, lambda, body) ->
       let new_body, body_ids = eliminate_ids_rec body ids in
       if not (IdSet.mem x body_ids) then
         new_body, body_ids
       else 
         let new_lambda, v_ids = eliminate_ids_rec lambda IdSet.empty in
         (* x is recursive function def, so remove x from v_ids *)
         let v_ids = IdSet.remove x v_ids in 
         let new_ids = IdSet.union (IdSet.remove x body_ids) v_ids in
         Rec (p, x, new_lambda, new_body), new_ids

    | Label (p, l, e) ->
       let new_e, ids = eliminate_ids_rec e ids in
       Label (p, l, new_e), ids

    | Break (p, l, e) ->
       let new_e, ids = eliminate_ids_rec e ids in
       Break (p, l, new_e), ids

    | TryCatch (p, body, catch) ->
       let b, ids = eliminate_ids_rec body ids in
       let c, ids = eliminate_ids_rec catch ids in
       TryCatch (p, b, c), ids

    | TryFinally (p, body, fin) ->
       let b, ids = eliminate_ids_rec body ids in
       let f, ids = eliminate_ids_rec fin ids in
       TryFinally (p, b, f), ids

    | Throw (p, e) ->
       let e, ids = eliminate_ids_rec e ids in
       Throw(p, e), ids

    | Lambda (p, xs, body) ->
       let freevars = free_vars e in
       let new_body, _ = eliminate_ids_rec body ids in
       Lambda (p, xs, new_body), IdSet.union freevars ids

    | Hint (p, id, e) ->
       let new_e, ids = eliminate_ids_rec e ids in
       Hint (p, id, new_e), ids
                              
  in 
  let new_exp, new_ids = eliminate_ids_rec exp IdSet.empty in
  new_exp
