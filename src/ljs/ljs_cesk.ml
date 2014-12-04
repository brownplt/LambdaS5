module C = Ljs_clos
module D = Ljs_delta
module L = Ljs_eval
module GC = Ljs_gc
module K = Ljs_kont
module PV = Ljs_pretty_value
module S = Ljs_syntax
module V = Ljs_values
module P = Prelude
module LocSet = Store.LocSet
module LocMap = Store.LocMap

(* A CESK-style evaluator for LambdaS5 *)
(* Written by Nicholas Labich and Adam Alix with help from David Van Horn. *)

(* borrowed from ljs_eval *)

let arity_mismatch_err p xs args =
  L.interp_error p ("Arity mismatch, supplied " ^
                    string_of_int (List.length args) ^
                    " arguments and expected " ^
                    string_of_int (List.length xs) ^
                    ". Arg names were: " ^
                    (List.fold_right (^) (P.map (fun s -> " " ^ s ^ " ") xs) "") ^
                    ". Values were: " ^
                    (List.fold_right (^) (P.map (fun v -> " " ^ V.pretty_value v ^ " ") args) ""))

(* modified from ljs_eval to add the arguments to the environment and store,
   then a triple of the body of the function, the updated env, and the
   updated store. *)
let rec apply p store func args = match func with
  | V.Closure (env, xs, body) ->
    let alloc_arg argval argname (store, env) =
      let (new_loc, store) = V.add_var store argval in
      let env' = P.IdMap.add argname new_loc env in
      (store, env') in
    if (List.length args) != (List.length xs) then
      arity_mismatch_err p xs args
    else
      let (store, env) = (List.fold_right2 alloc_arg args xs (store, env)) in
      (body, env, store)
  | V.ObjLoc loc -> begin match V.get_obj store loc with
    | ({ V.code = Some f }, _) -> apply p store f args
    | _ -> failwith "Applied an object without a code attribute"
  end
  | _ -> failwith (L.interp_error p
                     ("Applied non-function, was actually " ^
                         V.pretty_value func))

(* end borrowed ljs_eval helpers *)

(* gc params *)
let store_gc_size = 1500
let gc_instr_count = 30000

let count ((obj_s, _), (val_s, _)) =
  let folder = (fun _ _ n -> n+1) in
  (LocMap.fold folder obj_s 0, LocMap.fold folder val_s 0)

(* misc *)

let add_opt clos xs f = match f clos with
  | Some x -> x::xs
  | None -> xs

(* eval_cesk : (string -> Ljs_syntax.exp)
 *             clos
 *             (objectv Store.t * value Store.t)
 *             kont
 *             int ->
 *             (value * store)                   
 * Portions of these cases are in the vein of or replications of code in
 * ljs_eval, especially pertaining to attrs and fields. Both credit and
 * thanks go to the original author(s). *)
let rec eval_cesk desugar clo store kont i =
  (* very naive gc, much room for improvement here *)
  let store =
    if i mod gc_instr_count = 0 then
      match count store with
      | obj_count, val_count ->
        if obj_count > store_gc_size || val_count > store_gc_size then
          Ljs_gc.collect_garbage store (LocSet.union (C.locs_of_clos clo) (K.locs_of_kont kont))
        else store
    else store in
  begin
    let eval clo store kont = eval_cesk desugar clo store kont (i+1) in
    match clo, kont with
    | C.ValClos (valu, env), K.Mt ->
      (valu, store)
    (* value cases *)
    | C.ExpClos (S.Undefined _, env), _ ->
      eval (C.ValClos (V.Undefined, env)) store kont
    | C.ExpClos (S.Null _, env), _ ->
      eval (C.ValClos (V.Null, env)) store kont
    | C.ExpClos (S.String (_, s), env), _ ->
      eval (C.ValClos (V.String s, env)) store kont
    | C.ExpClos (S.Num (_, n), env), _ ->
      eval (C.ValClos (V.Num n, env)) store kont
    | C.ExpClos (S.True _, env), _ ->
      eval (C.ValClos (V.True, env)) store kont
    | C.ExpClos (S.False _, env), _ ->
      eval (C.ValClos (V.False, env)) store kont
    | C.ExpClos (S.Id (p, name), env), _ ->
      (match try V.get_maybe_var store (P.IdMap.find name env) with Not_found -> None with
      | Some valu -> eval (C.ValClos (valu, env)) store kont
      | None      -> failwith ("[interp] Unbound identifier: " ^ name ^ " in identifier lookup at " ^
                                  (P.Pos.string_of_pos p)))
    | C.ExpClos (S.Lambda (_, xs, body), env), k ->
      let free = S.free_vars body in
      let env' = P.IdMap.filter (fun var _ -> P.IdSet.mem var free) env in
      eval (C.ValClos (V.Closure (env', xs, body), env)) store k
    (* S.SetBang (pos, name, next)
     * Set name to next. *)
    | C.ExpClos (S.SetBang (p, x, new_val_exp), env), k ->
      (match try Some (P.IdMap.find x env) with Not_found -> None with
      | Some loc -> eval (C.ExpClos (new_val_exp, env)) store (K.SetBang (loc, k))
      | None     -> failwith ("[interp] Unbound identifier: " ^ x
                              ^ " in identifier lookup at " ^ (P.Pos.string_of_pos p)))
    | C.ValClos (v, env), K.SetBang (loc, k) ->
      let store' = V.set_var store loc v in
      eval (C.ValClos (v, env)) store' k
    (* S.Object (pos, attrs, props)
     * Evaluates the attrs, props, then adds the object to the
     * obj half of the store. *)
    | C.ExpClos (S.Object (p, attrs, props), env), k ->
      eval (C.AttrExpClos (attrs, env)) store (K.Object (props, k))
    | C.AttrValClos (valu, env), K.Object ([], k) -> (* empty props case *)
      let obj_loc, store = V.add_obj store (valu, P.IdMap.empty) in
      eval (C.ValClos (V.ObjLoc obj_loc, env)) store k
    | C.AttrValClos (attrsv, env), K.Object (prop::props, k) ->
      eval (C.PropExpClos (prop, env)) store (K.Object2 (attrsv, props, [], k))
    | C.PropValClos (propv, env), K.Object2 (attrsv, prop::props, propvs, k) ->
      eval (C.PropExpClos (prop, env)) store (K.Object2 (attrsv, props, propv::propvs, k))
    | C.PropValClos (propv, env), K.Object2 (attrsv, [], propvs, k) ->
      let add_prop acc (name, propv) = P.IdMap.add name propv acc in
      let propsv = List.fold_left add_prop P.IdMap.empty (propv::propvs) in
      let obj_loc, store = V.add_obj store (attrsv, propsv) in
      eval (C.ValClos (V.ObjLoc obj_loc, env)) store k
    (* S.Data ({ exp; writable }, enum, config)
     * Evaluates exp, then continues with the propv to object creation.
     * S.Accessor ({ getter; setter }, enum, config)
     * Same as S.Data, but with getter and setter.  *)
    | C.PropExpClos ((name, prop), env), k ->
      (match prop with
      | S.Data ({ S.value = valu; S.writable = writable; }, enum, config) ->
        eval (C.ExpClos (valu, env)) store (K.DataProp (name, writable, enum, config, k))
      | S.Accessor ({ S.getter = getter; S.setter = setter; }, enum, config) ->
        eval (C.ExpClos (getter, env)) store (K.AccProp (name, setter, enum, config, k)))
    | C.ValClos (valu, env), K.DataProp (name, writable, enum, config, k) ->
      eval (C.PropValClos ((name, V.Data ({ V.value=valu; V.writable=writable; }, enum, config)), env)) store k
    | C.ValClos (get_val, env), K.AccProp (name, setter, enum, config, k) ->
      eval (C.ExpClos (setter, env)) store (K.AccProp2 (name, get_val, enum, config, k))
    | C.ValClos (set_val, env), K.AccProp2 (name, get_val, enum, config, k) ->
      eval (C.PropValClos ((name, V.Accessor ({ V.getter=get_val; V.setter=set_val; }, enum, config)), env)) store k
    (* S.attrs : { primval; code; proto; class; extensible }
     * Evaluates optional exps primval, code, and proto, then continues
     * with an S.arrtsv. *)
    | C.AttrExpClos (attrs, env), k ->
      let { S.primval = pexp;
            S.code = cexp;
            S.proto = proexp;
            S.klass = kls;
            S.extensible = ext; } = attrs in
      let opt_add name ox xs = match ox with Some x -> (name, x)::xs | _ -> xs in
      let aes = opt_add "prim" pexp (opt_add "code" cexp (opt_add "proto" proexp [])) in
      (match aes with
      | [] ->
        let attrsv = { V.code=None; V.proto=V.Undefined; V.primval=None; V.klass=kls; V.extensible=ext } in
        eval (C.AttrValClos (attrsv, env)) store k
      | (name, exp)::pairs -> eval (C.ExpClos (exp, env)) store (K.Attrs (name, pairs, [], kls, ext, k)))
    | C.ValClos (valu, env), K.Attrs (name, (name', exp)::pairs, valus, kls, ext, k) ->
      eval (C.ExpClos (exp, env)) store (K.Attrs (name', pairs, (name, valu)::valus, kls, ext, k))
    | C.ValClos (valu, env), K.Attrs (name, [], valus, kls, ext, k) ->
      let valus = (name, valu)::valus in
      let rec opt_get name xs = match xs with
        | [] -> None
        | (name', valu)::xs' -> if name = name' then Some valu else opt_get name xs' in
      let rec und_get name xs = match xs with
        | [] -> V.Undefined
        | (name', valu)::xs' -> if name = name' then valu else und_get name xs' in
      let attrsv = { V.code=(opt_get "code" valus);
                     V.proto=(und_get "proto" valus);
                     V.primval=(opt_get "prim" valus);
                     V.klass=kls;
                     V.extensible=ext; } in
      eval (C.AttrValClos (attrsv, env)) store k
    (* S.GetAttr (pos, pattr, obj, field)
     * Get the pattr for the obj's field using Ljs_eval's get_attr. *)
    | C.ExpClos (S.GetAttr (_, attr, obj, field), env), k ->
      eval (C.ExpClos (obj, env)) store (K.GetAttr (attr, field, k))
    | C.ValClos (obj_val, env), K.GetAttr (attr, field, k) ->
      eval (C.ExpClos (field, env)) store (K.GetAttr2 (attr, obj_val, k))
    | C.ValClos (field_val, env), K.GetAttr2 (attr, obj_val, k) ->
      eval (C.ValClos (L.get_attr store attr obj_val field_val, env)) store k
    (* S.SetAttr (pos, pattr, obj, field, next)
     * The pattr for the obj's field is set to next, using Ljs_eval's
     * set_attr. *)
    | C.ExpClos (S.SetAttr (_, pattr, obj, field, next), env), k ->
      eval (C.ExpClos (obj, env)) store (K.SetAttr (pattr, field, next, k))
    | C.ValClos (obj_val, env), K.SetAttr (pattr, field, next, k) ->
      eval (C.ExpClos (field, env)) store (K.SetAttr2 (pattr, next, obj_val, k))
    | C.ValClos (field_val, env), K.SetAttr2 (pattr, next, obj_val, k) ->
      eval (C.ExpClos (next, env)) store (K.SetAttr3 (pattr, obj_val, field_val, k))
    | C.ValClos (valu, env), K.SetAttr3 (pattr, obj_val, field_val, k) ->
      let b, store = L.set_attr store pattr obj_val field_val valu in
      eval (C.ValClos (D.bool b, env)) store k
    (* S.GetObjAttr (pos, oattr, obj)
     * Get the oattr for obj. *)
    | C.ExpClos (S.GetObjAttr (_, oattr, obj), env), k ->
      eval (C.ExpClos (obj, env)) store (K.GetObjAttr (oattr, k))
    | C.ValClos (obj_val, env), K.GetObjAttr (oattr, k) ->
      (match obj_val with
      | V.ObjLoc obj_loc ->
        let (attrs, _) = V.get_obj store obj_loc in
        eval (C.ValClos (L.get_obj_attr attrs oattr, env)) store k
      | _ -> failwith ("[interp] GetObjAttr got a non-object: " ^
                          (V.pretty_value obj_val)))
    (* S.SetObjAttr (pos, oattr, obj, next)
     * The oattr for obj is set to next. *)
    | C.ExpClos (S.SetObjAttr (_, oattr, obj, next), env), k ->
      eval (C.ExpClos (obj, env)) store (K.SetObjAttr (oattr, next, k))
    | C.ValClos (obj_val, env), K.SetObjAttr (oattr, next, k) ->
      eval (C.ExpClos (next, env)) store (K.SetObjAttr2 (oattr, obj_val, k))
    | C.ValClos (valu, env), K.SetObjAttr2 (oattr, obj_val, k) ->
      (match obj_val with
      | V.ObjLoc loc ->
        let (attrs, props) = V.get_obj store loc in
        let attrs' = match oattr, valu with
          | S.Proto, V.ObjLoc _
          | S.Proto, V.Null -> { attrs with V.proto=valu }
          | S.Proto, _ ->
            failwith ("[interp] Update proto failed: " ^
                      (V.pretty_value valu))
          | S.Extensible, V.True  -> { attrs with V.extensible=true }
          | S.Extensible, V.False -> { attrs with V.extensible=false }
          | S.Extensible, _ ->
            failwith ("[interp] Update extensible failed: " ^
                      (V.pretty_value valu))
          | S.Code, _ -> failwith "[interp] Can't update Code"
          | S.Primval, v -> { attrs with V.primval=Some v }
          | S.Klass, _ -> failwith "[interp] Can't update Klass" in
        eval (C.ValClos (valu, env)) (V.set_obj store loc (attrs', props)) k
      | _ -> failwith ("[interp] SetObjAttr got a non-object: " ^
                       (V.pretty_value obj_val)))
    (* S.GetField (pos, obj, field, body)
     * If the getter field in obj is evaluated and, is a data
     * property, continues with the value; if an accessor, evaluates
     * the getter with the body and the obj values as arguments. *)
    | C.ExpClos (S.GetField (p, obj, field, body), env), k ->
      eval (C.ExpClos (obj, env)) store (K.GetField (p, field, body, env, k))
    | C.ValClos (obj_val, env), K.GetField (p, field, body, env', k) ->
      eval (C.ExpClos (field, env)) store (K.GetField2 (p, body, obj_val, env', k))
    | C.ValClos (field_val, env), K.GetField2 (p, body, obj_val, env', k) ->
      eval (C.ExpClos (body, env)) store (K.GetField3 (p, obj_val, field_val, env', k))
    | C.ValClos (body_val, env), K.GetField3 (p, obj_val, field_val, env', k) ->
      (match (obj_val, field_val) with
      | (V.ObjLoc _, V.String s) ->
        let prop = L.get_prop p store obj_val s in
        (match prop with
        | Some (V.Data ({V.value=v;}, _, _)) -> eval (C.ValClos (v, env')) store k
        | Some (V.Accessor ({V.getter=g;},_,_)) ->
          let (body, env'', store') = (apply p store g [obj_val; body_val]) in
          eval (C.ExpClos (body, env'')) store' (K.GetField4 (env', k))
        | None -> eval (C.ValClos (V.Undefined, env')) store k)
      | _ -> failwith ("[interp] Get field didn't get an object and a string at "
                       ^ P.Pos.string_of_pos p ^ ". Instead, it got "
                       ^ V.pretty_value obj_val ^ " and "
                       ^ V.pretty_value field_val))
    | C.ValClos (acc_val, _), K.GetField4 (env, k) ->
      eval (C.ValClos (acc_val, env)) store k
    (* S.OwnFieldNames (pos, obj)
     * Create an object in the store with a map of indices to all
     * obj's properties and the count of that map. *)
    | C.ExpClos (S.OwnFieldNames (p, obj), env), k ->
      eval (C.ExpClos (obj, env)) store (K.OwnFieldNames k)
    | C.ValClos (obj_val, env), K.OwnFieldNames k ->
      (match obj_val with
      | V.ObjLoc loc ->
        let _, props = V.get_obj store loc in
        let add_name n x m =
          P.IdMap.add (string_of_int x) (V.Data ({ V.value = V.String n; V.writable = false; },
                                             false,
                                             false)) m in
        let names = P.IdMap.fold (fun k v l -> (k :: l)) props [] in
        let props = List.fold_right2 add_name names (P.iota (List.length names)) P.IdMap.empty in
        let d = float_of_int (List.length names) in
        let final_props =
          P.IdMap.add "length" (V.Data ({ V.value = V.Num d; V.writable = false; },
                                    false,
                                    false)) props in
        let (new_obj, store) = V.add_obj store (V.d_attrsv, final_props) in
        eval (C.ValClos (V.ObjLoc new_obj, env)) store k
      | _ -> failwith ("[interp] OwnFieldNames didn't get an object," ^
                          " got " ^ (V.pretty_value obj_val) ^ " instead."))
    (* S.DeleteField(pos, obj, field)
     * Deletes field from obj. *)
    | C.ExpClos (S.DeleteField (p, obj, field), env), k ->
      eval (C.ExpClos (obj, env)) store (K.DeleteField (p, field, k))
    | C.ValClos (obj_val, env), K.DeleteField (p, field, k) ->
      eval (C.ExpClos (field, env)) store (K.DeleteField2 (p, obj_val, k))
    | C.ValClos (field_val, env), K.DeleteField2 (p, obj_val, k) ->
      (match obj_val, field_val with
      | V.ObjLoc loc, V.String s ->
        (match V.get_obj store loc with
        | attrs, props ->
          (try match P.IdMap.find s props with
          | V.Data (_, _, true)
          | V.Accessor (_, _, true) ->
            let store' = V.set_obj store loc (attrs, P.IdMap.remove s props) in
            eval (C.ValClos (V.True, env)) store' k
          | _ -> eval (C.LobClos (V.Throw ([], V.String "unconfigurable-delete", store))) store k
           with Not_found -> eval (C.ValClos (V.False, env)) store k))
      | _ -> failwith ("[interp] Delete field didn't get an object and a string at "
                       ^ P.Pos.string_of_pos p
                       ^ ". Instead, it got "
                       ^ V.pretty_value obj_val
                       ^ " and "
                       ^ V.pretty_value field_val))
    (* S.SetField (pos, obj, field, next, body)
     * Sets obj's field to next by executing body. *)
    | C.ExpClos (S.SetField (p, obj, field, next, body), env), k ->
      eval (C.ExpClos (obj, env)) store (K.SetField  (p, field, next, body, env, k))
    | C.ValClos (obj_val, env), K.SetField  (p, field, next, body, env', k) ->
      eval (C.ExpClos (field, env)) store (K.SetField2 (p, next, body, obj_val, env', k))
    | C.ValClos (field_val, env), K.SetField2 (p, next, body, obj_val, env', k) ->
      eval (C.ExpClos (next, env)) store (K.SetField3 (p, body, obj_val, field_val, env', k))
    | C.ValClos (valu, env), K.SetField3 (p, body, obj_val, field_val, env', k) ->
      eval (C.ExpClos (body, env)) store (K.SetField4 (p, obj_val, field_val, valu, env', k))
    | C.ValClos (body_val, env), K.SetField4 (p, obj_val, field_val, valu, env', k) ->
      (match (obj_val, field_val) with
      | (V.ObjLoc loc, V.String s) ->
        let ({V.extensible=extensible;} as attrs, props) = V.get_obj store loc in
        let prop = L.get_prop p store obj_val s in
        let unwritable = (V.Throw ([], V.String "unwritable-field", store)) in
        (match prop with
        | Some (V.Data ({ V.writable = true; }, enum, config)) ->
          let (enum, config) =
            if (P.IdMap.mem s props)
            then (enum, config)  (* 8.12.5, step 3, changing the value of a field *)
            else (true, true) in (* 8.12.4, last step where inherited.[[writable]] is true *)
          let store = V.set_obj store loc
            (attrs,
             P.IdMap.add s (V.Data ({ V.value = valu; V.writable = true }, enum, config)) props) in
          eval (C.ValClos (valu, env)) store k
        | Some (V.Data _) -> eval (C.LobClos unwritable) store k
        | Some (V.Accessor ({ V.setter = V.Undefined; }, _, _)) ->
          eval (C.LobClos unwritable) store k
        | Some (V.Accessor ({ V.setter = setterv; }, _, _)) ->
          (* 8.12.5, step 5 *)
          let (body, env'', store') = apply p store setterv [obj_val; body_val] in
          eval (C.ExpClos (body, env'')) store' (K.SetField5 (env', k))
        | None ->
          (* 8.12.5, step 6 *)
          if extensible
          then
            let store = V.set_obj store loc
              (attrs,
               P.IdMap.add s (V.Data ({ V.value = valu; V.writable = true; }, true, true)) props) in
            eval (C.ValClos (valu, env)) store k
          else
            eval (C.ValClos (V.Undefined, env)) store k)
      | _ -> failwith ("[interp] Update field didn't get an object and a string"
                       ^ P.Pos.string_of_pos p ^ " : " ^ (V.pretty_value obj_val) ^
                         ", " ^ (V.pretty_value field_val)))
    | C.ValClos (acc_val, _), K.SetField5 (env, k) ->
      eval (C.ValClos (acc_val, env)) store k
    (* S.Op1 (pos, name, arg)
     * Evaluates a unary operation name on arg. *)
    | C.ExpClos (S.Op1 (_, name, arg), env), k ->
      eval (C.ExpClos (arg, env)) store (K.OpOne (name, k))
    | C.ValClos (arg_val, env), K.OpOne (name, k) ->
      eval (C.ValClos (D.op1 store name arg_val, env)) store k
    (* S.Op2 (pos, name, arg1, arg2)
     * Evaluates a binary operation name on arg1 and arg2. *)
    | C.ExpClos (S.Op2 (_, name, arg1, arg2), env), k ->
      eval (C.ExpClos (arg1, env)) store (K.OpTwo (name, arg2, k))
    | C.ValClos (arg1_val, env), K.OpTwo (name, arg2, k) ->
      eval (C.ExpClos (arg2, env)) store (K.OpTwo2 (name, arg1_val, k))
    | C.ValClos (arg2_val, env), K.OpTwo2 (name, arg1_val, k) ->
      eval (C.ValClos (D.op2 store name arg1_val arg2_val, env)) store k
    (* S.If (pos, pred, then, else)
     * Evaluates then if pred, else otherwise. *)
    | C.ExpClos (S.If (_, pred, than, elze), env), k ->
      eval (C.ExpClos (pred, env)) store (K.If (env, than, elze, k))
    | C.ValClos (pred_val, env), K.If (env', than, elze, k) ->
      if (pred_val = V.True)
      then eval (C.ExpClos (than, env')) store k
      else eval (C.ExpClos (elze, env')) store k
    (* S.App (pos, func, args)
     * Applies the body of func with the given args. *)
    | C.ExpClos (S.App (pos, func, args), env), k ->
      eval (C.ExpClos (func, env)) store (K.App (pos, env, args, k))
      (* special case for no arg apps *)
    | C.ValClos (func, env), K.App (pos, env', [], k) ->
      let (body, env'', store') = apply pos store func [] in
      eval (C.ExpClos (body, env'')) store' (K.App3 (env', k))
    | C.ValClos (func, env), K.App  (pos, env', expr::exprs, k) ->
      eval (C.ExpClos (expr, env')) store (K.App2 (pos, func, env', [] , exprs, k))
    | C.ValClos (arg_val, env), K.App2 (pos, func, env', vs, expr::exprs, k) ->
      eval (C.ExpClos (expr, env')) store (K.App2 (pos, func, env', arg_val::vs, exprs, k))
    | C.ValClos (arg_val,  env), K.App2 (pos, func, env', vs, [], k) ->
      let (body, env'', store') = apply pos store func (List.rev (arg_val::vs)) in
      eval (C.ExpClos (body, env'')) store' (K.App3 (env', k))
    | C.ValClos (body_val, _), K.App3 (env', k) ->
      eval (C.ValClos (body_val, env')) store k
    (* S.Seq (pos, left, right)
     * Evaluates left then right, continuing with right's value. *)
    | C.ExpClos (S.Seq (_, left, right), env), k ->
      eval (C.ExpClos (left, env)) store (K.Seq (right, k))
    | C.ValClos (_, env), K.Seq (right, k) ->
      eval (C.ExpClos (right, env)) store k
    (* S.Let (pos, name, expr, body)
     * Evaluates body with name bound to expr. *)
    | C.ExpClos (S.Let (_, name, expr, body), env), k ->
      eval (C.ExpClos (expr, env)) store (K.Let (name, body, k))
    | C.ValClos (v, env), K.Let (name, body, k) ->
      let (new_loc, store') = V.add_var store v in
      eval (C.ExpClos (body, P.IdMap.add name new_loc env)) store' (K.Let2 (env, k))
    | C.ValClos (v, env), K.Let2 (env', k) ->
      eval (C.ValClos (v, env')) store k
    (* S.Rec (pos, name, expr, body)
     * Evaluates body with name bound to expr, which may contain
     * recursive references to name. *)
    | C.ExpClos (S.Rec (_, name, expr, body), env), k ->
      let (new_loc, store') = V.add_var store V.Undefined in
      let env' = P.IdMap.add name new_loc env in
      eval (C.ExpClos (expr, env')) store' (K.Rec (new_loc, body, k))
    | C.ValClos (v, env), K.Rec (new_loc, body, k) ->
      eval (C.ExpClos (body, env)) (V.set_var store new_loc v) k
    (* S.Label (pos, name, expr)
     * Evaluates expr, catching any Breaks with the matching name. *)
    | C.ExpClos (S.Label (_, name, exp), env), k ->
      eval (C.ExpClos (exp, env)) store (K.Label (name, env, k))
    | C.ValClos (valu, env), K.Label (_, _, k) ->
      eval (C.ValClos (valu, env)) store k
    (* S.Break (pos, label, expr)
     * Breaks to label with expr as the value passed back. *)
    | C.ExpClos (S.Break (_, label, expr), env), k ->
      eval (C.ExpClos (expr, env)) store (K.Break (label, k))
    | C.ValClos (v, _), K.Break (label, k) ->
      eval (C.LobClos (V.Break ([], label, v, store))) store k
    | C.LobClos (V.Break (t, label, v, store')), K.Label (name, env, k) ->
      if name = label then eval (C.ValClos (v, env)) store k
      else eval (C.LobClos (V.Break (t, label, v, store'))) store k
    (* S.TryCatch (pos, body, catch)
     * Evaluates body, evaluating catch with the thrown value as an
     * argument if a Throw is lobbed up. *)
    | C.ExpClos (S.TryCatch (p, body, catch), env), k ->
      eval (C.ExpClos (body, env)) store (K.TryCatch (p, catch, env, k))
    | C.ValClos (body_val, env'), K.TryCatch (p, catch, env, k) ->
      eval (C.ValClos (body_val, env')) store k
    | C.LobClos (V.Throw (_, throw_val, store)), K.TryCatch (p, catch, env, k) ->
      eval (C.ExpClos (catch, env)) store (K.TryCatch2 (p, throw_val, env, k))
    | C.ValClos (catch_val, env'), K.TryCatch2 (p, throw_val, env, k) ->
      let (body, env'', store') = apply p store catch_val [throw_val] in
      eval (C.ExpClos (body, env'')) store' (K.TryCatch3 (env, k))
    | C.ValClos (catch_body_val, _), K.TryCatch3 (env, k) ->
      eval (C.ValClos (catch_body_val, env)) store k
    (* S.TryFinally (pos, body, fin)
     * Evaluates body then fin; if an exception is thrown from body
     * fin will be executed and the exn's store is updated. *)
    | C.ExpClos (S.TryFinally (_, body, fin), env), k ->
      eval (C.ExpClos (body, env)) store (K.TryFinally (fin, env, k))
    | C.ValClos (valu, env'), K.TryFinally (fin, env, k) ->
      eval (C.ExpClos (fin, env)) store k
    | C.LobClos except, K.TryFinally (fin, env, k) ->
      eval (C.ExpClos (fin, env)) store (K.TryFinally2 (except, env, k))
    | C.ValClos (_, _), K.TryFinally2 (except, env, k) ->
      (match except with
      | V.Throw (t, v, _) -> eval (C.LobClos (V.Throw (t, v, store))) store k
      | V.Break (t, l, v, _) -> eval (C.LobClos (V.Break (t, l, v, store))) store k
      | _ -> failwith "Try finally caught something other than a throw or break.")
    (* S.Throw (pos, expr)
     * Lobs expr up through the future konts. *)
    | C.ExpClos (S.Throw (_, expr), env), k ->
      eval (C.ExpClos (expr, env)) store (K.Throw k)
    | C.ValClos (valu, env), K.Throw k ->
      eval (C.LobClos (V.Throw ([], valu, store))) store k
    (* S.Eval (pos, str_expr, bindings)
     * Evaluates str_expr with the fields defined in the object
     * bindings added to the environment. *)
    | C.ValClos (str_val, env), K.Eval (pos, bindings, k) ->
      eval (C.ExpClos (bindings, env)) store (K.Eval2 (pos, str_val, k))
    | C.ValClos (bind_val, env), K.Eval2 (pos, str_val, k) ->
      (match str_val, bind_val with
      | V.String s, V.ObjLoc o ->
        let expr = desugar s in
        let env', store' = L.envstore_of_obj pos (V.get_obj store o) store in
        eval (C.ExpClos (expr, env')) store' (K.Eval3 k)
      | V.String _, _ -> L.interp_error pos "Non-object given to eval() for env"
      | v, _ -> eval (C.ValClos (v, env)) store k)
    | C.ValClos (valu, env), K.Eval3 k ->
      eval (C.ValClos (valu, env)) store k
    (* S.Hint (pos, str, expr)
     * Evaluates expr, continuing with a Snapshot if str is
     * "___takeS5Snapshot", or just continues with expr's val. *)
    | C.ExpClos (S.Hint (_, "___takeS5Snapshot", expr), env), k ->
      eval (C.ExpClos (expr, env)) store (K.Hint k)
    | C.ExpClos (S.Hint (_, _, expr), env), k ->
      eval (C.ExpClos (expr, env)) store k
    | C.ValClos (valu, env), K.Hint k ->
      eval (C.LobClos (V.Snapshot ([], valu, [], store))) store k
    (* control cases. TODO: make own exns, remove the store from them. *)
    | C.LobClos exn, K.Mt -> raise exn
    | C.LobClos (V.Break (exprs, l, v, s)), k ->
      eval (C.LobClos (V.Break (C.add_opt clo exprs C.exp_of, l, v, s))) store (K.shed k)
    | C.LobClos (V.Throw (exprs, v, s)), k ->
      eval (C.LobClos (V.Throw (C.add_opt clo exprs C.exp_of, v, s))) store (K.shed k)
    | C.LobClos (V.PrimErr (exprs, v)), k ->
      eval (C.LobClos (V.PrimErr (add_opt clo exprs C.exp_of, v))) store (K.shed k)
    | C.LobClos (V.Snapshot (exprs, v, envs, s)), k ->
      let snap = V.Snapshot (add_opt clo exprs C.exp_of, v, add_opt clo envs C.env_of, s) in
      eval (C.LobClos snap) store (K.shed k)
    | _ -> failwith "Encountered an unmatched eval_cesk case."
  end

(* Ljs_eval's continue_eval and eval_expr, with slight modifications *)
let continue_eval expr desugar print_trace env store =
  try
    Sys.catch_break true;
    let (v, store) = eval_cesk desugar (C.ExpClos (expr, env)) store K.Mt 0 in
    L.Answer ([], v, [], store)
  with
  | V.Snapshot (exprs, v, envs, store) ->
    L.Answer (exprs, v, envs, store)
  | V.Throw (t, v, store) ->
    let err_msg =
      match v with
      | V.ObjLoc loc -> begin match V.get_obj store loc with
        | _, props -> try match P.IdMap.find "%js-exn" props with
          | V.Data ({V.value=jserr}, _, _) -> PV.string_of_value jserr store
          | _ -> PV.string_of_value v store
          with Not_found -> PV.string_of_value v store
      end
      | v -> PV.string_of_value v store in
    L.err print_trace t (P.sprintf "Uncaught exception: %s\n" err_msg)
  | V.Break (p, l, v, _) -> failwith ("Broke to top of execution, missed label: " ^ l)
  | V.PrimErr (t, v) ->
    L.err print_trace t (P.sprintf "Uncaught error: %s\n" (V.pretty_value v))

let eval_expr expr desugar print_trace =
  continue_eval expr desugar print_trace P.IdMap.empty (Store.empty, Store.empty)
