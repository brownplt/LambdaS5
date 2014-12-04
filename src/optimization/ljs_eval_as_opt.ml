open Prelude
module S = Ljs_syntax
module V = Ljs_values
module U = Exp_util
module D = Ljs_delta


let interp_error pos message =
  raise (V.PrimErr ([], V.String ("[interp] (" ^ Pos.string_of_pos pos ^ ") " ^ message)))

let rec get_prop p store obj field =
  match obj with
    | V.Null -> None
    | V.ObjLoc loc -> begin match V.get_obj store loc with
      | { V.proto = pvalue; }, props ->
         try Some (IdMap.find field props)
         with Not_found -> get_prop p store pvalue field
      end
    | _ -> failwith (interp_error p 
           "get_prop on a non-object.  The expression was (get-prop " 
         ^ V.pretty_value obj 
         ^ " " ^ field ^ ")")


let rec pre_eval (exp : S.exp) env (store : V.store) : (V.value * V.store * S.exp) =
  let rec apply p store func args = match func with
    | V.Closure (env, xs, body) ->
      let alloc_arg argval argname (store, env) =
        let (new_loc, store) = V.add_var store argval in
        let env' = IdMap.add argname new_loc env in
        (store, env') in
      if (List.length args) != (List.length xs) then
        (*arity_mismatch_err p xs args*)
        failwith "arity_mismatch"
      else
        let (store, env) = (List.fold_right2 alloc_arg args xs (store, env)) in
        pre_eval body env store
    | V.ObjLoc loc -> begin match V.get_obj store loc with
        | ({ V.code = Some f }, _) -> apply p store f args
        | _ -> failwith "Applied an object without a code attribute"
    end
    | _ -> failwith "applied non-function"
  in 
  match exp with 
  | S.Undefined _ -> V.Undefined, store, exp
  | S.Null _ -> V.Null, store, exp
  | S.String (_, s) -> V.String s, store, exp
  | S.Num (_, n) -> V.Num n, store, exp
  | S.True _ -> V.True, store, exp
  | S.False _ -> V.False, store, exp
  | S.Id (_, x) -> begin
      try
        V.get_var store (IdMap.find x env), store, exp
      with Not_found ->
        failwith ("Unbound identifier" ^ x)
    end 
  | S.SetBang (p,x,e) -> begin
      try 
        let loc = IdMap.find x env in
        let (new_val, store, new_e) = pre_eval e env store in
        let store = V.set_var store loc new_val in
        new_val, store, S.SetBang (p, x, new_e)
      with Not_found ->
        failwith ("Unbound " ^ x ^ "in set!")
    end 
  | S.Let (p, x, e, body) ->
      let (e_val, store, new_e) = pre_eval e env store in
      let (new_loc, store) = V.add_var store e_val in
      let (body_val, store, new_body) = 
        pre_eval body (IdMap.add x new_loc env) store in
      body_val, store, S.Let (p, x, new_e, new_body)
  | S.If (p, c, t, e) ->
    let  (c_val, store, _) = pre_eval c env store in
    if (c_val = V.True) then
      pre_eval t env store 
    else 
      pre_eval e env store
  | S.Op1 (p, op, e) ->
    let (e_val, store, new_e) = pre_eval e env store in
    let result = D.op1 store op e_val in
    (*let result_exp = U.value_to_exp result p in*)
    result, store, S.Op1 (p, op, new_e)
  | S.Op2 (p, op, e1, e2) -> 
      let (e1_val, store, new_e1) = pre_eval e1 env store in
      let (e2_val, store, new_e2) = pre_eval e2 env store in
      let result = D.op2 store op e1_val e2_val in
      result, store, S.Op2 (p, op, new_e1, new_e2)
  | S.Seq (p, e1, e2) -> 
      let (_, store, new_e1) = pre_eval e1 env store in
      let (e2_val, store, new_e2) = pre_eval e2 env store in
      e2_val, store, S.Seq (p, new_e1, new_e2)

  | S.Throw (p, e) -> 
    let (v, s, _) = pre_eval e env store in
    raise (V.Throw ([], v, s))

  | S.Lambda (p, xs, e) ->
    (* Only close over the variables that the function body might reference. *)
    let free_vars = S.free_vars e in
    let filtered_env =
      IdMap.filter (fun var _ -> IdSet.mem var free_vars) env in
    V.Closure (filtered_env, xs, e), store, exp

  | S.Object (p, attrs, props) -> 
    let { S.primval = vexp;
          S.proto = protoexp;
          S.code = codexp;
          S.extensible = ext;
          S.klass = kls; } = attrs in
    let opt_lift (value, store, e) = (Some value, store, Some e) in
    let primval, store, new_primval = match vexp with
      | Some vexp -> opt_lift (pre_eval vexp env store)
      | None -> None, store, None
    in
    let proto, store, new_proto = match protoexp with 
      | Some pexp -> 
        let (value, store, new_proto) = pre_eval pexp env store in
        (value, store, Some new_proto)
      | None -> V.Undefined, store, None
    in
    let code, store, new_code = match codexp with
        | Some cexp -> opt_lift (pre_eval cexp env store)
        | None -> None, store, None
    in
    let attrs = {
      S.code=new_code; S.proto=new_proto; S.primval=new_primval;
      S.klass=kls; S.extensible=ext;
    } in
    let attrsv = {
      V.code=code; V.proto=proto; V.primval=primval;
      V.klass=kls; V.extensible=ext;
    } in
    let eval_prop prop store = match prop with
      | S.Data ({ S.value = vexp; S.writable = w; }, enum, config) ->
        let vexp, store, new_value = pre_eval vexp env store in
        V.Data ({ V.value = vexp; writable = w; }, enum, config), store,
        S.Data ({ S.value = new_value; writable = w; }, enum, config)
      | S.Accessor ({ S.getter = ge; S.setter = se; }, enum, config) ->
        let gv, store, new_getter = pre_eval ge env store in
        let sv, store, new_setter = pre_eval se env store in
        V.Accessor ({ V.getter = gv; V.setter = sv}, enum, config), store,
        S.Accessor ({ S.getter = new_getter; S.setter = new_setter}, enum, config)
    in
    let eval_prop (m, store) (name, prop) = 
      let propv, store, _ = eval_prop prop store in
      IdMap.add name propv m, store
    in
    let propsv, store =
      fold_left eval_prop (IdMap.empty, store) props in
    let obj_loc, store = V.add_obj store (attrsv, propsv) in
    V.ObjLoc obj_loc, store, exp
  | S.GetField (p, obj, f, args) ->
      let (obj_value, store, new_obj) = pre_eval obj env store in
      let (f_value, store, new_f) = pre_eval f env store in 
      let (args_value, store, new_args) = pre_eval args env store in begin
        match (obj_value, f_value) with
          | (V.ObjLoc _, V.String s) ->
            let prop = get_prop p store obj_value s in
            begin match prop with
              | Some (V.Data ({V.value=v;}, _, _)) -> v, store, exp
              | Some (V.Accessor ({V.getter=g;},_,_)) ->
                apply p store g [obj_value; args_value]
              | None -> V.Undefined, store, exp
            end
          | _ -> failwith ("[interp] Get field didn't get an object and a string at " 
                 ^ Pos.string_of_pos p 
                 ^ ". Instead, it got " 
                 ^ V.pretty_value obj_value 
                 ^ " and " 
                 ^ V.pretty_value f_value)
      end
  | S.SetField (p, obj, f, v, args) ->
      let (obj_value, store, new_obj) = pre_eval obj env store in
      let (f_value, store, new_f) = pre_eval f env store in
      let (v_value, store, new_v) = pre_eval v env store in
      let (args_value, store, new_args) = pre_eval args env store in 
      begin
        match (obj_value, f_value) with
          | (V.ObjLoc loc, V.String s) ->
            let ({V.extensible=extensible;} as attrs, props) =
              V.get_obj store loc in
            let prop = get_prop p store obj_value s in
            let unwritable = (V.Throw ([],
                                       V.String "unwritable-field",
                                       store
                                      )) 
            in
            begin match prop with
              | Some (V.Data ({ V.writable = true; }, enum, config)) ->
                let (enum, config) = 
                  if (IdMap.mem s props)
                  then (enum, config) (* 8.12.5, step 3, changing the value of a field *)
                  else (true, true) in (* 8.12.4, last step where inherited.[[writable]] is true *)
                let store = V.set_obj store loc 
                    (attrs,
                      IdMap.add s
                        (V.Data ({ V.value = v_value; V.writable = true },
                               enum, config))
                        props) in
                v_value, store, new_v
              | Some (V.Data _) -> raise unwritable
              | Some (V.Accessor ({ V.setter = V.Undefined; }, _, _)) ->
                raise unwritable
              | Some (V.Accessor ({ V.setter = setterv; }, _, _)) -> 
                (* 8.12.5, step 5 *)
                apply p store setterv [obj_value; args_value]
              | None ->
                (* 8.12.5, step 6 *)
                if extensible
                then
                  let store = V.set_obj store loc 
                      (attrs,
                        IdMap.add s 
                          (V.Data ({ V.value = v_value; V.writable = true; },
                                 true, true))
                          props) in
                  v_value, store, new_v
                else
                  V.Undefined, store, new_v (* TODO: Check error in case of non-extensible *)
            end
          | _ -> failwith ("[interp] Update field didn't get an object and a string" 
                           ^ Pos.string_of_pos p ^ " : " ^ (V.pretty_value obj_value) ^ 
                             ", " ^ (V.pretty_value f_value))
      end
  | S.App (p, func, args) -> 
      let (func_value, store, new_func) = eval func env store in
      let (args_values, store, new_args) =
        fold_left (fun (vals, store) e ->
            let (newval, store, new_arg) = pre_eval e env store in
            (newval::vals, store))
          ([], store) args in
      apply p store func_value (List.rev args_values)

  | S.Label (_,_,_)
  | S.Object (_,_,_) 
  | S.GetObjAttr (_, _, _)
  | S.SetAttr (_,_,_,_,_)
  | S.GetAttr (_,_,_,_)
  | S.SetObjAttr (_,_,_,_)
  | S.DeleteField (_, _, _) 
  | S.OwnFieldNames (_,_)
  | S.Rec (_,_,_,_)
  | S.Break (_,_,_)
  | S.TryCatch (_,_,_)
  | S.TryFinally (_,_,_)
  | S.Hint (_,_,_)
      -> failwith "not implemented"


let preprocess (e : S.exp) : S.exp =
  let env = IdMap.empty in
  let store = (Store.empty, Store.empty) in
  let (_, _, new_e) = pre_eval e env store in
  new_e
