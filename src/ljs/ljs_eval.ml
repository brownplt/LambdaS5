open Prelude
module S = Ljs_syntax
open Format
open Ljs
open Ljs_values
open Ljs_delta
open Ljs_pretty
open Unix
open SpiderMonkey
open Exprjs_to_ljs
open Js_to_exprjs
open Str

let bool b = match b with
  | true -> True
  | false -> False

let unbool b = match b with
  | True -> true
  | False -> false
  | _ -> failwith ("tried to unbool a non-bool" ^ (pretty_value b))

let interp_error pos message =
  "[interp] (" ^ string_of_position pos ^ ") " ^ message

let apply p store func args = match func with
  | Closure c -> c args store
  | ObjLoc loc -> begin match get_obj store loc with
      | ({ code = Some (Closure c) }, _) -> c args store
      | _ -> failwith "Applied an object without a code attribute"
  end
  | _ -> failwith (interp_error p 
                     ("Applied non-function, was actually " ^ 
                         pretty_value func))

let rec get_prop p store obj field =
  match obj with
    | Null -> None
    | ObjLoc loc -> begin match get_obj store loc with
      | { proto = pvalue; }, props ->
         try Some (IdMap.find field props)
         with Not_found -> get_prop p store pvalue field
      end
    | _ -> failwith (interp_error p 
           "get_prop on a non-object.  The expression was (get-prop " 
         ^ pretty_value obj 
         ^ " " ^ field ^ ")")

let get_obj_attr attrs attr = match attrs, attr with
  | { proto=proto }, S.Proto -> proto
  | { extensible=extensible} , S.Extensible -> bool extensible
  | { code=Some code}, S.Code -> code
  | { code=None}, S.Code -> Null
  | { primval=Some primval}, S.Primval -> primval
  | { primval=None}, S.Primval ->
      failwith "[interp] Got Primval attr of None"
  | { klass=klass }, S.Klass -> String klass


let rec get_attr store attr obj field = match obj, field with
  | ObjLoc loc, String s -> let (attrs, props) = get_obj store loc in
      if (not (IdMap.mem s props)) then
        undef
      else
        begin match (IdMap.find s props), attr with 
          | Data (_, _, config), S.Config
          | Accessor (_, _, config), S.Config -> bool config
          | Data (_, enum, _), S.Enum
          | Accessor (_, enum, _), S.Enum -> bool enum
          | Data ({ writable = b; }, _, _), S.Writable -> bool b
          | Data ({ value = v; }, _, _), S.Value -> v
          | Accessor ({ getter = gv; }, _, _), S.Getter -> gv
          | Accessor ({ setter = sv; }, _, _), S.Setter -> sv
          | _ -> failwith "bad access of attribute"
        end
  | _ -> failwith ("[interp] get-attr didn't get an object and a string.")

(* 
   The goal here is to maintain a few invariants (implied by 8.12.9
   and 8.10.5), while keeping things simple from a semantic
   standpoint.  The errors from 8.12.9 and 8.10.5 can be defined in
   the environment and enforced that way.  The invariants here make it
   more obvious that the semantics can't go wrong.  In particular, a
   property

   1.  Has to be either an accessor or a data property, and;

   2.  Can't change attributes when Config is false, except for 
       a. Value, which checks Writable
       b. Writable, which can change true->false
*)
let rec set_attr (store : store) attr obj field newval = match obj, field with
  | ObjLoc loc, String f_str -> begin match get_obj store loc with
      | ({ extensible = ext; } as attrsv, props) ->
        if not (IdMap.mem f_str props) then
          if ext then 
            let newprop = match attr with
              | S.Getter -> 
                Accessor ({ getter = newval; setter = Undefined; }, 
                          false, false)
              | S.Setter -> 
                Accessor ({ getter = Undefined; setter = newval; }, 
                          false, false)
              | S.Value -> 
                Data ({ value = newval; writable = false; }, false, false)
              | S.Writable ->
                Data ({ value = Undefined; writable = unbool newval },
                      false, false) 
              | S.Enum ->
                Data ({ value = Undefined; writable = false },
                      unbool newval, true) 
              | S.Config ->
                Data ({ value = Undefined; writable = false },
                      true, unbool newval) in
            let store = set_obj store loc
                  (attrsv, IdMap.add f_str newprop props) in
            true, store
          else
            failwith "[interp] Extending inextensible object ."
        else
        (* 8.12.9: "If a field is absent, then its value is considered
        to be false" -- we ensure that fields are present and
        (and false, if they would have been absent). *)
          let newprop = match (IdMap.find f_str props), attr, newval with
            (* S.Writable true -> false when configurable is false *)
            | Data ({ writable = true } as d, enum, config), S.Writable, new_w -> 
              Data ({ d with writable = unbool new_w }, enum, config)
            | Data (d, enum, true), S.Writable, new_w ->
              Data ({ d with writable = unbool new_w }, enum, true)
            (* Updating values only checks writable *)
            | Data ({ writable = true } as d, enum, config), S.Value, v ->
              Data ({ d with value = v }, enum, config)
            (* If we had a data property, update it to an accessor *)
            | Data (d, enum, true), S.Setter, setterv ->
              Accessor ({ getter = Undefined; setter = setterv }, enum, true)
            | Data (d, enum, true), S.Getter, getterv ->
              Accessor ({ getter = getterv; setter = Undefined }, enum, true)
            (* Accessors can update their getter and setter properties *)
            | Accessor (a, enum, true), S.Getter, getterv ->
              Accessor ({ a with getter = getterv }, enum, true)
            | Accessor (a, enum, true), S.Setter, setterv ->
              Accessor ({ a with setter = setterv }, enum, true)
            (* An accessor can be changed into a data property *)
            | Accessor (a, enum, true), S.Value, v ->
              Data ({ value = v; writable = false; }, enum, true)
            | Accessor (a, enum, true), S.Writable, w ->
              Data ({ value = Undefined; writable = unbool w; }, enum, true)
            (* enumerable and configurable need configurable=true *)
            | Data (d, _, true), S.Enum, new_enum ->
              Data (d, unbool new_enum, true)
            | Data (d, enum, true), S.Config, new_config ->
              Data (d, enum, unbool new_config)
            | Data (d, enum, false), S.Config, False -> 
              Data (d, enum, false)
            | Accessor (a, enum, true), S.Config, new_config ->
              Accessor (a, enum, unbool new_config)
            | Accessor (a, enum, true), S.Enum, new_enum ->
              Accessor (a, unbool new_enum, true)
            | Accessor (a, enum, false), S.Config, False ->
              Accessor (a, enum, false)
            | _ -> raise (PrimErr ([], String ("[interp] bad property set "
                    ^ (pretty_value obj) ^ " " ^ f_str ^ " " ^
                    (S.string_of_attr attr) ^ " " ^ (pretty_value newval))))
        in begin
            let store = set_obj store loc 
              (attrsv, IdMap.add f_str newprop props) in
            true, store
        end
  end
  | _ -> failwith ("[interp] set-attr didn't get an object and a string")


let rec eval jsonPath exp env (store : store) : (value * store) =
  let eval exp env store =
    begin try eval jsonPath exp env store
      with 
      | Break (exprs, l, v, s) ->
        raise (Break (exp::exprs, l, v, s))
      | Throw (exprs, v, s) ->
        raise (Throw (exp::exprs, v, s))
      | PrimErr (exprs, v) ->
        raise (PrimErr (exp::exprs, v))
    end in
  match exp with
  | S.Hint (_, _, e) -> eval e env store
  | S.Undefined _ -> Undefined, store
  | S.Null _ -> Null, store
  | S.String (_, s) -> String s, store
  | S.Num (_, n) -> Num n, store
  | S.True _ -> True, store
  | S.False _ -> False, store
  | S.Id (p, x) -> begin
      try
        (get_var store (IdMap.find x env), store)
      with Not_found ->
        failwith ("[interp] Unbound identifier: " ^ x ^ " in identifier lookup at " ^
                    (string_of_position p))
    end
  | S.SetBang (p, x, e) -> begin
      try
        let loc = IdMap.find x env in
        let (new_val, store) = eval e env store in
        let store = set_var store loc new_val in
        new_val, store
      with Not_found ->
        failwith ("[interp] Unbound identifier: " ^ x ^ " in set! at " ^
                    (string_of_position p))
    end
  | S.Object (p, attrs, props) -> 
    let { S.primval = vexp;
          S.proto = protoexp;
          S.code = codexp;
          S.extensible = ext;
          S.klass = kls; } = attrs in
    let opt_lift (value, store) = (Some value, store) in
    let primval, store = match vexp with
      | Some vexp -> opt_lift (eval vexp env store)
      | None -> None, store
    in
    let proto, store = match protoexp with 
      | Some pexp -> eval pexp env store
      | None -> Undefined, store
    in
    let code, store = match codexp with
        | Some cexp -> opt_lift (eval cexp env store)
        | None -> None, store
    in
    let attrsv = {
      code=code; proto=proto; primval=primval;
      klass=kls; extensible=ext;
    } in
    let eval_prop prop store = match prop with
      | S.Data ({ S.value = vexp; S.writable = w; }, enum, config) ->
        let vexp, store = eval vexp env store in
        Data ({ value = vexp; writable = w; }, enum, config), store
      | S.Accessor ({ S.getter = ge; S.setter = se; }, enum, config) ->
        let gv, store = eval ge env store in
        let sv, store = eval se env store in
        Accessor ({ getter = gv; setter = sv}, enum, config), store
    in
      let eval_prop (m, store) (name, prop) = 
        let propv, store = eval_prop prop store in
          IdMap.add name propv m, store in
      let propsv, store =
        fold_left eval_prop (IdMap.empty, store) props in
      let obj_loc, store = add_obj store (attrsv, propsv) in
      ObjLoc obj_loc, store
    (* 8.12.4, 8.12.5 *)
  | S.SetField (p, obj, f, v, args) ->
      let (obj_value, store) = eval obj env store in
      let (f_value, store) = eval f env store in
      let (v_value, store) = eval v env store in
      let (args_value, store) = eval args env store in begin
        match (obj_value, f_value) with
          | (ObjLoc loc, String s) ->
            let ({extensible=extensible;} as attrs, props) =
              get_obj store loc in
            let prop = get_prop p store obj_value s in
            begin match prop with
              | Some (Data ({ writable = true; }, enum, config)) ->
                let (enum, config) = 
                  if (IdMap.mem s props)
                  then (enum, config) (* 8.12.5, step 3, changing the value of a field *)
                  else (true, true) in (* 8.12.4, last step where inherited.[[writable]] is true *)
                let store = set_obj store loc 
                    (attrs,
                      IdMap.add s
                        (Data ({ value = v_value; writable = true },
                               enum, config))
                        props) in
                v_value, store
              | Some (Data _) -> raise (PrimErr ([], String ("Field " ^ s ^ " not writable!")))
              | Some (Accessor ({ setter = setterv; }, enum, config)) ->
                (* 8.12.5, step 5 *)
                apply p store setterv [obj_value; args_value]
              | None ->
                (* 8.12.5, step 6 *)
                if extensible
                then
                  let store = set_obj store loc 
                      (attrs,
                        IdMap.add s 
                          (Data ({ value = v_value; writable = true; },
                                 true, true))
                          props) in
                  v_value, store
                else
                  Undefined, store (* TODO: Check error in case of non-extensible *)
            end
          | _ -> failwith ("[interp] Update field didn't get an object and a string" 
                           ^ string_of_position p ^ " : " ^ (pretty_value obj_value) ^ 
                             ", " ^ (pretty_value f_value))
      end
  | S.GetField (p, obj, f, args) ->
      let (obj_value, store) = eval obj env store in
      let (f_value, store) = eval f env store in 
      let (args_value, store) = eval args env store in begin
        match (obj_value, f_value) with
          | (ObjLoc _, String s) ->
            let prop = get_prop p store obj_value s in
            begin match prop with
              | Some (Data ({value=v;}, _, _)) -> v, store
              | Some (Accessor ({getter=g;},_,_)) ->
                apply p store g [obj_value; args_value]
              | None -> Undefined, store
            end
          | _ -> failwith ("[interp] Get field didn't get an object and a string at " 
                 ^ string_of_position p 
                 ^ ". Instead, it got " 
                 ^ pretty_value obj_value 
                 ^ " and " 
                 ^ pretty_value f_value)
      end
  | S.DeleteField (p, obj, f) ->
      let (obj_val, store) = eval obj env store in
      let (f_val, store) = eval f env store in begin
        match (obj_val, f_val) with
          | (ObjLoc loc, String s) -> 
            begin match get_obj store loc with
              | (attrs, props) -> begin try
                match IdMap.find s props with
                  | Data (_, _, true) 
                  | Accessor (_, _, true) ->
                    let store = set_obj store loc
                      (attrs, IdMap.remove s props) in
                    True, store
                  | _ -> False, store
                with Not_found -> False, store
              end
            end
          | _ -> failwith ("[interp] Delete field didn't get an object and a string at " 
                           ^ string_of_position p 
                           ^ ". Instead, it got " 
                           ^ pretty_value obj_val
                           ^ " and " 
                           ^ pretty_value f_val)
        end
  | S.GetAttr (p, attr, obj, field) ->
      let (obj_val, store) = eval obj env store in
      let (f_val, store) = eval field env store in
        get_attr store attr obj_val f_val, store
  | S.SetAttr (p, attr, obj, field, newval) ->
      let (obj_val, store) = eval obj env store in
      let (f_val, store) = eval field env store in
      let (v_val, store) = eval newval env store in
      let b, store = set_attr store attr obj_val f_val v_val in
      bool b, store
  | S.GetObjAttr (p, oattr, obj) ->
      let (obj_val, store) = eval obj env store in
      begin match obj_val with
        | ObjLoc loc ->
            let (attrs, _) = get_obj store loc in
            get_obj_attr attrs oattr, store
        | _ -> failwith ("[interp] GetObjAttr got a non-object: " ^
                          (pretty_value obj_val))
      end
  | S.SetObjAttr (p, oattr, obj, attre) ->
      let (obj_val, store) = eval obj env store in
      let (attrv, store) = eval attre env store in
      begin match obj_val with
        | ObjLoc loc ->
            let (attrs, props) = get_obj store loc in
            let attrs' = match oattr, attrv with
              | S.Proto, ObjLoc _
              | S.Proto, Null -> { attrs with proto=attrv }
              | S.Proto, _ ->
                  failwith ("[interp] Update proto failed: " ^
                            (pretty_value attrv))
              | S.Extensible, True -> { attrs with extensible=true }
              | S.Extensible, False -> { attrs with extensible=false }
              | S.Extensible, _ ->
                  failwith ("[interp] Update extensible failed: " ^
                            (pretty_value attrv))
              | S.Code, _ -> failwith "[interp] Can't update Code"
              | S.Primval, _ -> failwith "[interp] Can't update Primval"
              | S.Klass, _ -> failwith "[interp] Can't update Klass" in
            attrv, set_obj store loc (attrs', props)
        | _ -> failwith ("[interp] SetObjAttr got a non-object: " ^
                          (pretty_value obj_val))
      end
  | S.OwnFieldNames (p, obj) ->
      let (obj_val, store) = eval obj env store in
      begin match obj_val with
        | ObjLoc loc ->
          let _, props = get_obj store loc in
          let add_name n x m = 
            IdMap.add (string_of_int x) 
              (Data ({ value = String n; writable = false; }, false, false)) 
              m in
          let namelist = IdMap.fold (fun k v l -> (k :: l)) props [] in
          let props = 
            List.fold_right2 add_name namelist
              (iota (List.length namelist)) IdMap.empty
          in
          let d = (float_of_int (List.length namelist)) in
          let final_props = 
            IdMap.add "length" 
              (Data ({ value = Num d; writable = false; }, false, false))
              props
          in
          let (new_obj, store) = add_obj store (d_attrsv, final_props) in
          ObjLoc new_obj, store
        | _ -> failwith ("[interp] OwnFieldNames didn't get an object," ^
                  " got " ^ (pretty_value obj_val) ^ " instead.")
      end
  | S.Op1 (p, op, e) ->
      let (e_val, store) = eval e env store in
      op1 store op e_val, store
  | S.Op2 (p, op, e1, e2) -> 
      let (e1_val, store) = eval e1 env store in
      let (e2_val, store) = eval e2 env store in
      op2 store op e1_val e2_val, store
  | S.If (p, c, t, e) ->
      let (c_val, store) = eval c env store in
        if (c_val = True)
        then eval t env store
        else eval e env store
  | S.App (p, func, args) -> 
      let (func_value, store) = eval func env store in
      let (args_values, store) =
        fold_left (fun (vals, store) e ->
            let (newval, store) = eval e env store in
            (newval::vals, store))
          ([], store) args in
      apply p store func_value (List.rev args_values)
  | S.Seq (p, e1, e2) -> 
      let (_, store) = eval e1 env store in
      eval e2 env store
  | S.Let (p, x, e, body) ->
      let (e_val, store) = eval e env store in
      let (new_loc, store) = add_var store e_val in
      eval body (IdMap.add x new_loc env) store
  | S.Rec (p, x, e, body) ->
      let (new_loc, store) = add_var store Undefined in
      let env' = (IdMap.add x new_loc env) in
      let (ev_val, store) = eval e env' store in
      eval body env' (set_var store new_loc ev_val)
  | S.Label (p, l, e) ->
      begin
        try
          eval e env store
        with Break (t, l', v, store) ->
          if l = l' then (v, store)
          else raise (Break (t, l', v, store))
      end
  | S.Break (p, l, e) ->
      let v, store = eval e env store in
      raise (Break ([], l, v, store))
  | S.TryCatch (p, body, catch) -> begin
      try
        eval body env store
      with Throw (_, v, store) ->
        let catchv, store = eval catch env store in
        apply p store catchv [v]
    end
  | S.TryFinally (p, body, fin) -> begin
      try
        let (_, store) = eval body env store in
        eval fin env store
      with
        | Throw (t, v, store) ->
          let (_, store) = eval fin env store in
          raise (Throw (t, v, store))
        | Break (t, l, v, store) ->
          let (_, store) = eval fin env store in
          raise (Break (t, l, v, store))
      end
  | S.Throw (p, e) -> let (v, s) = eval e env store in
    raise (Throw ([], v, s))
  | S.Lambda (p, xs, e) -> 
    let alloc_arg argval argname (store, env) =
      let (new_loc, store) = add_var store argval in
      let env' = IdMap.add argname new_loc env in
      (store, env') in
    let closure args store =
      if (List.length args) != (List.length xs) then
        arity_mismatch_err p xs args
      else
        let (store, env) = (List.fold_right2 alloc_arg args xs (store, env)) in
        eval e env store in
    Closure closure, store
  | S.Eval (p, e) ->
    begin match eval e env store with
      | String s, store -> eval_op s env store jsonPath
      | v, store -> v, store
    end

and arity_mismatch_err p xs args = failwith ("Arity mismatch, supplied " ^ string_of_int (List.length args) ^ " arguments and expected " ^ string_of_int (List.length xs) ^ " at " ^ string_of_position p ^ ". Arg names were: " ^ (List.fold_right (^) (map (fun s -> " " ^ s ^ " ") xs) "") ^ ". Values were: " ^ (List.fold_right (^) (map (fun v -> " " ^ pretty_value v ^ " ") args) ""))

(* This function is exactly as ridiculous as you think it is.  We read,
   parse, desugar, and evaluate the string, storing it to temp files along
   the way.  We make no claims about encoding issues that may arise from
   the filesystem.  Thankfully, JavaScript is single-threaded, so using
   only a single file works out. 

   TODO(joe): I have no idea what happens on windows. *)
and eval_op str env store jsonPath = 
  let outchan = open_out "/tmp/curr_eval.js" in
  output_string outchan str;
  close_out outchan;
  let cmdstring = 
    (sprintf "%s /tmp/curr_eval.js 1> /tmp/curr_eval.json 2> /tmp/curr_evalerr.json" jsonPath) in
  ignore (system cmdstring);
  let inchan = open_in "/tmp/curr_evalerr.json" in
  let buf = String.create (in_channel_length inchan) in
  really_input inchan buf 0 (in_channel_length inchan);
  let json_err = regexp (quote "SyntaxError") in
  begin try
    ignore (search_forward json_err buf 0);
    raise (Throw ([], String "EvalError", store))
    with Not_found -> ()
  end;
  let ast =
    parse_spidermonkey (open_in "/tmp/curr_eval.json") "/tmp/curr_eval.json" in
  let (used_ids, exprjsd) = 
    try
      js_to_exprjs ast (Exprjs_syntax.IdExpr (dummy_pos, "%global"))
    with ParseError _ -> raise (Throw ([], String "EvalError", store))
    in
  let desugard = exprjs_to_ljs used_ids exprjsd in
  if (IdMap.mem "%global" env) then
    (Ljs_pretty.exp desugard std_formatter; print_newline ();
     eval jsonPath desugard env store (* TODO: which env? *))
  else
    (failwith "no global")

let rec eval_expr expr jsonPath = try
  eval jsonPath expr IdMap.empty (Store.empty, Store.empty)
with
  | Throw (t, v, store) ->
      let err_msg = 
        match v with
          | ObjLoc loc ->
              let (attrs, props) = get_obj store loc in
                begin try
                  match IdMap.find "message" props with
                    | Data ({ value = msg_val; }, _, _) ->
                        (pretty_value msg_val)
                    | _ -> string_of_value v store
                with Not_found -> string_of_value v store
                end
          | v -> (pretty_value v) in
        printf "%s\nUncaught exception: %s\n" (string_stack_trace t) err_msg;
        failwith "Uncaught exception"
  | Break (p, l, v, _) -> failwith ("Broke to top of execution, missed label: " ^ l)
  | PrimErr (t, v) ->
      printf "%s\nUncaught error: %s\n" (string_stack_trace t) (pretty_value v);
      failwith "Uncaught error"

