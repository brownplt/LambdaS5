open Ljs_delta
open Ljs_pretty
open Ljs_pretty_value
open Ljs_values
open Prelude

module S = Ljs_syntax
module K = Ljs_kont
module L = Ljs_eval

let interp_error pos message =
  raise (PrimErr ([], String ("[interp] (" ^ Pos.string_of_pos pos ^ ") " ^ message)))

(* Machine-specific closures *)
type closure =
  | ExpClosure of S.exp * env
  | ValClosure of value * env
  | AEClosure of S.attrs * env
  | AVClosure of attrsv * env
  | PEClosure of (string * S.prop) * env
  | PVClosure of (string * propv) * env ;;

let exp_of clos = match clos with
  | ExpClosure (expr, _) -> Some expr
  | _ -> None
let env_of clos = match clos with
  | ExpClosure (_, env) -> Some env
  | _ -> None
let env_of_any clos = match clos with
  | ExpClosure (_, env) -> env
  | ValClosure (_, env) -> env
  | AEClosure  (_, env) -> env
  | AVClosure  (_, env) -> env
  | PEClosure  (_, env) -> env
  | PVClosure  (_, env) -> env
let add_opt clos xs f = match f clos with
  | Some x -> x::xs
  | None -> xs
let rec string_of_expr expr = match expr with
  | S.Null _ -> "null"
  | S.Undefined _ -> "undef"
  | S.String (_, s) -> "\""^s^"\""
  | S.Num (_, f) -> string_of_float f
  | S.True _ -> "true"
  | S.False _ -> "false"
  | S.Id (_, name) -> "id(\""^name^"\")"
  | S.Object (_, _, _) -> "objlit"
  | S.GetAttr (_, _, obj, field) -> "getattr(_,_, "^(string_of_expr obj)^", "^(string_of_expr field)^")"
  | S.SetAttr (_,_,obj, field, newv) -> "setattr(_,_, "^(string_of_expr obj)^", "^(string_of_expr field)^", "^(string_of_expr newv)^")"
  | S.GetObjAttr (_,_,obj) -> "getobjattr(_,_, "^(string_of_expr obj)^")"
  | S.SetObjAttr (_,_,_,obj) -> "setobjattr(_,_,_, "^(string_of_expr obj)^")"
  | S.GetField (_,_,obj,field) -> "getfield(_,_, "^(string_of_expr obj)^", "^(string_of_expr field)^")"
  | S.SetField (_,_,obj,field,newv) -> "setfield(_,_, "^(string_of_expr obj)^", "^(string_of_expr field)^", "^(string_of_expr newv)^")"
  | S.DeleteField (_,obj,field) -> "deletefield(_, "^(string_of_expr obj)^", "^(string_of_expr field)^")"
  | S.OwnFieldNames (_,obj) -> "ownfieldnames(_, "^(string_of_expr obj)^")"
  | S.SetBang (_,name,valu) -> "setbang(_, "^name^", "^(string_of_expr valu)^")"
  | S.Op1 (_,op,arg) -> "op1(_, "^op^", "^(string_of_expr arg)^")"
  | S.Op2 (_,op,arg1,arg2) -> "op2(_, "^op^", "^(string_of_expr arg1)^", "^(string_of_expr arg2)^")"
  | S.If (_,p,t,e) -> "if(_, "^(string_of_expr p)^", "^(string_of_expr t)^", "^(string_of_expr e)^")"
  | S.App (_,_,_) -> "app"
  | S.Seq (_,_,_) -> "seq"
  | S.Let (_,n,b,bod) -> "let(_, "^n^", "^(string_of_expr b)^", "^(string_of_expr bod)^")"
  | S.Rec (_,_,_,_) -> "letrec"
  | S.Label (_,_,_) -> "label"
  | S.Break (_,_,_) -> "break"
  | S.TryCatch (_,_,_) -> "trycatch"
      (** Catch block must be an [ELambda] *)
  | S.TryFinally (_,_,_) -> "tryfinally"
  | S.Throw (_,_) -> "throw"
  | S.Lambda (_,_,_) -> "lambda"
  | S.Eval (_,_,_) -> "eval"
  | S.Hint (_,_,_) -> "hint"
let str_clos_type clos store = match clos with 
  | ExpClosure (e, env) -> "Exp("^(string_of_expr e)^")"
  | ValClosure (v, env) ->  "Val("^(string_of_value v store)^")"
  | ExpClosure (e, env) -> "Exp("^(string_of_expr e)^", "^(string_of_env env)^")"
  | ValClosure (v, env) ->  "Val("^(string_of_value v store)^", "^(string_of_env env)^")"
  | AEClosure  (_, _) ->  "ae"
  | AVClosure  (_, _) ->  "av"
  | PEClosure  (_, _) ->  "pe"
  | PVClosure  (_, _) ->  "pv"
let string_of_kont k = match k with
  | K.SetBang (_, _) -> "k.setbang"
  | K.GetAttr (_, _, _, _) -> "k.getattr"
  | K.SetAttr (_, _, _, _, _, _) -> "k.setattr"
  | K.GetObjAttr (_, _) -> "k.getobjattr"
  | K.SetObjAttr (_, _, _, _) -> "k.setobjattr"
  | K.GetField (_, _, _, _, _, _, _, _) -> "k.getfield"
  | K.SetField (_, _, _, _, _, _, _, _, _, _) -> "k.setfield"
  | K.OwnFieldNames _ -> "k.ownfieldnames"
  | K.DeleteField (_, _, _, _) -> "k.deletefield"
  | K.Op1 (_, _) -> "k.op1"
  | K.Op2 (_, _, _, _) -> "k.op2"
  | K.Mt -> "k.mt"
  | K.If (_, _, _, _) -> "k.if"
  | K.App (_, _, _, _, _, _, _) -> "k.app"
  | K.Seq (_, _) -> "k.seq"
  | K.Let (_, _, _) -> "k.let"
  | K.Rec (_, _, _) -> "k.rec"
  | K.Break (label, _) -> "k.break: "^label
  | K.TryCatch (_, _, _, _, _) -> "k.trycatch"
  | K.TryFinally (_, _, _, _) -> "k.tryfinally"
  | K.Throw -> "k.throw"
  | K.Eval (_, _, _, _, _) -> "k.eval"
  | K.Hint -> "k.hint"
  | K.Object (_, _, _, _) -> "k.object"
  | K.Attrs (_, _, _, _, _, _) -> "k.attrs"
  | K.DataProp (_, _, _, _, _) -> "k.dataprop"
  | K.AccProp (_, _, _, _, _, _) -> "k.accprop"


(* from ljs_eval, let's move these to a util file eventuallly *)
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
          | _ -> interp_error Pos.dummy "bad access of attribute"
        end
  | _ -> failwith ("[interp] get-attr didn't get an object and a string.")

let unbool b = match b with
  | True -> true
  | False -> false
  | _ -> failwith ("tried to unbool a non-bool" ^ (pretty_value b))

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

let get_obj_attr attrs attr = match attrs, attr with
  | { proto=proto }, S.Proto -> proto
  | { extensible=extensible} , S.Extensible -> bool extensible
  | { code=Some code}, S.Code -> code
  | { code=None}, S.Code -> Null
  | { primval=Some primval}, S.Primval -> primval
  | { primval=None}, S.Primval ->
      failwith "[interp] Got Primval attr of None"
  | { klass=klass }, S.Klass -> String klass

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
                     ^ (*pretty_value obj*) "obj"
                     ^ " " ^ field ^ ")")

(* end borrowed ljs_eval helpers *)

let rec eval_cesk desugar clos store kont debug : (value * store) =
  let print_debug ce s k = begin
    print_string "$$$\n" ;
    print_string ((str_clos_type ce s)^"\n") ;
    print_values store ;
    print_string "\n" ;
    print_objects store ;
    print_string "\n" ;
    print_string ((string_of_kont k)^"\n") ;
  end in
  begin 
    if debug then print_debug clos store kont ;
    let eval clos store kont =
      begin try eval_cesk desugar clos store kont debug with
    | Break (exprs, l, v, s) ->
      raise (Break (add_opt clos exprs exp_of, l, v, s))
    | Throw (exprs, v, s) ->
      raise (Throw (add_opt clos exprs exp_of, v, s))
    | PrimErr (exprs, v) ->
      raise (PrimErr (add_opt clos exprs exp_of, v))
    | Snapshot (exps, v, envs, s) ->
      raise (Snapshot (add_opt clos exps exp_of, v, add_opt clos envs env_of, s))
    | Sys.Break ->
      raise (PrimErr (add_opt clos [] exp_of, String "s5_cesk_eval stopped by user interrupt"))
    | Stack_overflow ->
      raise (PrimErr (add_opt clos [] exp_of, String "s5_cesk_eval overflowed the Ocaml stack"))
    end in
  let rec apply p store func args = match func with
    | Closure (env, xs, body) ->
      let alloc_arg argval argname (store, env) =
        let (new_loc, store) = add_var store argval in
        let env' = IdMap.add argname new_loc env in
        (store, env') in
      if (List.length args) != (List.length xs) then
        arity_mismatch_err p xs args
      else
        let (store, env) = (List.fold_right2 alloc_arg args xs (store, env)) in
        (body, env, store)
    | ObjLoc loc -> begin match get_obj store loc with
        | ({ code = Some f }, _) -> apply p store f args
        | _ -> failwith "Applied an object without a code attribute"
    end
    | _ -> failwith (interp_error p
                       ("Applied non-function, was actually " ^
                         pretty_value func)) in
  match clos, kont with
  | ValClosure (valu, env), K.Mt -> begin
    if debug then print_string ("Converged to a value: "^(string_of_value valu store)) ;
    (valu, store)
  end
  (* value cases *)
  | ExpClosure (S.Undefined _, env), _ ->
    eval (ValClosure (Undefined, env)) store kont
  | ExpClosure (S.Null _, env), _ ->
    eval (ValClosure (Null, env)) store kont
  | ExpClosure (S.String (_, s), env), _ ->
    eval (ValClosure (String s, env)) store kont
  | ExpClosure (S.Num (_, n), env), _ ->
    eval (ValClosure (Num n, env)) store kont
  | ExpClosure (S.True _, env), _ ->
    eval (ValClosure (True, env)) store kont
  | ExpClosure (S.False _, env), _ ->
    eval (ValClosure (False, env)) store kont
  | ExpClosure (S.Id (p, name), env), _ ->
    (try
       let valu = get_var store (IdMap.find name env) in
       eval (ValClosure (valu, env)) store kont
     with Not_found ->
       failwith ("[interp] Unbound identifier: " ^ name ^ " in identifier lookup at " ^
                    (Pos.string_of_pos p)))
  | ExpClosure (S.Lambda (_, xs, body), env), k ->
    let free = S.free_vars body in
    let env' = IdMap.filter (fun var _ -> IdSet.mem var free) env in
    eval (ValClosure (Closure (env', xs, body), env)) store k
  (* SetBang cases *)
  (* TODO(adam): error cases for non-existent id's *)
  | ExpClosure (S.SetBang (p, x, new_val_exp), env), k ->
    (try
       let loc = IdMap.find x env in
       eval (ExpClosure (new_val_exp, env)) store (K.SetBang (loc, k))
     with Not_found ->
       failwith ("[interp] Unbound identifier: " ^ x ^ " in identifier lookup at " ^ (Pos.string_of_pos p)))
  | ValClosure (v, env), K.SetBang (loc, k) ->
    let store' = set_var store loc v in
    eval (ValClosure (v, env)) store' k
  (* Object cases *)
  | ExpClosure (S.Object (p, attrs, props), env), k ->
    eval (AEClosure (attrs, env)) store (K.Object (None, props, [], k))
  | AVClosure (valu, env), K.Object (None, [], [], k) ->
    let obj_loc, store = add_obj store (valu, IdMap.empty) in
    eval (ValClosure (ObjLoc obj_loc, env)) store k
  | AVClosure (valu, env), K.Object (None, prop::props, [], k) ->
    eval (PEClosure (prop, env)) store (K.Object (Some valu, props, [], k))
  | PVClosure (propv, env), K.Object (Some attrsv, prop::props, propvs, k) ->
    eval (PEClosure (prop, env)) store (K.Object (Some attrsv, props, propv::propvs, k))
  | PVClosure (propv, env), K.Object (Some attrsv, [], propvs, k) ->
    let add_prop acc (name, propv) = IdMap.add name propv acc in
    let propsv = List.fold_left add_prop IdMap.empty (propv::propvs) in
    let obj_loc, store = add_obj store (attrsv, propsv) in
    eval (ValClosure (ObjLoc obj_loc, env)) store k
  (* object properties cases *)
  | PEClosure ((name, prop), env), k ->
    (match prop with
    | S.Data ({ S.value = vexp; S.writable = w; }, enum, config) ->
      eval (ExpClosure (vexp, env)) store (K.DataProp (name, w, enum, config, k))
    | S.Accessor ({ S.getter = ge; S.setter = se; }, enum, config) ->
      eval (ExpClosure (ge, env)) store (K.AccProp (name, None, Some se, enum, config, k)))
  | ValClosure (valu, env), K.DataProp (name, w, enum, config, k) ->
    eval (PVClosure ((name, Data ({ value=valu; writable=w; }, enum, config)), env)) store k
  | ValClosure (valu, env), K.AccProp (name, None, Some se, enum, config, k) ->
    eval (ExpClosure (se, env)) store (K.AccProp (name, Some valu, None, enum, config, k))
  | ValClosure (valu, env), K.AccProp (name, Some gv, None, enum, config, k) ->
    eval (PVClosure ((name, Accessor ({ getter=gv; setter=valu; }, enum, config)), env)) store k
  (* object attributes cases *)
  | AEClosure (attrs, env), k ->
    let { S.primval = pexp; (* Opt *)
          S.code = cexp;     (* Opt *)
          S.proto = proexp;  (* Opt *)
          S.klass = kls;
          S.extensible = ext; } = attrs in
    let opt_add name ox xs = match ox with Some x -> (name, x)::xs | _ -> xs in
    let aes = opt_add "prim" pexp (opt_add "code" cexp (opt_add "proto" proexp [])) in
    (match aes with
    | [] ->
      let attrsv = { code=None; proto=Undefined; primval=None; klass=kls; extensible=ext } in
      eval (AVClosure (attrsv, env)) store k
    | (name, exp)::pairs -> eval (ExpClosure (exp, env)) store (K.Attrs (name, pairs, [], kls, ext, k)))
  | ValClosure (valu, env), K.Attrs (name, (name', exp)::pairs, valus, kls, ext, k) ->
    eval (ExpClosure (exp, env)) store (K.Attrs (name', pairs, (name, valu)::valus, kls, ext, k))
  | ValClosure (valu, env), K.Attrs (name, [], valus, kls, ext, k) ->
    let valus = (name, valu)::valus in
    let rec opt_get name xs = match xs with
      | [] -> None
      | (name', valu)::xs' -> if name = name' then Some valu else opt_get name xs' in
    let rec und_get name xs = match xs with
      | [] -> Undefined
      | (name', valu)::xs' -> if name = name' then valu else und_get name xs' in
    let attrsv = { code=(opt_get "code" valus);
                   proto=(und_get "proto" valus);
                   primval=(opt_get "primval" valus);
                   klass=kls;
                   extensible=ext; } in
    eval (AVClosure (attrsv, env)) store k
  (* GetAttr *)
  (* better way to do this? it's non-exhaustive, but shouldn't be an issue we
     we are guaranteeing left to right evaluation on the obj / field *)
  | ExpClosure (S.GetAttr (_, attr, obj, field), env), k ->
    eval (ExpClosure (obj, env)) store (K.GetAttr (attr, None, Some field, k))
  | ValClosure (obj_val, env), K.GetAttr (attr, None, Some field, k) ->
    eval (ExpClosure (field, env)) store (K.GetAttr (attr, Some obj_val, None, k))
  | ValClosure (field_val, env), K.GetAttr (attr, Some obj_val, None, k) ->
    eval (ValClosure (get_attr store attr obj_val field_val, env)) store k
  (* SetAttr Cases *)
  | ExpClosure (S.SetAttr (_, pattr, oe, pe, new_val_expr), env), k ->
    eval (ExpClosure (oe, env)) store (K.SetAttr (pattr, None, Some pe, None, Some new_val_expr, k))
  | ValClosure (oe_val, env), K.SetAttr (pattr, None, Some pe, None, Some new_val_expr, k) ->
    eval (ExpClosure (pe, env)) store (K.SetAttr (pattr, Some oe_val, None, None, Some new_val_expr, k))
  | ValClosure (pe_val, env), K.SetAttr (pattr, Some oe_val, None, None, Some new_val_expr, k) ->
    eval (ExpClosure (new_val_expr, env)) store (K.SetAttr (pattr, Some oe_val, None, Some pe_val, None, k))
  | ValClosure (new_val, env), K.SetAttr (pattr, Some oe_val, None, Some pe_val, None, k) ->
    let b, store = set_attr store pattr oe_val pe_val new_val in
    eval (ValClosure (bool b, env)) store k
  (* GetObjAttr Cases *)
  | ExpClosure (S.GetObjAttr (_, oattr, obj), env), k ->
    eval (ExpClosure (obj, env)) store (K.GetObjAttr (oattr, k))
  | ValClosure (obj_val, env), K.GetObjAttr (oattr, k) ->
    begin match obj_val with
      | ObjLoc obj_loc ->
        let (attrs, _) = get_obj store obj_loc in
        eval (ValClosure (get_obj_attr attrs oattr, env)) store k
      | _ -> failwith ("[interp] GetObjAttr got a non-object: " ^
                          (pretty_value obj_val))
    end
  (* SetObjAttr Cases *)
  | ExpClosure (S.SetObjAttr (_, oattr, obj_exp, na_exp), env), k ->
    eval (ExpClosure (obj_exp, env)) store (K.SetObjAttr (oattr, None, Some na_exp, k))
  | ValClosure (obj_val, env), K.SetObjAttr (oattr, None, Some na_exp, k) ->
    eval (ExpClosure (na_exp, env)) store (K.SetObjAttr (oattr, Some obj_val, None, k))
  | ValClosure (na_val, env), K.SetObjAttr (oattr, Some obj_val, None, k) ->
    begin match obj_val with
      | ObjLoc loc ->
        let (attrs, props) = get_obj store loc in
        let attrs' = match oattr, na_val with
          | S.Proto, ObjLoc _
          | S.Proto, Null -> { attrs with proto=na_val }
          | S.Proto, _ ->
            failwith ("[interp] Update proto failed: " ^
                       (pretty_value na_val))
          | S.Extensible, True -> { attrs with extensible=true }
          | S.Extensible, False -> { attrs with extensible=false }
          | S.Extensible, _ ->
            failwith ("[interp] Update extensible failed: " ^
                       (pretty_value na_val))
          | S.Code, _ -> failwith "[interp] Can't update Code"
          | S.Primval, v -> { attrs with primval=Some v }
          | S.Klass, _ -> failwith "[interp] Can't update Klass" in
        eval (ValClosure (na_val, env)) (set_obj store loc (attrs', props)) k
      | _ -> failwith ("[interp] SetObjAttr got a non-object: " ^
                        (pretty_value obj_val))
    end
  (* GetField cases *)
  | ExpClosure (S.GetField (p, obj, field, body), env), k ->
    eval (ExpClosure (obj, env)) store (K.GetField (p, None, Some field, None, Some body, env, false, k))
  | ValClosure (obj_val, env), K.GetField (p, None, Some field, None, Some body, env', false, k) ->
    eval (ExpClosure (field, env)) store (K.GetField (p, Some obj_val, None, None, Some body, env', false, k))
  | ValClosure (field_val, env), K.GetField (p, obj_val, None, None, Some body, env', false, k) ->
    eval (ExpClosure (body, env)) store (K.GetField (p, obj_val, None, Some field_val, None, env', false, k))
  | ValClosure (body_val, env), K.GetField (p, Some obj_val, None, Some field_val, None, env', false, k) ->
    begin match (obj_val, field_val) with
      | (ObjLoc _, String s) ->
        let prop = get_prop p store obj_val s in
        begin match prop with
          | Some (Data ({value=v;}, _, _)) -> eval (ValClosure (v, env')) store k
          | Some (Accessor ({getter=g;},_,_)) ->
            let (body, env'', store') = (apply p store g [obj_val; body_val]) in
            eval (ExpClosure (body, env'')) store' (K.GetField (p, None, None, None, None, env', true, k))
          | None -> eval (ValClosure (Undefined, env')) store k
        end
      | _ -> failwith ("[interp] Get field didn't get an object and a string at "
                       ^ Pos.string_of_pos p ^ ". Instead, it got "
                       ^ pretty_value obj_val ^ " and "
                       ^ pretty_value field_val)
    end
  | ValClosure (acc_val, _), K.GetField (_, _, _, _, _, env, true, k) ->
    eval (ValClosure (acc_val, env)) store k
  (* own field names cases *)
  | ExpClosure (S.OwnFieldNames (p, obj), env), k ->
    eval (ExpClosure (obj, env)) store (K.OwnFieldNames k)
  | ValClosure (obj_val, env), K.OwnFieldNames k ->
    begin match obj_val with
    | ObjLoc loc ->
      let _, props = get_obj store loc in
      let add_name n x m =
        IdMap.add (string_of_int x) (Data ({ value = String n; writable = false; }, false, false)) m in
      let names = IdMap.fold (fun k v l -> (k :: l)) props [] in
      let props = List.fold_right2 add_name names (iota (List.length names)) IdMap.empty in
      let d = float_of_int (List.length names) in
      let final_props =
        IdMap.add "length" (Data ({ value = Num d; writable = false; }, false, false)) props in
      let (new_obj, store) = add_obj store (d_attrsv, final_props) in
      eval (ValClosure (ObjLoc new_obj, env)) store k
    | _ -> failwith ("[interp] OwnFieldNames didn't get an object," ^
                  " got " ^ (pretty_value obj_val) ^ " instead.")
    end
  (* delete field cases *)
  | ExpClosure (S.DeleteField (p, obj, field), env), k ->
    eval (ExpClosure (obj, env)) store (K.DeleteField (p, None, Some field, k))
  | ValClosure (valu, env), K.DeleteField (p, None, Some field, k) ->
    eval (ExpClosure (field, env)) store (K.DeleteField (p, Some valu, None, k))
  | ValClosure (f_val, env), K.DeleteField (p, Some obj_val, None, k) ->
    begin match obj_val, f_val with
    | ObjLoc loc, String s ->
      begin match get_obj store loc with
      | attrs, props ->
        begin
          try match IdMap.find s props with
          | Data (_, _, true)
          | Accessor (_, _, true) ->
            let store' = set_obj store loc (attrs, IdMap.remove s props) in
            eval (ValClosure (True, env)) store' k
          | _ -> raise (Throw ([], String "unconfigurable-delete", store))
          with Not_found -> eval (ValClosure (False, env)) store k
        end
      end
    | _ -> failwith ("[interp] Delete field didn't get an object and a string at "
                     ^ Pos.string_of_pos p
                     ^ ". Instead, it got "
                     ^ pretty_value obj_val
                     ^ " and "
                     ^ pretty_value f_val)
    end
  (* SetField Cases *)
  | ExpClosure (S.SetField (p, obj, field, nf_exp, body), env), k ->
    (eval (ExpClosure (obj, env))
          store
          (K.SetField (p, None, Some field, None, Some nf_exp, None, Some body, env, false, k)))
  | ValClosure (obj_val, env),
    K.SetField (p, None, Some field, None, nf_exp, None, body, env', false, k) ->
    (eval (ExpClosure (field, env))
          store
          (K.SetField (p, Some obj_val, None, None, nf_exp, None, body, env', false, k)))
  | ValClosure (field_val, env),
    K.SetField (p, obj_val, None, None, Some nf_exp, None, body, env', false, k) ->
    (eval (ExpClosure (nf_exp, env))
          store
          (K.SetField (p, obj_val, None, Some field_val, None, None, body, env', false, k)))
  | ValClosure (nf_val, env),
    K.SetField (p, obj_val, None, field_val, None, None, Some body, env', false, k) ->
    (eval (ExpClosure (body, env))
          store
          (K.SetField (p, obj_val, None, field_val, None, Some nf_val, None, env', false, k)))
  | ValClosure (body_val, env),
    K.SetField (p, Some obj_val, None, Some field_val, None, Some nf_val, None, env', false, k) ->
    begin match (obj_val, field_val) with
      | (ObjLoc loc, String s) ->
        let ({extensible=extensible;} as attrs, props) =
          get_obj store loc in
        let prop = get_prop p store obj_val s in
        let unwritable = (Throw ([],
                                 String "unwritable-field",
                                 store)) in
        begin match prop with
          | Some (Data ({ writable = true; }, enum, config)) ->
            let (enum, config) =
              if (IdMap.mem s props)
              then (enum, config) (* 8.12.5, step 3, changing the value of a field *)
              else (true, true) in (* 8.12.4, last step where inherited.[[writable]] is true *)
            let store = set_obj store loc
              (attrs,
               IdMap.add s
                 (Data ({ value = nf_val; writable = true },
                        enum, config))
                 props) in
            eval (ValClosure (nf_val, env)) store k
          | Some (Data _) -> raise unwritable
          | Some (Accessor ({ setter = Undefined; }, _, _)) ->
            raise unwritable
          | Some (Accessor ({ setter = setterv; }, _, _)) ->
                (* 8.12.5, step 5 *)
            let (body, env'', store') = apply p store setterv [obj_val; body_val] in
            eval (ExpClosure (body, env'')) store' (K.SetField (p, None, None, None, None, None, None, env', true, k))
          | None ->
                (* 8.12.5, step 6 *)
            if extensible
            then
              let store = set_obj store loc
                (attrs,
                 IdMap.add s
                   (Data ({ value = nf_val; writable = true; },
                          true, true))
                   props) in
              eval (ValClosure (nf_val, env)) store k
            else
              eval (ValClosure (Undefined, env)) store k
        end
      | _ -> failwith ("[interp] Update field didn't get an object and a string"
                       ^ Pos.string_of_pos p ^ " : " ^ (pretty_value obj_val) ^
                         ", " ^ (pretty_value field_val))
    end
  | ValClosure (acc_val, _), K.SetField (_, _, _, _, _, _, _, env, true, k) ->
    eval (ValClosure (acc_val, env)) store k
  (* Op1 cases *)
  | ExpClosure (S.Op1 (_, name, arg), env), k ->
    eval (ExpClosure (arg, env)) store (K.Op1 (name, k))
  | ValClosure (arg_val, env), K.Op1 (name, k) ->
    eval (ValClosure (op1 store name arg_val, env)) store k
  (* Op2 cases *)
  | ExpClosure (S.Op2 (_, name, arg1, arg2), env), k ->
    eval (ExpClosure (arg1, env)) store (K.Op2 (name, None, Some arg2, k))
  | ValClosure (arg1_val, env), K.Op2 (name, None, Some arg2, k) ->
    eval (ExpClosure (arg2, env)) store (K.Op2 (name, Some arg1_val, None, k))
  | ValClosure (arg2_val, env), K.Op2 (name, Some arg1_val, None, k) ->
    eval (ValClosure (op2 store name arg1_val arg2_val, env)) store k
  (* If cases *)
  | ExpClosure (S.If (_, pred, than, elze), env), k ->
    eval (ExpClosure (pred, env)) store (K.If (env, than, elze, k))
  | ValClosure (v, env), K.If (env', than, elze, k) ->
    if (v = True)
    then eval (ExpClosure (than, env')) store k
    else eval (ExpClosure (elze, env')) store k
  (* App cases *)
  | ExpClosure (S.App (pos, func, args), env), k ->
    eval (ExpClosure (func, env)) store (K.App (pos, None, env, [], args, false, k))
  | ValClosure (func, env), K.App (pos, None, env', [], [], false, k) -> (* special case for no arg apps *)
    let (body, env'', store') = apply pos store func [] in
    eval (ExpClosure (body, env'')) store' (K.App (pos, None, env', [], [], true, k))
  | ValClosure (func, env), K.App (pos, None, env', vs, expr::exprs, false, k) ->
    eval (ExpClosure (expr, env')) store (K.App (pos, Some func, env', vs, exprs, false, k))
  | ValClosure (arg_val, env), K.App (pos, Some func, env', vs, expr::exprs, false, k) ->
    eval (ExpClosure (expr, env')) store (K.App (pos, Some func, env', arg_val::vs, exprs, false, k))
  | ValClosure (arg_val, env), K.App (pos, Some func, env', vs, [], false, k) ->
    let (body, env'', store') = apply pos store func (List.rev (arg_val::vs)) in
    eval (ExpClosure (body, env'')) store' (K.App (pos, None, env', [], [], true, k))
  | ValClosure (body_val, env), K.App (_, _, orig_env, _, _, true, k) ->
    eval (ValClosure (body_val, orig_env)) store k
  (* sequence (begin) cases *)
  | ExpClosure (S.Seq (_, left, right), env), k ->
    eval (ExpClosure (left, env)) store (K.Seq (right, k))
  | ValClosure (_, env), K.Seq (right, k) ->
    eval (ExpClosure (right, env)) store k
  (* let cases *)
  | ExpClosure (S.Let (_, name, expr, body), env), k ->
    eval (ExpClosure (expr, env)) store (K.Let (name, body, k))
  | ValClosure (v, env), K.Let (name, body, k) ->
    let (new_loc, store') = add_var store v in
    eval (ExpClosure (body, IdMap.add name new_loc env)) store' k
  (* letrec cases *)
  | ExpClosure (S.Rec (_, name, expr, body), env), k ->
    let (new_loc, store') = add_var store Undefined in
    let env' = IdMap.add name new_loc env in
    eval (ExpClosure (expr, env')) store' (K.Rec (new_loc, body, k))
  | ValClosure (v, env), K.Rec (new_loc, body, k) ->
    eval (ExpClosure (body, env)) (set_var store new_loc v) k
  (* Label case, just creates a try that we can break to. Should control flow
     rely on OCaml's control flow? *)
  | ExpClosure (S.Label (_, name, exp), env), k ->
    (try
      eval (ExpClosure (exp, env)) store k
    with Break (t, l', v, store') ->
      if name = l' then
        eval (ValClosure (v, env)) store' k
      else raise (Break (t, l', v, store')))
  (* break cases, see details in label case for future work *)
  | ExpClosure (S.Break (_, label, expr), env), k ->
    eval (ExpClosure (expr, env)) store (K.Break (label, k))
  | ValClosure (v, _), K.Break (label, _) ->
    raise (Break ([], label, v, store))
  (* try catch *)
  | ExpClosure (S.TryCatch (p, body, catch), env), k ->
    (try
      eval (ExpClosure (body, env)) store (K.TryCatch (p, Some catch, env, None, k))
    with Throw (_, throw_val, store) ->
      eval (ExpClosure (catch, env)) store (K.TryCatch (p, None, env, Some throw_val, k)))
  | ValClosure (body_val, env'), K.TryCatch (p, Some catch, env, None, k) ->
    eval (ValClosure (body_val, env')) store k
  | ValClosure (catch_val, env'), K.TryCatch (p, None, env, Some throw_val, k) ->
    let (body, env'', store') = apply p store catch_val [throw_val] in
    eval (ExpClosure (body, env'')) store' (K.TryCatch (p, None, env, None, k))
  | ValClosure (catch_body_val, _), K.TryCatch (p, None, env, None, k) ->
    eval (ValClosure (catch_body_val, env)) store k
  (* try finally. the semantics below will throw errors which occur during the evaluation
     of the finally clause up, as is the expected? functionality, which is inconsistent with
     the original eval *)
  | ExpClosure (S.TryFinally (_, body, fin), env), k ->
    (try
       eval (ExpClosure (body, env)) store (K.TryFinally (Some fin, env, None, k))
     with
     | Throw (p, v, store') ->
       eval (ExpClosure (fin, env)) store (K.TryFinally (None, env, Some (Throw (p, v, store')), k))
     | Break (t, l, v, store') ->
       eval (ExpClosure (fin, env)) store (K.TryFinally (None, env, Some (Break (t, l, v, store')), k)))
  | ValClosure (valu, env'), K.TryFinally (Some fin, env, None, k) -> (* now evaluate the fin *)
    eval (ExpClosure (fin, env)) store k
  | ValClosure (valu, env'), K.TryFinally (None, env, Some except, k) ->
    (match except with
    | Throw (t, v, _) -> raise (Throw (t, v, store))
    | Break (t, l, v, _) -> raise (Break (t, l, v, store)))
  (* lob those exceptions *)
  | ExpClosure (S.Throw (_, expr), env), k ->
    eval (ExpClosure (expr, env)) store K.Throw
  | ValClosure (valu, env), K.Throw ->
    raise (Throw ([], valu, store))
  (* eval *)
  | ExpClosure (S.Eval (pos, str_expr, bindings), env), k ->
    eval (ExpClosure (str_expr, env)) store (K.Eval (pos, None, Some bindings, store, k))
  | ValClosure (valu, env), K.Eval (pos, None, Some bindings, store', k) ->
    eval (ExpClosure (bindings, env)) store (K.Eval (pos, Some valu, None, store', k))
  | ValClosure (bind_val, env), K.Eval (pos, Some str_val, None, store', k) ->
    (match str_val, bind_val with
    | String s, ObjLoc o ->
      let expr = desugar s in
      let env', store'' = envstore_of_obj pos (get_obj store o) store in
      eval (ExpClosure (expr, env')) store'' (K.Eval (pos, None, None, store', k))
    | String _, _ -> interp_error pos "Non-object given to eval() for env"
    | v, _ -> eval (ValClosure (v, env)) store' k)
  | ValClosure (valu, env), K.Eval (_, None, None, store', k) ->
    eval (ValClosure (valu, env)) store' k
  (* hints, we raise a snapshot if that's what we need to do, otherwise we
     just continue evaluation *)
  | ExpClosure (S.Hint (_, "___takeS5Snapshot", expr), env), k ->
    eval (ExpClosure (expr, env)) store K.Hint
  | ExpClosure (S.Hint (_, _, expr), env), k ->
    eval (ExpClosure (expr, env)) store k
  | ValClosure (valu, env), K.Hint ->
    raise (Snapshot ([], valu, [], store))
end

and envstore_of_obj p (_, props) store =
  IdMap.fold (fun id prop (env, store) -> match prop with
    | Data ({value=v}, _, _) ->
      let new_loc, store = add_var store v in
      let env = IdMap.add id new_loc env in
      env, store
    | _ -> interp_error p "Non-data value in env_of_obj")
  props (IdMap.empty, store)

and arity_mismatch_err p xs args = interp_error p ("Arity mismatch, supplied " ^ string_of_int (List.length args) ^ " arguments and expected " ^ string_of_int (List.length xs) ^ ". Arg names were: " ^ (List.fold_right (^) (map (fun s -> " " ^ s ^ " ") xs) "") ^ ". Values were: " ^ (List.fold_right (^) (map (fun v -> " " ^ pretty_value v ^ " ") args) ""))

let err show_stack trace message =
  if show_stack then begin
      eprintf "%s\n" (string_stack_trace trace);
      eprintf "%s\n" message;
      failwith "Runtime error"
    end
  else
    eprintf "%s\n" message;
    failwith "Runtime error"


(*     expr => Ljs_syntax.exp
    desugar => (string -> Ljs_syntax.exp)
print_trace => bool
        env => IdMap
      store => (Store, Store)
               where the left is for objects and
               the right is for values            *)
let continue_eval expr desugar print_trace env store = try
  Sys.catch_break true;
  let (v, store) = eval_cesk desugar (ExpClosure (expr, env)) store K.Mt false in
  L.Answer ([], v, [], store)
with
  | Snapshot (exprs, v, envs, store) ->
    L.Answer (exprs, v, envs, store)
  | Throw (t, v, store) ->
      let err_msg =
        match v with
          | ObjLoc loc -> begin match get_obj store loc with
            | _, props -> try match IdMap.find "%js-exn" props with
              | Data ({value=jserr}, _, _) -> string_of_value jserr store
              | _ -> string_of_value v store
              with Not_found -> string_of_value v store
            end
          | v -> string_of_value v store in
        err print_trace t (sprintf "Uncaught exception: %s\n" err_msg)
  | Break (p, l, v, _) -> failwith ("Broke to top of execution, missed label: " ^ l)
  | PrimErr (t, v) ->
      err print_trace t (sprintf "Uncaught error: %s\n" (pretty_value v))

(*     expr => Ljs_syntax.exp
    desugar => (string -> Ljs_syntax.exp)
print_trace => bool                       *)
let eval_expr expr desugar print_trace =
  continue_eval expr desugar print_trace IdMap.empty (Store.empty, Store.empty)
