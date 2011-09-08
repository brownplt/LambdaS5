open Prelude

module E = Exprjs_syntax
module S = Es5_syntax

let idx = ref 0

let mk_id str = 
  idx := !idx + 1;
  "%" ^ str ^ (string_of_int !idx)

let make_get_field p obj fld =
  let argsobj = S.Object (p, S.d_attrs, []) in
  match obj with
    | S.Id (p, "%context") ->
      S.App (p, S.Id (p, "%EnvLookup"), [obj; fld])
    | _ -> S.GetField (p, obj, fld, argsobj)

let to_string p v =
  match v with
    | S.String (p, s) -> S.String (p, s)
    | _ -> S.App (p, S.Id (p, "%ToString"), [v])

let to_object p v =
  match v with
    | S.Id (p, "%context") -> v
    | _ -> S.App (p, S.Id (p, "%ToObject"), [v])

let prop_accessor_check p v =
  match v with
    | S.Id (p, "%context") -> v
    | _ -> S.App (p, S.Id (p, "%PropAccessorCheck"), [v])

(* 15.4: A property name P (in the form of a String value) is an array index if and
 * only if ToString(ToUint32(P)) is equal to P and ToUint32(P) is not equal to
 * 2^32−1 *)
let make_set_field p obj fld value =
  match obj with
  | S.Id (p, "%context") -> 
    S.App (p, S.Id (p, "%EnvCheckAssign"), [obj; fld; value])
  | _ -> S.App (p, S.Id (p, "%set-property"), [obj; fld; value])

let make_args_obj p args =
    let n_args = List.length args in
    let indices = Prelude.iota n_args in
    let combined = List.combine indices args in
    let records =
      List.map (fun (n, arg) -> (n, {S.value = arg; S.writable = true})) combined in
    let props = 
      List.map 
        (fun (n, rcrd) -> (string_of_int n, S.Data (rcrd, true, true))) records in
    S.App (p, S.Id (p, "%mkArgsObj"), [S.Object (p, S.d_attrs, props)])

let rec ejs_to_ljs (e : E.expr) : S.exp = match e with
  | E.True (p) -> S.True (p)
  | E.False (p) -> S.False (p)
  | E.Num (p, n) -> S.Num (p, n)
  | E.Undefined (p) -> S.Undefined (p)
  | E.Null (p) -> S.Null (p)
  | E.String (p, s) -> S.String (p, s)
  | E.RegExpr (p, s) -> 
    let re_attrs = { S.primval = None;
                     S.code = None;
                     S.proto = Some (S.Id (p, "%RegexpProto"));
                     S.klass = "Regexp"; (* correct? *)
                     S.extensible = true; } in
    let lit_data = S.Data ({S.value = S.String (p, s); S.writable = false;}, false, false) in
    S.Object (p, re_attrs, [("%lit", lit_data)])
  | E.ArrayExpr (p, el) ->
    let rec e_to_p e n = (
      string_of_int n, 
      S.Data ({ S.value = e; S.writable = true; }, true, true))
    and el_to_pl l n = match l with
      | [] -> []
      | first :: rest -> (e_to_p first n) :: el_to_pl rest (n + 1) in
    let desugared = List.map ejs_to_ljs el
    and a_attrs = {
      S.primval = None;
        S.code = None;
        S.proto = Some (S.Id (p, "%ArrayProto")); 
        S.klass = "Array";
        S.extensible = true; } in
    let exp_props = el_to_pl desugared 0 in
    let lfloat = float_of_int (List.length exp_props) in
    let l_prop = (* TODO: is array length prop writ/enum/configurable? *)
      S.Data (
        { S.value = S.Num (p, lfloat); S.writable = true; },
        false,
        false) in
    S.Object (p, a_attrs, ("length", l_prop) :: exp_props)
  | E.ObjectExpr (p, pl) ->
    (* Given a tuple, if it's a getter/setter, create a name-accessor pair and add to
     * sofar *)
    let add_accessor pr sofar = match pr with
      | (_, _, E.Getter (nm, exp)) ->
        let gval = get_fobj p [] exp (S.Id (p, "%context")) in
        let a = { S.getter = gval; S.setter = S.Undefined (p); } in
        (nm, S.Accessor (a, false, false)) :: sofar
      | (_, _, E.Setter (nm, exp)) ->
        let (param_name, sfunc) = match exp with
          | E.LetExpr (_, nm, _, body) -> (nm, body)
          | _ -> failwith "setter desugaring error: expected LetExpr here" in
        let sval = get_fobj p [param_name] sfunc (S.Id (p, "%context")) in
        let a = { S.getter = S.Undefined (p); S.setter = sval; } in
        (nm, S.Accessor (a, false, false)) :: sofar
      | _ -> sofar in
    (* Given a list of tuples, produce a list of name, accessor pairs *)
    let rec accessors tl sofar = match tl with
      | [] -> sofar
      | t :: rest -> accessors rest (add_accessor t sofar) in
    (* Get only those pairs with name = nm *)
    let tuples tl nm = List.filter (fun (n, _) -> n = nm) tl in
    (* Given a list of name-accessor pairs, reduce them to one *)
    let rec reduce al result = match al with
      | [] -> result
      | (nm, S.Accessor (a, wr, cfg)) :: rest ->
        let result_a = match result with
          | S.Accessor (aa, _, _) -> aa in
        let next = match a with
          | { S.getter = S.Undefined _; S.setter = s; } ->
            S.Accessor ({ S.getter = result_a.S.getter; S.setter = s; }, wr, cfg)
          | { S.getter = g; S.setter = S.Undefined _; } ->
            S.Accessor ({ S.getter = g; S.setter = result_a.S.setter; }, wr, cfg)
          | _ -> S.Accessor (a, wr, cfg) in
        reduce rest next in
    let dup_pairs = accessors pl [] in
    let name_lst = remove_dupes (map (fun (n, _) -> n) dup_pairs) in
    let name_assoc = map (fun n -> (n, tuples dup_pairs n)) name_lst in
    let dummy_prop = 
      S.Accessor (
        { S.getter = S.Undefined (p); S.setter = S.Undefined (p); }, true, true) in
    let reduced_assoc = map (fun (n, al) -> (n, reduce al dummy_prop)) name_assoc in
    let data_props = 
      List.filter (fun p -> let result = 
        match p with (_, _, E.Data _) -> true | _ -> false in result) pl in
    let rec ejsprop_to_sprop pr = match pr with
      | E.Data (e) -> 
          let rec v = ejs_to_ljs e
          and d = { S.value = v; S.writable = true; } in
          S.Data (d, true, true)
      | _ -> failwith "accessor properties should have been filtered out"
    and tuple_to_prop t = match t with
      (p, s, pr) -> (s, ejsprop_to_sprop pr)
    and form_props props = match props with
      | [] -> []
      | first :: rest -> (tuple_to_prop first) :: form_props rest in
    let data_result = form_props data_props in
    let o_attrs = {
      S.primval = None;
      S.code = None;
      S.proto = Some (S.Id (p, "%ObjectProto"));
      S.klass = "Object";
      S.extensible = true; } in
    S.Object (p, o_attrs, List.append reduced_assoc data_result)
  | E.ThisExpr (p) -> S.Id (p, "%this")
  | E.IdExpr (p, nm) -> S.Id (p, nm)
  | E.BracketExpr (p, l, r) -> 
    let o = prop_accessor_check p (ejs_to_ljs l) in
    let f = to_string p (ejs_to_ljs r) in
    make_get_field p o f
  | E.NewExpr (p, econstr, eargs) -> 
    let constr_id = mk_id "constr" in
    let pr_id = mk_id "cproto" in
    let newobj = mk_id "newobj" in
    let constr_result = mk_id "constr_ret" in
    let getterargs = S.Object (p, S.d_attrs, []) in
    let constrargs = make_args_obj p (map ejs_to_ljs eargs) in
    S.Let (p, constr_id, ejs_to_ljs econstr,
      S.If (p, 
        S.Op1 (p, "!", 
          S.Op2 (p, "stx=", 
            S.Op1 (p, "typeof", S.Id (p, constr_id)),
            S.String (p, "function"))),
        S.App (p, S.Id (p, "%ThrowTypeError"), [S.Null (p); S.Null (p)]),
           S.Let (p, pr_id, S.GetField (p, S.Id (p, constr_id), 
                                        S.String (p, "prototype"), getterargs),
                  S.If (p, S.Op2 (p, "stx=", S.Id (p, pr_id), S.Undefined (p)), 
                      S.App (p, S.Id (p, "%ThrowTypeError"), [S.Null (p); S.Null (p)]),
                  S.Let (p, newobj, 
                         S.Object (p, { S.d_attrs with S.proto = Some (S.Id (p, pr_id)) }, []),
                         S.If (p, S.Op2 (p, "stx=", S.Null (p), 
                          S.Op1 (p, "get-code", S.Id (p, constr_id))),
                          S.App (p, S.Id (p, "%ThrowTypeError"), [S.Null (p); S.Null (p)]),
                         S.Let (p, constr_result,
                                S.App (p, S.Id (p, constr_id), [S.Id (p, newobj); constrargs]),
                                S.If (p, S.Op2 (p, "stx=", S.String (p, "object"), 
                                                S.Op1 (p, "typeof", S.Id (p, constr_result))),
                                      S.Id (p, constr_result),
                                      S.If (p, S.Op2 (p, "stx=", S.String (p,
                                      "function"), S.Op1 (p, "typeof", S.Id (p,
                                      constr_result))), S.Id (p, constr_result),
                                      S.Id (p, newobj))))))))))
  | E.PrefixExpr (p, op, exp) -> let result = match op with
    | "postfix:++" -> let target = ejs_to_ljs exp in
      begin match target with
        | S.App (_, S.Id (_, "%EnvLookup"), [context; fldexpr]) ->
          S.App (p, S.Id (p, "%PostIncrementCheck"), [context; fldexpr])
        | S.GetField (_, obj, fld, _) ->
          S.App (p, S.Id (p, "%PostIncrement"), [obj; fld])
        | _ -> failwith "desugaring error: postfix:++"
      end
    | "postfix:--" -> let target = ejs_to_ljs exp in
      begin match target with
        | S.App (_, S.Id (_, "%EnvLookup"), [context; fldexpr]) ->
          S.App (p, S.Id (p, "%PostDecrementCheck"), [context; fldexpr])
        | S.GetField (_, obj, fld, _) ->
          S.App (p, S.Id (p, "%PostDecrement"), [obj; fld])
        | _ -> failwith "desugaring error: postfix:--"
      end
    | "prefix:++" -> let target = ejs_to_ljs exp in 
      begin match target with
        | S.App (_, S.Id (_, "%EnvLookup"), [context; fldexpr]) ->
          S.App (p, S.Id (p, "%IncrementCheck"), [context; fldexpr])
        | S.GetField (_, obj, fld, _) ->
          S.App (p, S.Id (p, "%PrefixIncrement"), [obj; fld])
        | _ -> failwith "desugaring error: prefix:++"
      end
    | "prefix:--" -> let target = ejs_to_ljs exp in
      begin match target with
        | S.App (_, S.Id (_, "%EnvLookup"), [context; fldexpr]) ->
          S.App (p, S.Id (p, "%DecrementCheck"), [context; fldexpr])
        | S.GetField (_, obj, fld, _) ->
          S.App (p, S.Id (p, "%PrefixDecrement"), [obj; fld])
        | _ -> failwith "desugaring error: prefix:--"
      end
    | "typeof" -> let target = ejs_to_ljs exp in
      begin match target with
        | S.App (_, S.Id (_, "%EnvLookup"), [context; fldexpr]) ->
          S.Op1 (p, "surface-typeof", S.GetField (p, context, fldexpr, noargs_obj))
        | _ -> S.Op1 (p, "surface-typeof", target)
      end
    | "delete" -> let result = match exp with
      | E.BracketExpr (pp, obj, fld) -> 
        let fld_str = S.Op1 (p, "prim->str", ejs_to_ljs fld)
        and sobj = ejs_to_ljs obj in
        let null = S.Null (pp) in
        begin match sobj with
          | S.Id (_, "%context") ->
            let null = S.Null (p) in
            S.App (pp, S.Id (pp, "%ThrowSyntaxError"), [null; null])
          | _ ->
            S.If (p, S.Op2 (p, "hasProperty", sobj, fld_str),
              S.If (p,
                S.GetAttr (pp, S.Config, sobj, fld_str),
                S.DeleteField (pp, sobj, fld_str),
                S.App (p, S.Id (p, "%ThrowTypeError"), [null; null])),
              S.True (p))
        end
      | _ -> S.True (p) in result
    | "-" -> S.App(p, S.Id (p, "%UnaryNeg"), [ejs_to_ljs exp])
    | "+" -> S.App (p, S.Id (p, "%UnaryPlus"), [ejs_to_ljs exp])
    | "~" -> S.App (p, S.Id (p, "%BitwiseNot"), [ejs_to_ljs exp])
    | _ -> S.Op1 (p, op, ejs_to_ljs exp) in result
  | E.InfixExpr (p, op, l, r) ->
    let sl = ejs_to_ljs l and sr = ejs_to_ljs r in
    let result = match op with
      | "&&" ->
        S.Let (p, "%l-evaled", sl,
          S.If (p, 
            S.App (p, S.Id (p, "%ToBoolean"), [S.Id (p, "%l-evaled")]),
            sr, 
            S.Id (p, "%l-evaled")))
      | "||" ->
        S.Let (p, "%l-evaled", sl,
          S.If (p,
            S.App (p, S.Id (p, "%ToBoolean"), [S.Id (p, "%l-evaled")]),
            S.Id (p, "%l-evaled"),
            sr))
      | "!==" -> S.Op1 (p, "!", S.Op2 (p, "stx=", sl, sr))
      | "!=" -> S.Op1 (p, "!", S.App (p, S.Id (p, "%EqEq"), [sl; sr]))
      | "==" -> S.App (p, S.Id (p, "%EqEq"), [sl; sr])
      | "+" -> S.App (p, S.Id (p, "%PrimAdd"), [sl; sr])
      | "-" -> S.App (p, S.Id (p, "%PrimSub"), [sl; sr])
      | "*"
      | "%"
      | "/" -> 
        let op_func = 
          S.Lambda (p, ["a"; "b"], S.Op2 (p, op, S.Id (p, "a"), S.Id (p, "b"))) in
        S.App (p, S.Id (p, "%PrimMultOp"), [sl; sr; op_func])
      | "instanceof" -> S.App (p, S.Id (p, "%instanceof"), [sl; sr])
      | "&" -> S.App (p, S.Id (p, "%instanceof"), [sl; sr])
      | _ -> let op = match op with
        | "===" -> "stx="
        | _ -> op in S.Op2 (p, op, sl, sr) in result
  | E.IfExpr (p, e1, e2, e3) -> let e1 = ejs_to_ljs e1
    and e2 = ejs_to_ljs e2
    and e3 = ejs_to_ljs e3 in 
    S.If (p, 
      S.App (p, S.Id (p, "%ToBoolean"), [e1]),
      e2, 
      e3)
  | E.AssignExpr (p, obj, pr, vl) -> 
    let sobj = to_object p (ejs_to_ljs obj) in
    let spr = to_string p (ejs_to_ljs pr) in
    let svl = ejs_to_ljs vl in
    make_set_field p sobj spr svl
  | E.AppExpr (p, e, el) -> 
    let sl = List.map (fun x -> ejs_to_ljs x) el in
    let args_obj = make_args_obj p sl in
    let obj_id = mk_id "obj" in
    let fun_id = mk_id "fun" in
    begin match e with
      | E.BracketExpr (_, E.IdExpr (_, "%context"), _) ->
        S.Let (p, fun_id, ejs_to_ljs e,
          appexpr_check (S.Id (p, fun_id))
          (S.App (p, S.Id (p, fun_id), [S.Id (p, "%global"); args_obj]))
          p)
      | E.BracketExpr (_, obj, fld) ->
        let flde = ejs_to_ljs fld in
        S.Let (p, obj_id, ejs_to_ljs obj, 
          S.Let (p, fun_id, make_get_field p (to_object p (S.Id (p, obj_id))) (to_string p flde),
            appexpr_check (S.Id (p, fun_id))
            (S.App (p, S.Id (p, fun_id), [to_object p (S.Id (p, obj_id)); args_obj]))
            p))
      | _ ->
        S.Let (p, fun_id, ejs_to_ljs e,
          appexpr_check (S.Id (p, fun_id))
          (S.App (p, S.Id (p, fun_id), [S.Id (p, "%global"); args_obj]))
          p)
    end
  | E.FuncExpr (p, args, body) -> get_fobj p args body (S.Id (p, "%context"))
  | E.LetExpr (p, nm, vl, body) ->
    let sv = ejs_to_ljs vl
    and sb = ejs_to_ljs body in
    let result_obj = match nm with
      | "%context" -> let orig_props = match sv with
        | S.Object (_, _, pl) -> pl
        | _ -> failwith "let bound %context to a non-object" in
        let c_attrs = { S.primval = None;
                        S.code = None;
                        S.proto = Some (S.Id (p, "%context"));
                        S.klass = "Object";
                        S.extensible = true; } in
        S.Object (p, c_attrs, orig_props)
      | _ -> sv in
    S.Let (p, nm, result_obj, sb)
  | E.SeqExpr (p, e1, e2) -> S.Seq (p, ejs_to_ljs e1, ejs_to_ljs e2)
  | E.WhileExpr (p, tst, bdy) ->
    let t = ejs_to_ljs tst and b = ejs_to_ljs bdy in get_while t b
  | E.LabelledExpr (p, lbl, exp) -> S.Label (p, lbl, ejs_to_ljs exp)
  | E.BreakExpr (p, id, e) -> S.Break (p, id, ejs_to_ljs e)
  | E.ForInExpr (p, nm, vl, bdy) ->
    get_forin p nm (ejs_to_ljs vl) (ejs_to_ljs bdy)
  | E.TryCatchExpr (p, body, ident, catch) -> 
    let new_ctxt = 
      S.Object (p, { S.d_attrs with S.proto = Some (S.Id (p, "%parent")) },
                [(ident, 
                  S.Data ({ S.value = S.Id (p, ident); S.writable = true }, 
                         false, false) );])
    in
    S.TryCatch (p, ejs_to_ljs body, 
                S.Lambda(p, [ident], 
                         S.Let (p, "%parent", S.Id (p, "%context") ,
                                S.Let (p, "%context", new_ctxt, 
                                       ejs_to_ljs catch))))
  | E.FuncStmtExpr (p, nm, args, body) -> 
    let fobj = get_fobj p args body (S.Id (p, "%context")) in
    let arcrd = { S.value = fobj; S.writable = true; } in
    let aprop = S.Data (arcrd, true, true) in
    let aprops = [("0", aprop)] in
    let argsobj = S.Object (p, S.d_attrs, aprops) in
    S.SetField (p, S.Id (p, "%context"), S.String (p, nm), fobj, argsobj)
  | E.TryFinallyExpr (p, body, finally) -> 
    S.TryFinally (p, ejs_to_ljs body, ejs_to_ljs finally)
  | E.ThrowExpr (p, e) -> S.Throw (p, ejs_to_ljs e)
  | E.HintExpr _ -> failwith "Bizarre error: Hint found somehow"

and a_attrs = {
  S.primval = None;
      S.code = None;
      S.proto = Some (S.Id (dummy_pos, "%ArrayProto"));
      S.klass = "Array";
      S.extensible = true; }

and noargs_obj = S.Object (dummy_pos, a_attrs, [])

and onearg_obj a = 
  let r = { S.value = a; S.writable = true; } in
  let p = S.Data (r, true, true) in
  S.Object (dummy_pos, a_attrs, [("0", p)])

and get_fobj p args body context = 
  let call = get_lambda p args body in
  let fproto = S.Id (p, "%FunctionProto") in
  let fobj_attrs = 
    { S.primval = None; S.code = Some (call); S.proto = Some (fproto); S.klass = "Function"; 
    S.extensible = true; } in
  let param_len = List.length args in
  let indices = Prelude.iota param_len in
  let combined = List.combine indices args in
  let rcds =
    List.map (fun (n, prm) -> (n, {S.value = S.String (p, prm); S.writable =
      true;})) combined in
  let props =
    List.map (fun (n, rcd) -> (string_of_int n, S.Data (rcd, true, true)))
    rcds in
  let param_obj = S.Object (p, S.d_attrs, props) in
  let proto_id = mk_id "prototype" in
  let proto_obj = 
    S.Object (p, {S.d_attrs with S.proto = Some (S.Id (p, "%ObjectProto"))}, 
              [("constructor", S.Data ({ S.value = S.Undefined p;
                                         S.writable = true}, 
                                       false, false))]) in
  let proto_prop = S.Data ({ S.value = S.Id (p, proto_id); S.writable = true}, 
                           false, true) in
  let length_prop = S.Data ({ S.value = S.Num (p, (float_of_int param_len)); S.writable = true}, 
                           false, true) in
  let func_id = mk_id "thisfunc" in
  S.Let (p, proto_id, proto_obj,
         S.Let (p, "%parent", context,
                S.Let (p, "%params", param_obj,
                       S.Let (p, func_id, S.Object (p, fobj_attrs, [("prototype", proto_prop); ("length", length_prop)]),
                              S.Seq (p, S.SetField (p, S.Id (p, proto_id), S.String (p, "constructor"), S.Id (p, func_id), S.Null p),
                                     S.Id (p, func_id))))))
           
(* The first stage of desugaring creates exprjs let expressions corresponding
 * to JavaScript declared variables.  
 * get_prop_lets and create_context are used to translate those variables into 
 * the final representation (let-bound es5 variables with randomly generated
 * names, that are read/written by context object accessor properties with the
 * "real" name)
 *)
and get_prop_lets p nms e = match nms with
  | [] -> e
  | nm :: rest ->
    get_prop_lets p rest (S.Let (p, nm, S.Undefined p, e))

and create_context p body parent =
  let rec strip_lets e nms = match e with
    | E.LetExpr (p, nm, vl, rst) ->
      let prefix = if (String.length nm) >= 2 then String.sub nm 0 2 else "" in
      if prefix = "%%" then
        let l = (String.length nm) - 2 in
        let next_nms = (String.sub nm 2 l) :: nms in strip_lets rst next_nms
      else
        let (final_nms, final_e) = strip_lets rst nms in
        (final_nms, E.LetExpr (p, nm, vl, final_e))
    | _ -> (nms, e)
  and get_prop_pairs nms uids prs = 
    let getter uid = 
      S.Lambda (p, ["this"; "args"], 
        S.Label (p, "%ret",
          S.Break (p, "%ret", S.Id (p, uid))))
    and setter uid =
      let newval = S.GetField (p, S.Id (p, "args"), S.String (p, "0"), noargs_obj) in
      let setterao = onearg_obj newval in
      S.Lambda (p, ["this"; "args"],
      S.Label (p, "%ret",
      S.Break (p, "%ret",
      S.SetBang (p, uid, newval)))) in
    match nms, uids with
    | [], [] -> prs
    | nm :: rest, uid :: uid_rest ->
      let arc = { S.getter = getter uid; S.setter = setter uid; } in
      let a = S.Accessor (arc, false, false) in
      get_prop_pairs rest uid_rest ((nm, a) :: prs) in
  let c_attrs = { 
    S.primval = None;
    S.code = None; 
    S.proto = parent;
    S.klass = "Object";
    S.extensible = true; } in
  let (nl, real_body) = strip_lets body [] in
  let uids = List.map (fun nm -> mk_id nm) nl in
  let prop_pairs = get_prop_pairs nl uids [] in
  (uids, real_body, S.Object (p, c_attrs, prop_pairs))

and get_lambda p args body = 
  let (uids, real_body, ncontext) = create_context p body (Some (S.Id (p, "%parent"))) in
  let desugared = ejs_to_ljs real_body in
  let final = 
    S.Seq (p,
      S.SetField (p, S.Id (p, "%context"), S.String (p, "arguments"), S.Id (p,
      "%args"), onearg_obj (S.Id (p, "%args"))), desugared) in
  let param_len = List.length args in
  let indices = Prelude.iota param_len in
  let combined = List.combine indices args in
  let seq_chain = get_chain p combined final in
  let seq_chain_end = S.Seq (p, seq_chain, S.Undefined p) in
  S.Lambda (p, ["%this"; "%args"],
    S.Label (p, "%ret",
      get_prop_lets p uids (S.Let (p, "%context", ncontext, seq_chain_end))))

and prm_to_setfield p n prm =
  let argsobj = S.Object (p, S.d_attrs, []) in
  let update = 
    S.GetField (p, S.Id (p, "%args"), S.String (p, string_of_int n), argsobj)
  and field = 
    S.GetField (p, S.Id (p, "%params"), S.String (p, string_of_int n), argsobj) in
  S.Seq (p, 
  S.SetField (p, S.Id (p, "%context"), field, update, onearg_obj update),
  S.SetAttr (p, S.Config, S.Id (p, "%context"), field, S.False (p)))

and fv_to_setfield p v = 
  let arec = { S.value = S.Undefined (p); S.writable = true; } in
  let aprop = S.Data (arec, true, true) in
  let argsobj = S.Object (p, S.d_attrs, [(v, aprop)]) in
  S.SetField (p, S.Id (p, "%context"), S.String (p, v), S.Undefined (p),
  argsobj)

and get_chain p params final = match params with
  | [] -> final
  | (n, first) :: rest ->
    let a = prm_to_setfield p n (List.hd params) 
    and b = get_chain p (List.tl params) final in
    S.Seq (p, a, b)

and get_fv_chain p fvs final = match fvs with
  | [] -> final
  | first :: rest ->
    let a = fv_to_setfield p first
    and b = get_fv_chain p rest final in
    S.Seq (p, a, b)

and remove_dupes lst =
  let rec helper l seen result = match l with
    | [] -> result
    | first :: rest ->
      let next = if (List.mem first seen) then result else (first :: result) in
      helper rest (first :: seen) next in
  helper lst [] []

and get_while tst bdy =
  let p = dummy_pos in
  let tst = S.Lambda (p, [], tst)
  and bdy = S.Lambda (p, [], bdy) in
  S.Rec (p, "%while",
    S.Lambda (p, ["%tst"; "%bdy"],
      S.Let (p, "%result", S.App (p, tst, []),
        S.If (p, S.Id (p, "%result"),
          S.Seq (p, S.App (p, S.Id (p, "%bdy"), []), 
          S.App (p, S.Id (p, "%while"), [S.Id (p, "%tst"); S.Id (p, "%bdy")])),
          S.Undefined (p)))),
    S.App (p, S.Id (p, "%while"), [tst; bdy]))

and prop_itr = 
  let p = dummy_pos in
  let tst =
    S.Op2 (p, "hasOwnProperty", 
      S.Id (p, "%obj"), 
      S.Op1 (p, "prim->str", S.Id (p, "%index")))
  and cns = 
    S.Let (p, "%rval",
    S.GetField (p, S.Id (p, "%obj"), S.Op1 (p, "prim->str", S.Id (p, "%index")),
    S.Null (p)),
    S.Seq (p,
    S.SetBang (p, "%index", S.Op2 (p, "+", S.Id (p ,"%index"), S.Num (p, 1.))),
    S.Id (p, "%rval"))) in
  S.Lambda (p, ["%obj"],
    S.Let (p, "%index", S.Num (p, 0.),
      S.Lambda (p, [],
        S.If (p, tst, cns, S.Undefined (p)))))

and get_forin p nm robj bdy = (* TODO: null args object below!! *)
  let context = S.Id (p, "%context")
  and nms = S.String (p, nm) in
  let tst =
    S.Op1 (p, "!", 
    S.Op2 (p, "stx=", 
      S.GetField (p, context, nms, S.Null (p)), 
      S.Undefined (p)))
  and wbdy = 
    S.Seq (p, bdy, 
           make_set_field p context nms (S.App (p, S.Id (p, "%prop_itr"), []))) in
  let doloop_id = mk_id "do_loop" in
  S.Let (p, doloop_id,
    S.Lambda (p, [], 
      S.Rec (p, "%get_itr", prop_itr,
      S.Let (p, "%pnameobj", S.Op1 (p, "property-names", robj),
      S.Let (p, "%prop_itr", S.App (p, S.Id (p, "%get_itr"), [S.Id (p, "%pnameobj")]),
      S.Seq (p, 
              S.App (p, 
                S.Id (p, "%set-property"), 
                [context; nms; S.App (p, S.Id (p, "%prop_itr"), [])]),
             get_while tst wbdy))))),
    S.If (p, S.Op2 (p, "stx=", robj, S.Undefined (p)),
      S.Undefined (p),
      S.If (p, S.Op2 (p, "stx=", robj, S.Null (p)),
        S.Undefined (p),
        S.App (p, S.Id (p, doloop_id), []))))

and appexpr_check f app p = 
  let ftype = mk_id "ftype" in
  let not_function =
    S.Op1 (p, "!", S.Op2 (p, "stx=", S.Id (p, ftype), S.String (p, "function"))) in
  let error = S.App (p, S.Id (p, "%ThrowTypeError"), [S.Null(p); S.Null(p)]) in
  S.Let (p, ftype, S.Op1 (p, "typeof", f),
    S.If (p, not_function, error, app))
    
let exprjs_to_ljs (e : E.expr) : S.exp =
  let p = dummy_pos in
  let (uids, real_body, ncontext) = create_context p e (Some (S.Id (p, "%global"))) in
  let desugared = ejs_to_ljs real_body in
  let final = 
    S.Let (p, "%this", S.Id (p, "%context"), desugared) in
  get_prop_lets p uids (S.Let (p, "%context", ncontext, final))
