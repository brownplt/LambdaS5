open Prelude

module E = Exprjs_syntax
module S = Ljs_syntax

let idx = ref 0

let mk_id str = 
  idx := !idx + 1;
  "%" ^ str ^ (string_of_int !idx)

let undef_test p v =
  S.Op2 (p, "stx=", v, S.Undefined p)

let null_test p v =
  S.Op2 (p, "stx=", v, S.Null p)

let type_test p v typ =
  S.Op2 (p, "stx=", S.Op1 (p, "typeof", v), S.String (p, typ))

let is_object_type p o =
  S.If (p, type_test p o "object", S.True (p), type_test p o "function")

let throw_typ_error p msg =
  S.App (p, S.Id (p, "%ThrowTypeError"), [S.Null (p); S.String (p, msg)])

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
                     S.proto = Some (S.Id (p, "%RegExpProto"));
                     S.klass = "RegExp"; (* correct? *)
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
          | S.Accessor (aa, _, _) -> aa
          | _ -> failwith "Fatal: non-accessor in exprjs_to_ljs.reduce" in
        let next = match a with
          | { S.getter = S.Undefined _; S.setter = s; } ->
            S.Accessor ({ S.getter = result_a.S.getter; S.setter = s; }, wr, cfg)
          | { S.getter = g; S.setter = S.Undefined _; } ->
            S.Accessor ({ S.getter = g; S.setter = result_a.S.setter; }, wr, cfg)
          | _ -> S.Accessor (a, wr, cfg) in
        reduce rest next
      | _ -> failwith "Fatal: exprjs_to_ljs.reduce given non-accessors" in
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
      S.If (p, S.Op1 (p, "!", type_test p (S.Id (p, constr_id)) "function"),
        throw_typ_error p "Constructor was not a function", 
        S.Let (p, pr_id, S.GetField (p, S.Id (p, constr_id), 
                           S.String (p, "prototype"), getterargs),
          S.If (p, undef_test p (S.Id (p, pr_id)),
            throw_typ_error p "prototype was not defined in new expression",
            S.Seq (p,
              S.If (p, S.Op1 (p, "!", is_object_type p (S.Id (p, pr_id))),
                S.SetBang (p, pr_id, S.Id (p, "%ObjectProto")), S.Undefined p),
            S.Let (p, newobj, S.Object (p, { S.d_attrs with S.proto = Some (S.Id (p, pr_id)) }, []),
              S.If (p, null_test p (S.GetObjAttr (p, S.Code, S.Id (p, constr_id))),
                    throw_typ_error p "Constructor was not applicable",
                    S.Let (p, constr_result, S.App (p, S.Id (p, constr_id), [S.Id (p, newobj); constrargs]),
                    S.If (p, is_object_type p (S.Id (p, constr_result)),
                      S.Id (p, constr_result),
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
          S.Op1 (p, "typeof", S.GetField (p, context, fldexpr, noargs_obj (Pos.synth p)))
        | _ -> S.Op1 (p, "typeof", target)
      end
    | "delete" -> let result = match exp with
      | E.BracketExpr (pp, obj, fld) -> 
        let fld_id = mk_id "fld" in
        let fld_str = S.Op1 (p, "prim->str", ejs_to_ljs fld)
        and sobj = ejs_to_ljs obj in
        (* TODO(joe): unused var --- what's it doing here? *)
        (* let null = S.Null (pp) in *)
        begin match sobj with
          | S.Id (_, "%context") ->
            let null = S.Null (p) in
            S.App (pp, S.Id (pp, "%ThrowSyntaxError"), [null; null])
          | _ ->
            S.Let (p, fld_id, fld_str,
              S.If (p, S.Op2 (p, "hasProperty", sobj, S.Id (p, fld_id)),
                S.If (p,
                  S.GetAttr (pp, S.Config, sobj, S.Id (p, fld_id)),
                  S.DeleteField (pp, sobj, S.Id (p, fld_id)),
                  throw_typ_error p "Deleting non-configurable field"),
                S.True (p)))
        end
      | _ -> S.True (p) in result
    | "-" -> S.App(p, S.Id (p, "%UnaryNeg"), [ejs_to_ljs exp])
    | "+" -> S.App (p, S.Id (p, "%UnaryPlus"), [ejs_to_ljs exp])
    | "~" -> S.App (p, S.Id (p, "%BitwiseNot"), [ejs_to_ljs exp])
    | _ -> S.Op1 (p, op, ejs_to_ljs exp) in result
  | E.InfixExpr (p, op, l, r) ->
    let op_func =
      S.Lambda (p, ["a"; "b"],
        S.Op2 (p, op, S.Id (p, "a"), S.Id (p, "b"))) in
    let sl = ejs_to_ljs l and sr = ejs_to_ljs r in
    begin match op with
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
      | "<<" -> S.App (p, S.Id (p, "%LeftShift"), [sl; sr])
      | ">>" -> S.App (p, S.Id (p, "%SignedRightShift"), [sl; sr])
      | ">>>" -> S.App (p, S.Id (p, "%UnsignedRightShift"), [sl; sr])
      | "&" | "^" | "|" -> 
        S.App (p, S.Id (p, "%BitwiseInfix"), [sl; sr; op_func])
      | "*" | "%" | "/" -> 
        S.App (p, S.Id (p, "%PrimMultOp"), [sl; sr; op_func])
      | "<" -> S.App (p, S.Id (p, "%LessThan"), [sl; sr])
      | ">" -> S.App (p, S.Id (p, "%GreaterThan"), [sl; sr])
      | "<=" -> S.App (p, S.Id (p, "%LessEqual"), [sl; sr])
      | ">=" -> S.App (p, S.Id (p, "%GreaterEqual"), [sl; sr])
      | "instanceof" -> S.App (p, S.Id (p, "%instanceof"), [sl; sr])
      | "in" -> S.App (p, S.Id (p, "%in"), [sl; sr])
      | "===" -> S.Op2 (p, "stx=", sl, sr)
      | _ -> failwith ("fatal: unknown infix operator: " ^ op)
    end
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
    let sl = List.map ejs_to_ljs el in
    let args_obj = make_args_obj p sl in
    let obj_id = mk_id "obj" in
    let fun_id = mk_id "fun" in
    begin match e with
      | E.BracketExpr (_, E.IdExpr (_, "%context"), E.String (_, "eval")) ->
        S.App (p, S.Id (p, "%maybeDirectEval"), [S.Id (p, "%this"); S.Id (p, "%context"); args_obj])
      | E.BracketExpr (_, E.IdExpr (_, "%context"), _) ->
        S.Let (p, fun_id, ejs_to_ljs e,
          appexpr_check (S.Id (p, fun_id))
          (S.App (p, S.Id (p, fun_id), [S.Undefined (p); args_obj]))
          p)
      | E.BracketExpr (_, obj, fld) ->
        let flde = ejs_to_ljs fld in
        S.Let (p, obj_id, ejs_to_ljs obj, 
          S.Let (p, fun_id, make_get_field p (to_object p (S.Id (p, obj_id))) (to_string p flde),
            appexpr_check (S.Id (p, fun_id))
            (S.App (p, S.Id (p, fun_id), [to_object p (S.Id (p, obj_id)); args_obj]))
            p))
      | E.FuncExpr _
      | _ ->
        S.Let (p, fun_id, ejs_to_ljs e,
          appexpr_check (S.Id (p, fun_id))
          (S.App (p, S.Id (p, fun_id), [S.Undefined (p); args_obj]))
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
    let t = ejs_to_ljs tst in
    let (b, after) = match bdy with
      | E.LetExpr (p, "%%after", after, real_bdy) ->
        (ejs_to_ljs real_bdy, ejs_to_ljs after)
      | _ -> (ejs_to_ljs bdy, S.Undefined (p)) in
    get_while (Pos.synth p) t b after
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
  | E.SwitchExpr (p, d, cl) ->

    let or' a b = 
      S.If (p, a, S.True (p), b) in
    let and' a b =
      S.If (p, a, b, S.False (p)) in
    let disc_id = mk_id "disc" in
    let disc = S.Id (p, disc_id) in

    if List.exists (fun c -> match c with E.Default _ -> true | _ -> false) cl
    then

      let (a_clauses, default , b_clauses ) =
        let (a_clauses, rest) = take_while (function
          | E.Default _ -> false
          | _ -> true) cl in
        let (default, b_clauses) = match rest with
          | [] -> None, []
          | hd::tl -> Some hd, tl in
        (a_clauses, default, b_clauses) in
        
      let rec loop i case = function
        | [] -> S.Null (p)
        | [a] -> case i a
        | a :: rest -> S.Seq (p, case i a, loop (i+1) case rest) in

      let case_to_ljs = function 
        | E.Case (p, test, body) ->
          (ejs_to_ljs test, ejs_to_ljs body)
        | _ -> failwith "no default" in

      let default_to_ljs = function 
        | Some (E.Default (p, body)) -> ejs_to_ljs body
        | _ -> failwith "Fatal: default_to_ljs received non-default expr" in

      let step5 rest = 
        let step5iter caseCount (tst, bdy) =
          S.Seq (p,
            S.If (p, 
              (and' (S.Op2 (p, "stx=", S.Id (p, "%found"), S.False (p)))
                    (S.Op2 (p, "stx=", disc, tst))),
              S.SetBang (p, "%found", S.True (p)),
              S.Null (p)),
            S.If (p, 
              S.Id (p, "%found"),
              bdy,
              S.Null (p))) in
        S.Let (p, "%found", S.False (p), 
          S.Seq (p, 
            loop 0 step5iter (map case_to_ljs a_clauses),
            rest)) in

      let step6 rest = 
        S.Let (p, "%foundInB", S.False (p), rest) in

      let step7 rest = 
        let step7iter caseCount (tst, bdy) =
          (* This is what we think browsers are doing
          S.If (p, 
            (and' (S.Op2 (p, "stx=", S.Id (p, "%foundInB"), S.False (p)))
                  (S.Op2 (p, "stx=", disc, tst))),
            S.Seq (p,
              S.SetBang (p, "%foundInB", S.True (p)),
              S.Seq (p, 
                S.SetBang (p, "%casecount", S.Num(p, float_of_int caseCount)),
                bdy)),
            S.Null (p)) in
          *)
          (* This is what the spec says *)
          S.If (p,
            S.Op2 (p, "stx=", S.Id (p, "%foundInB"), S.False (p)),
            S.Seq (p,
              S.SetBang (p, "%casecount", S.Num (p, float_of_int caseCount)),
              S.If (p, 
                S.Op2 (p, "stx=", disc, tst),
                S.Seq (p,
                  S.SetBang (p, "%foundInB", S.True (p)),
                  bdy),
                S.Null (p))),
            S.Null (p)) in
        S.Let (p, "%casecount", S.Num (p, -1.),
          S.Seq (p, 
            S.If (p, 
              S.Id (p, "%found"), 
              S.Null (p),
              loop 0 step7iter (map case_to_ljs b_clauses)),
            rest)) in

      let step8 rest = 
        S.Seq (p, 
          S.If (p, 
            S.Id (p, "%foundInB"), 
            S.Null (p),
            default_to_ljs default),
          rest) in

      let step9 =
        let step9iter caseCount (tst, bdy) =
          S.If (p,
            S.Op2 (p, "<", S.Id (p, "%casecount"), S.Num (p,
            float_of_int(caseCount))),
            bdy,
            S.Null (p)) in
        loop 0 step9iter (map case_to_ljs b_clauses) in
      S.Label (p, "%before",
        S.Let(p, disc_id, ejs_to_ljs d, step5 (step6 (step7 (step8 step9)))))

    else
      let case = function
        | E.Case (p, test, body) ->
          let stest = ejs_to_ljs test
          and sbody = ejs_to_ljs body in
          S.If (p, 
            (or' (S.Op2 (p, "stx=", disc, stest)) (S.Id (p,"%fallthrough"))),
            S.Seq (p, 
              S.SetBang (p, "%fallthrough", S.True (p)),
              sbody),
            S.Null (p))
        | _ -> failwith "desugaring error: found default case" in
      let rec cl_to_seq = function
        | [] -> S.Undefined (p)
        | [c] -> case c
        | c :: rest -> S.Seq (p, case c, cl_to_seq rest) in
      S.Label (p, "%before",
        S.Let (p, "%fallthrough", S.False (p),
          S.Let (p, disc_id, ejs_to_ljs d,
            cl_to_seq cl)))
  | E.HintExpr _ -> failwith "Bizarre error: Hint found somehow"

and a_attrs pos = {
  S.primval = None;
      S.code = None;
      S.proto = Some (S.Id (pos, "%ArrayProto"));
      S.klass = "Array";
      S.extensible = true; }

and noargs_obj pos = S.Object (pos, a_attrs pos, [])

and onearg_obj pos a = 
  let r = { S.value = a; S.writable = true; } in
  let p = S.Data (r, true, true) in
  S.Object (pos, a_attrs pos, [("0", p)])

and get_fobj p args body context =
  let contains_illegals = 
    List.exists (fun nm -> (nm = "arguments") || (nm = "eval")) args in
  let uargs = remove_dupes args in
  if (uargs <> args) || contains_illegals then
    S.App (p, S.Id (p, "%ThrowTypeError"), [S.Null (p); S.Null (p)]) else
  let call = get_lambda p args body in
  let fproto = S.Id (p, "%FunctionProto") in
  let fobj_attrs =
    { S.primval = None; S.code = Some (call); S.proto = Some (fproto); S.klass = "Function"; 
    S.extensible = true; } in
  let param_len = List.length args in
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
               S.Let (p, func_id, S.Object (p, fobj_attrs, [("prototype", proto_prop); ("length", length_prop)]),
                      S.Seq (p, S.SetField (p, S.Id (p, proto_id), S.String (p, "constructor"), S.Id (p, func_id), S.Null p),
                             S.Id (p, func_id)))))
           
and strip_lets e nms = match e with
  | E.LetExpr (p, nm, vl, rst) ->
    let prefix = if (String.length nm) >= 2 then String.sub nm 0 2 else "" in
    if prefix = "%%" then
      let l = (String.length nm) - 2 in
      let next_nms = (String.sub nm 2 l) :: nms in strip_lets rst next_nms
    else
      let (final_nms, final_e) = strip_lets rst nms in
      (final_nms, E.LetExpr (p, nm, vl, final_e))
  | _ -> (nms, e)

(* The first stage of desugaring creates exprjs let expressions corresponding
 * to JavaScript declared variables.  create_context is used to translate those
 * variables into the final representation (let-bound es5 variables with
 * randomly generated names, that are read/written by context object accessor
 * properties with the "real" name)
 *)
(* TODO(joe): overlapping vars and argument names goes here *)
and create_context p args body parent =
  let rec add_props props e =
    List.fold_right (fun prop e -> S.Let (p, prop, S.Undefined p, e)) props e
  and add_arg param index e = S.Let (p, param, S.GetField (p, S.Id (p, "%args"), S.String (p, string_of_int index), S.Null p), e)
  and add_args args' e = List.fold_right2 add_arg args' (Prelude.iota (List.length args')) e
  and get_prop_pairs nms uids prs = 
    let getter uid = 
      S.Lambda (p, ["this"; "args"], 
        S.Label (p, "%ret",
          S.Break (p, "%ret", S.Id (p, uid))))
    and setter uid =
      let newval = S.GetField (p, S.Id (p, "args"), S.String (p, "0"), noargs_obj (Pos.synth p)) in
      (* TODO(joe): unused variable: what's it doing here? *)
      (* let setterao = onearg_obj newval in *)
      S.Lambda (p, ["this"; "args"],
      S.Label (p, "%ret",
      S.Break (p, "%ret",
      S.SetBang (p, uid, newval)))) in
    match nms, uids with
    | [], [] -> prs
    | nm :: rest, uid :: uid_rest ->
      let arc = { S.getter = getter uid; S.setter = setter uid; } in
      let a = S.Accessor (arc, false, false) in
      get_prop_pairs rest uid_rest ((nm, a) :: prs)
    | _ -> failwith "Fatal: unmatched id/arg lengths in create_context" in
  let c_attrs = { 
    S.primval = None;
    S.code = None; 
    S.proto = parent;
    S.klass = "Object";
    S.extensible = true; } in
  let (nl, real_body) = strip_lets body [] in
  let uids = List.map mk_id nl in
  let uids' = List.map mk_id args in
  let prop_pairs = get_prop_pairs (nl@args) (uids@uids') [] in
  (* TODO(joe): is data good enough here?  what about using arguments
   * in a catch block? *)
  let arg_prop = ("arguments", S.Data ({
    S.value = S.Id (p, "%args");
    S.writable = true;
  }, false, false)) in
  (uids, real_body, (add_props uids (add_args uids' (S.Object (p, c_attrs, arg_prop::prop_pairs)))))

and get_lambda p args body = 
  let (uids, real_body, ncontext) = create_context p args body (Some (S.Id (p, "%parent"))) in
  let desugared = ejs_to_ljs real_body in
  S.Lambda (p, ["%this"; "%args"],
    S.Label (p, "%ret",
      S.Let (p, "%context", ncontext, S.Seq (p, desugared, S.Undefined (p)))))

and remove_dupes lst =
  let rec helper l seen result = match l with
    | [] -> result
    | first :: rest ->
      let next = if (List.mem first seen) then result else (first :: result) in
      helper rest (first :: seen) next in
  List.rev (helper lst [] [])

and get_while p tst body after =
  (* This is to insert the label (if it exists) at 
   * the correct location in the desugared code *)
  let real_body = match body with
    | S.Label (_, nm, 
        S.Seq (_, init, 
          S.Label (_, 
            before, 
            S.Rec (_, 
              whilenm, 
              S.Lambda (_, 
                args, 
                S.Let (_, 
                  resultnm, 
                  testapp, 
                  S.If (_, 
                    result, 
                    S.Seq (_, 
                      S.Label (_, clbl, bdyapp),
                      e2),
                    e3))),
              whileapp)))) ->
      S.Seq (p, init, 
        S.Label (p, 
          before, 
          S.Rec (p, 
            whilenm, 
            S.Lambda (p, 
              args, 
              S.Let (p, 
                resultnm, 
                testapp, 
                S.If (p, 
                  result, 
                  S.Seq (p, 
                    S.Label (p, nm, bdyapp),
                    e2),
                  e3))),
            whileapp)))
    | _ -> body in
  let test = match tst with
    | S.Label (_, "%%dowhile", real_test) ->
      let ft_id = mk_id "firsttest" in
      S.Let (p, ft_id, S.True (p),
        S.Lambda (p, [],
          S.If (p, S.Id (p, ft_id),
            S.Seq (p, S.SetBang (p, ft_id, S.False (p)), S.True (p)),
            real_test)))
    | _ -> S.Lambda (p, [], tst)
  and bdy = S.Lambda (p, [], real_body)
  and aftr = S.Lambda (p, [], after) in
  S.Rec (p, "%while",
    S.Lambda (p, ["%tst"; "%bdy"; "%after"],
      S.Let (p, "%result", 
        S.App (p, S.Id (p, "%ToBoolean"),
          [S.App (p, S.Id (p, "%tst"), [])]),
        S.If (p, S.Id (p, "%result"),
          S.Seq (p, 
            S.Label (p, "%continue", S.App (p, S.Id (p, "%bdy"), [])),
            S.Seq (p, 
              S.App (p, S.Id (p, "%after"), []),
              S.App (p, S.Id (p, "%while"), 
                [S.Id (p, "%tst"); S.Id (p, "%bdy"); S.Id (p, "%after")]))),
          S.Undefined (p)))),
    S.App (p, S.Id (p, "%while"), [test; bdy; aftr]))

and prop_itr p = 
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
    S.Op1 (p, "!", undef_test p (S.GetField (p, context, nms, S.Null (p))))
  and after =
    make_set_field p context nms (S.App (p, S.Id (p, "%prop_itr"), [])) in
  let doloop_id = mk_id "do_loop" in
  S.Let (p, doloop_id,
    S.Lambda (p, [], 
      S.Rec (p, "%get_itr", prop_itr (Pos.synth p),
      S.Let (p, "%pnameobj", S.App (p, S.Id (p, "%propertyNames"), [robj]),
      S.Let (p, "%prop_itr", S.App (p, S.Id (p, "%get_itr"), [S.Id (p, "%pnameobj")]),
      S.Seq (p, 
              S.App (p, 
                S.Id (p, "%set-property"), 
                [context; nms; S.App (p, S.Id (p, "%prop_itr"), [])]),
             get_while (Pos.synth p) tst bdy after))))),
    S.If (p, undef_test p robj,
      S.Undefined (p),
      S.If (p, S.Op2 (p, "stx=", robj, S.Null (p)),
        S.Undefined (p),
        S.App (p, S.Id (p, doloop_id), []))))

and appexpr_check f app p = 
  let ftype = mk_id "ftype" in
  let not_function =
    S.Op1 (p, "!", S.Op2 (p, "stx=", S.Id (p, ftype), S.String (p, "function"))) in
  let error = throw_typ_error p "Not a function" in 
  S.Let (p, ftype, S.Op1 (p, "typeof", f),
    S.If (p, not_function, error, app))

let add_preamble p used_ids var_ids final = 
  let define_id id =
    S.App (p, S.Id (p, "%defineGlobalAccessors"), [S.Id (p, "%context"); S.String (p, id)]) in
  let define_var id =
    S.App (p, S.Id (p, "%defineGlobalVar"), [S.Id (p, "%context"); S.String (p, id)]) in
  let rec dops_of_ids def_fun lst base = match lst with
    | [] -> base
    | id :: rest -> S.Seq (p, def_fun id, dops_of_ids def_fun rest base) in
  dops_of_ids define_var var_ids (dops_of_ids define_id used_ids final)

let rec is_strict_mode exp = match exp with
  | S.Seq (_, S.String (_, "use strict"), _) -> true
  | S.Seq (_, S.String _, exp) -> is_strict_mode exp
  | _ -> false

let exprjs_to_ljs p (used_ids : IdSet.t) (e : E.expr) : S.exp =
  let (names, inner) = strip_lets e [] in
  let desugared = ejs_to_ljs inner in
  let binder =
    if is_strict_mode desugared then "%strictContext" else "%nonstrictContext" in
  S.Let (p, "%context", S.Id (p, binder),
    add_preamble p (IdSet.elements used_ids) names desugared)

