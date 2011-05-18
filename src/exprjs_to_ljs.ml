open Prelude

module E = Exprjs_syntax
module S = Es5_syntax

let idx = ref 0

let mk_id str = 
  idx := !idx + 1;
  "%" ^ str ^ (string_of_int !idx)

let make_args_obj p args =
    let n_args = List.length args in
    let indices = Prelude.iota n_args in
    let combined = List.combine indices args in
    let records =
      List.map (fun (n, arg) -> (n, {S.value = arg; S.writable = true})) combined in
    let props = 
      List.map 
        (fun (n, rcrd) -> (string_of_int n, S.Data (rcrd, true, true))) records in
    let a_attrs = {
        S.code = None;
        S.proto = Some (S.Id (p, "%ArrayProto"));
        S.klass = "Array";
        S.extensible = true; } in
    let lfloat = float_of_int (List.length props) in
    let l_prop = (* TODO: is array length prop writ/enum/configurable? *)
      S.Data (
        { S.value = S.Num (p, lfloat); S.writable = true; },
        false,
        false) in
    S.Object (p, a_attrs, ("length", l_prop) :: props)

let rec exprjs_to_ljs (e : E.expr) : S.exp = match e with
  | E.True (p) -> S.True (p)
  | E.False (p) -> S.False (p)
  | E.Num (p, n) -> S.Num (p, n)
  | E.Undefined (p) -> S.Undefined (p)
  | E.Null (p) -> S.Null (p)
  | E.String (p, s) -> S.String (p, s)
  | E.RegExpr (p, s) -> 
    let re_attrs = { S.code = None;
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
    let desugared = List.map exprjs_to_ljs el
    and a_attrs = {
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
        (nm, S.Accessor (a, true, true)) :: sofar
      | (_, _, E.Setter (nm, exp)) ->
        let (param_name, sfunc) = match exp with
          | E.LetExpr (_, nm, _, body) -> (nm, body)
          | _ -> failwith "setter desugaring error: expected LetExpr here" in
        let sval = get_fobj p [param_name] sfunc (S.Id (p, "%context")) in
        let a = { S.getter = S.Undefined (p); S.setter = sval; } in
        (nm, S.Accessor (a, true, true)) :: sofar
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
          let rec v = exprjs_to_ljs e
          and d = { S.value = v; S.writable = true; } in
          S.Data (d, true, true)
      | E.Getter (nm, e) -> failwith "getters unimplemented"
      | E.Setter (nm, e) -> failwith "setters unimplemented"
    and tuple_to_prop t = match t with
      (p, s, pr) -> (s, ejsprop_to_sprop pr)
    and form_props props = match props with
      | [] -> []
      | first :: rest -> (tuple_to_prop first) :: form_props rest in
    let data_result = form_props data_props in
    let o_attrs = {
      S.code = None;
      S.proto = Some (S.Id (p, "%ObjectProto"));
      S.klass = "Object";
      S.extensible = true; } in
    S.Object (p, o_attrs, List.append reduced_assoc data_result)
  | E.ThisExpr (p) -> S.Id (p, "%this")
  | E.IdExpr (p, nm) -> S.Id (p, nm)
  | E.BracketExpr (p, l, r) -> 
    let o = exprjs_to_ljs l
    and f = S.Op1 (p, "prim->str", exprjs_to_ljs r) in
    let argsobj = S.Object (p, S.d_attrs, []) in
    S.GetField (p, o, f, argsobj)
  | E.NewExpr (p, econstr, eargs) -> 
    let constr_id = mk_id "constr" in
    let pr_id = mk_id "cproto" in
    let newobj = mk_id "newobj" in
    let constr_result = mk_id "constr_ret" in
    let getterargs = S.Object (p, S.d_attrs, []) in
    let constrargs = make_args_obj p (map exprjs_to_ljs eargs) in
    S.Let (p, constr_id, exprjs_to_ljs econstr,
           S.Let (p, pr_id, S.GetField (p, S.Id (p, constr_id), 
                                        S.String (p, "prototype"), getterargs),
                  S.Let (p, newobj, 
                         S.Object (p, { S.d_attrs with S.proto = Some (S.Id (p, pr_id)) }, []),
                         S.Let (p, constr_result,
                                S.App (p, S.Id (p, constr_id), [S.Id (p, newobj); constrargs]),
                                S.If (p, S.Op2 (p, "stx=", S.String (p, "object"), 
                                                S.Op1 (p, "typeof", S.Id (p, constr_result))),
                                      S.Id (p, constr_result),
                                      S.Id (p, newobj))))))
  | E.PrefixExpr (p, op, exp) -> let result = match op with
    | "postfix:++" ->
      let lhs = match exp with
        | E.BracketExpr (_, E.IdExpr (_, "%context"), E.String (_, nm)) ->
          S.String (p, nm)
        | _ -> failwith "postfix ++ not yet fully implemented"
      and sexp = exprjs_to_ljs exp in
      let bop = S.Op2 (p, "+", sexp, S.Num (p, 1.)) in
      let rec arecd = { S.value = bop; S.writable = true; }
      and aprop = S.Data (arecd, true, true)
      and aobj = S.Object (p, S.d_attrs, [("0", aprop)]) in
      S.SetField (p, S.Id (p, "%context"), lhs, bop, aobj)
    | "typeof" -> S.Op1 (p, "surface-typeof", exprjs_to_ljs exp)
    | _ -> S.Op1 (p, op, exprjs_to_ljs exp) in result
  | E.InfixExpr (p, op, l, r) ->
    let sl = exprjs_to_ljs l and sr = exprjs_to_ljs r
    and this = S.Id (p, "%this") in
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
      | "+" -> S.App (p, S.Id (p, "%PrimAdd"), [sl; sr])
      | _ -> let op = match op with
        | "===" -> "abs="
        | "==" -> "stx="
        | _ -> op in S.Op2 (p, op, sl, sr) in result
  | E.IfExpr (p, e1, e2, e3) -> let e1 = exprjs_to_ljs e1
    and e2 = exprjs_to_ljs e2
    and e3 = exprjs_to_ljs e3 in 
    S.If (p, 
      S.App (p, S.Id (p, "%ToBoolean"), [e1]),
      e2, 
      e3)
  | E.AssignExpr (p, obj, pr, vl) -> 
    let sobj = exprjs_to_ljs obj
    and spr = exprjs_to_ljs pr
    and svl = exprjs_to_ljs vl in
    let arecd = { S.value = svl; S.writable = true; } in
    let aprop = S.Data (arecd, true, true) in
    let aobj = S.Object (p, S.d_attrs, [("0", aprop)]) in
    S.SetField (p, sobj, spr, svl, aobj)
  | E.AppExpr (p, e, el) -> 
    let sl = List.map (fun x -> exprjs_to_ljs x) el
    and f = exprjs_to_ljs e in 
    let this = match f with
      | S.GetField (p, l, r, args) -> l
      | _ -> S.Id (p, "%this") in
    let args_obj = make_args_obj p sl in
    S.App (p, f, [this; args_obj])
  | E.FuncExpr (p, args, body) -> get_fobj p args body (S.Id (p, "%context"))
  | E.LetExpr (p, nm, vl, body) ->
    let sv = exprjs_to_ljs vl
    and sb = exprjs_to_ljs body in
    let result_obj = match nm with
      | "%context" -> let orig_props = match sv with
        | S.Object (_, _, pl) -> pl
        | _ -> failwith "let bound %context to a non-object" in
        let c_attrs = { S.code = None;
                        S.proto = Some (S.Id (p, "%context"));
                        S.klass = "Object";
                        S.extensible = true; } in
        S.Object (p, c_attrs, orig_props)
      | _ -> sv in
    S.Let (p, nm, result_obj, sb)
  | E.SeqExpr (p, e1, e2) -> S.Seq (p, exprjs_to_ljs e1, exprjs_to_ljs e2)
  | E.WhileExpr (p, tst, bdy) ->
    let t = exprjs_to_ljs tst and b = exprjs_to_ljs bdy in get_while t b
  | E.LabelledExpr (p, lbl, exp) -> S.Label (p, lbl, exprjs_to_ljs exp)
  | E.BreakExpr (p, id, e) -> S.Break (p, id, exprjs_to_ljs e)
  | E.ForInExpr (p, nm, vl, bdy) ->
    get_forin p nm (exprjs_to_ljs vl) (exprjs_to_ljs bdy)
  | E.TryCatchExpr (p, body, ident, catch) -> 
    let new_ctxt = 
      S.Object (p, { S.d_attrs with S.proto = Some (S.Id (p, "%parent")) },
                [(ident, 
                  S.Data ({ S.value = S.Id (p, ident); S.writable = true }, 
                         false, false) );])
    in
    S.TryCatch (p, exprjs_to_ljs body, 
                S.Lambda(p, [ident], 
                         S.Let (p, "%parent", S.Id (p, "%context") ,
                                S.Let (p, "%context", new_ctxt, 
                                       exprjs_to_ljs catch))))
  | E.FuncStmtExpr (p, nm, args, body) -> 
    let fobj = get_fobj p args body (S.Id (p, "%context")) in
    let arcrd = { S.value = fobj; S.writable = true; } in
    let aprop = S.Data (arcrd, true, true) in
    let aprops = [("0", aprop)] in
    let argsobj = S.Object (p, S.d_attrs, aprops) in
    S.SetField (p, S.Id (p, "%context"), S.String (p, nm), fobj, argsobj)
  | E.TryFinallyExpr (p, body, finally) -> 
    S.TryFinally (p, exprjs_to_ljs body, exprjs_to_ljs finally)
  | E.ThrowExpr (p, e) -> S.Throw (p, exprjs_to_ljs e)
  | E.HintExpr _ -> failwith "Bizarre error: Hint found somehow"

and get_fobj p args body context = 
  let call = get_lambda p args body in
  let fproto = S.Id (p, "%FunctionProto") in
  let fobj_attrs = 
    { S.code = Some (call); S.proto = Some (fproto); S.klass = "Function"; 
    S.extensible = true; } in
  let param_len = List.length args in
  let indices = Prelude.iota param_len in
  let combined = List.combine indices args in
  let rcds =
    List.map (fun (n, prm) -> (n, {S.value = S.String (p, prm); S.writable =
      true;})) combined in
  let props =
    List.map (fun (n, rcd) -> (string_of_int n, S.Data (rcd, false, false)))
    rcds in
  let proto_prop = S.Data ({ S.value = S.Id (p, "%ObjectProto"); S.writable = true}, false, true) in
  let param_obj = S.Object (p, S.d_attrs, props) in
  S.Let (p, "%parent", context,
    S.Let (p, "%params", param_obj,
      S.Object (p, fobj_attrs, [("prototype", proto_prop)])))

and get_lambda p args body = 
  let getter nm = 
    S.Lambda (p, ["this"; "args"], 
    S.Label (p, "%ret",
    S.Break (p, "%ret",
    S.GetField (p, S.Id (p, "%context"), S.String (p, "%" ^ nm), S.Null (p)))))
  and setter nm =
    let newval = S.GetField (p, S.Id (p, "args"), S.String (p, "0"), S.Null (p)) in
    S.Lambda (p, ["this"; "args"],
    S.Label (p, "%ret",
    S.Break (p, "%ret",
    S.SetField (p, S.Id (p, "%context"), S.String (p, "%" ^ nm), 
      newval, S.Null (p))))) in
  (* Strip the lets from the top of the function body, and get a tuple containig
   * the name of all those ids (declared with var keyword) and the actual
   * function body *)
  let rec strip_lets e nms = match e with
    | E.LetExpr (p, nm, vl, rst) ->
      let prefix = String.sub nm 0 2 in
      if prefix = "%%" then
        let l = (String.length nm) - 2 in
        let next_nms = (String.sub nm 2 l) :: nms in strip_lets rst next_nms
      else
        let (final_nms, final_e) = strip_lets rst nms in
        (final_nms, E.LetExpr (p, nm, vl, final_e))
    | _ -> (nms, e) in
  (* For each name, create a data/accessor property *)
  let rec get_prop_pairs nms prs = match nms with
    | [] -> prs
    | nm :: rest ->
      let data_name = "%" ^ nm in
      let drc = { S.value = S.Undefined (p); S.writable = true; } in
      let d = S.Data (drc, true, true) in
      let arc = { S.getter = getter nm; S.setter = setter nm; } in
      let a = S.Accessor (arc, true, true) in
      get_prop_pairs rest ((data_name, d) :: ((nm, a) :: prs)) in
  let (nl, real_body) = strip_lets body [] in
  let prop_pairs = get_prop_pairs nl [] in
  let desugared = exprjs_to_ljs real_body in
  let final = 
    S.Seq (p,
      S.SetField (p, S.Id (p, "%context"), S.String (p, "arguments"), S.Id (p,
      "%args"), S.Null (p)), desugared) in
  let c_attrs = { S.code = None; 
    S.proto = Some (S.Id (p, "%parent"));
    S.klass = "Object";
    S.extensible = true; } in
  let ncontext = S.Object (p, c_attrs, prop_pairs) in
  let param_len = List.length args in
  let indices = Prelude.iota param_len in
  let combined = List.combine indices args in
  let seq_chain = get_chain p combined final in
  S.Lambda (p, ["%this"; "%args"],
    S.Label (p, "%ret",
      S.Let (p, "%context", ncontext, seq_chain)))

and prm_to_setfield p n prm =
  let argsobj = S.Object (p, S.d_attrs, []) in
  S.SetField (p, S.Id (p, "%context"), 
  S.GetField (p, S.Id (p, "%params"), S.String (p, string_of_int n), argsobj),
  S.GetField (p, S.Id (p, "%args"), S.String (p, string_of_int n), argsobj),
  S.Null (p))

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
    (*
    S.Seq (p, 
    S.SetBang (p, "%index", S.Op2 (p, "+", S.Id (p ,"%index"), S.Num (p, 1.))),
    S.GetField (p, S.Id (p, "%obj"), S.Op1 (p, "prim->str", S.Id (p, "%index")),
    S.Null (p))) in (* TODO: null args obj here!! *)
  *)
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
    S.SetField (p, context, nms, 
      S.App (p, S.Id (p, "%prop_itr"), []), S.Null (p))) in
  S.Rec (p, "%get_itr", prop_itr,
  S.Let (p, "%pnameobj", S.Op1 (p, "property-names", robj),
  S.Let (p, "%prop_itr", S.App (p, S.Id (p, "%get_itr"), [S.Id (p, "%pnameobj")]),
  S.Seq (p, 
    S.SetField (p, context, nms, S.App (p, S.Id (p, "%prop_itr"), []), S.Null (p)),
    get_while tst wbdy))))

