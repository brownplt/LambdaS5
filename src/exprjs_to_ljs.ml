open Prelude

module E = Exprjs_syntax
module S = Es5_syntax

(*type expr = 
  | True of pos
  | False of pos
  | Num of pos * float
  | Undefined of pos
  | Null of pos
  | String of pos * string
  | ArrayExpr of pos * expr list
  | ObjectExpr of pos * (pos * string * prop) list
  | ThisExpr of pos
  | VarExpr of pos * id
  | IdExpr of pos * id
  | BracketExpr of pos * expr * expr
  | NewExpr of pos * expr * expr list
  | PrefixExpr of pos * id * expr
  | InfixExpr of pos * id * expr * expr
  | IfExpr of pos * expr * expr * expr
  | AssignExpr of pos * expr * expr * expr
  | AppExpr of pos * expr * expr list
  | FuncExpr of pos * id list * expr
  | LetExpr of pos * id * expr * expr
  | SeqExpr of pos * expr * expr
  | WhileExpr of pos * expr * expr
  | LabelledExpr of pos * id * expr
  | BreakExpr of pos * id * expr
  | ForInExpr of pos * id * expr * expr
  | VarDeclExpr of pos * id * expr
  | TryCatchExpr of pos * expr * id * expr
  | TryFinallyExpr of pos * expr * expr
  | ThrowExpr of pos * expr
  | FuncStmtExpr of pos * id * id list * expr
  | HintExpr of pos * string * expr
and prop =
  | Data of expr
  | Getter of id * expr
  | Setter of id * expr
  *)

let rec exprjs_to_ljs (e : E.expr) : S.exp = match e with
  | E.True (p) -> S.True (p)
  | E.False (p) -> S.False (p)
  | E.Num (p, n) -> S.Num (p, n)
  | E.Undefined (p) -> S.Undefined (p)
  | E.Null (p) -> S.Null (p)
  | E.String (p, s) -> S.String (p, s)
  | E.ObjectExpr (p, pl) ->
    (* Given a tuple, if it's a getter/setter, create a name-accessor pair and add to
     * sofar *)
    let add_accessor pr sofar = match pr with
      | (_, _, E.Getter (nm, exp)) ->
        let gval = 
          get_accessor_fobj p [] exp (S.Id (p, "%context")) in
        let a = { S.getter = gval; S.setter = S.Undefined (p); } in
        (nm, S.Accessor (a, true, true)) :: sofar
      | (_, _, E.Setter (nm, exp)) -> failwith "setters nyi"
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
    S.Object (p, S.d_attrs, List.append reduced_assoc data_result)
  | E.IdExpr (p, nm) -> S.Id (p, nm)
  | E.BracketExpr (p, l, r) -> 
    let o = exprjs_to_ljs l
    and f = exprjs_to_ljs r in
    let normal = S.GetField (p, o, f, S.Null (p))
    and lookup = s_lookup f in
    let result = match l with
      | E.IdExpr (p, nm) -> if nm <> "%context" then normal else lookup
      | _ -> normal in
    result
  | E.PrefixExpr (p, op, exp) -> S.Op1 (p, op, exprjs_to_ljs exp)
  | E.InfixExpr (p, op, l, r) -> let op = match op with
    | "===" -> "abs="
    | "==" -> "stx="
    | _ -> op in
    S.Op2 (p, op, exprjs_to_ljs l, exprjs_to_ljs r)
  | E.IfExpr (p, e1, e2, e3) -> let e1 = exprjs_to_ljs e1
    and e2 = exprjs_to_ljs e2
    and e3 = exprjs_to_ljs e3 in S.If (p, e1, e2, e3)
  | E.AssignExpr (p, obj, pr, vl) -> 
    let sobj = exprjs_to_ljs obj
    and spr = exprjs_to_ljs pr
    and svl = exprjs_to_ljs vl in
    S.SetField (p, sobj, spr, svl, S.Null (p)) (* TODO: Args object is null for now *)
  | E.SeqExpr (p, e1, e2) -> S.Seq (p, exprjs_to_ljs e1, exprjs_to_ljs e2)
  | E.AppExpr (p, e, el) -> 
    let sl = List.map (fun x -> exprjs_to_ljs x) el
    and f = exprjs_to_ljs e in
    let fscope = match f with
      | S.Object (p, at, pl) -> 
        S.GetField (p, f, S.String (p, "%scope"), S.Null (p))
      | _ -> S.Id (p, "%context") in
    S.App (p, f, fscope :: sl)
  | E.FuncExpr (p, args, body) -> get_fobj p args body (S.Id (p, "%context"))
  | E.FuncStmtExpr (p, nm, args, body) -> 
    (* TODO: null Args object *)
    let fobj = get_fobj p args body (S.Id (p, "%context")) in
    S.SetField (p, S.Id (p, "%context"), S.String (p, nm), fobj, S.Null (p))
  | E.LetExpr (p, nm, vl, body) -> 
    let sv = exprjs_to_ljs vl
    and sb = exprjs_to_ljs body in
    S.Let (p, nm, sv, sb)
  | E.BreakExpr (p, id, e) ->
    S.Break (p, id, exprjs_to_ljs e)
  | _ -> failwith "unimplemented exprjs type"

(* 13.2 *)
and get_fobj p args body context = 
  let call = get_lambda p args body in
  let fobj_attrs = 
    { S.code = Some (call); S.proto = Some (S.Null (p)); S.klass = "Function"; 
    S.extensible = true; }
  and scope_prop =
    ("%scope", S.Data ({ S.value = context; S.writable = false; }, false,
    false)) in
  S.Object (p, fobj_attrs, [scope_prop])

(* 13.2.1 *)
and get_lambda p args body = 
  (* TODO: binding for "this" in new context *)
  let arg_to_prop arg = 
      (arg, S.Data ({ S.value = S.Id (p, arg); S.writable = true; }, true, true)) in
    let rec ncontext_aprops = List.map (fun arg -> arg_to_prop arg) args
    and parent_prop = 
      ("%parent", S.Data ({ S.value = S.Id (p, "%parent"); S.writable = false; }, 
      true, true))
    and ncontext_props = parent_prop :: ncontext_aprops
    and ncontext = S.Object (p, S.d_attrs, ncontext_props) in
    let rec inner_body = exprjs_to_ljs body
    and inner_let = S.Let (p, "%context", ncontext, inner_body)
    and inner_lbl = S.Label (p, "%ret", inner_let) in
    S.Lambda (p, "%parent" :: args, inner_lbl)

and get_accessor_fobj p args body context = 
  let call = get_accessor_lambda p args body in
  let fobj_attrs = 
    { S.code = Some (call); S.proto = Some (S.Null (p)); S.klass = "Function"; 
    S.extensible = true; }
  and scope_prop =
    ("%scope", S.Data ({ S.value = context; S.writable = false; }, false,
    false)) in
  S.Object (p, fobj_attrs, [scope_prop])

and get_accessor_lambda p args body = 
  (* TODO: binding for "this" in new context *)
  let arg_to_prop arg = 
      (arg, S.Data ({ S.value = S.Id (p, arg); S.writable = true; }, true, true)) in
    let rec ncontext_aprops = List.map (fun arg -> arg_to_prop arg) args
    and parent_prop = 
      ("%parent", S.Data ({ S.value = S.Id (p, "%parent"); S.writable = false; }, 
      true, true))
    and ncontext_props = parent_prop :: ncontext_aprops
    and ncontext = S.Object (p, S.d_attrs, ncontext_props) in
    let rec inner_body = exprjs_to_ljs body
    and inner_lbl = S.Label (p, "%ret", inner_body) in
    S.Lambda (p, "%parent" :: args, inner_lbl)

and s_lookup prop =
  let p = dummy_pos in
    S.Rec (p, "lookup",
    S.Lambda (p, ["k"; "obj";], 
      S.If (p, 
        S.Op2 (p, "stx=", S.Id (p, "obj"), S.Undefined (p)),
        S.Undefined (p),
        S.Let (p, "f", 
          S.GetField (p, S.Id (p, "obj"), S.Id (p, "k"), S.Null (p)),
          S.If (p, S.Op2 (p, "stx=", S.Id (p, "f"), S.Undefined (p)),
            S.App (p, S.Id (p, "lookup"), 
              [S.Id (p, "k"); 
              S.GetField (p, S.Id (p, "obj"), S.String(p, "%parent"), S.Null (p));]),
            S.Id (p, "f"))))),
    S.App (p, S.Id (p, "lookup"), [prop; S.Id (p, "%context");]))

and remove_dupes lst =
  let rec helper l seen result = match l with
    | [] -> result
    | first :: rest ->
      let next = if (List.mem first seen) then result else (first :: result) in
      helper rest (first :: seen) next in
  helper lst [] []
