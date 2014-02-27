module E = Exprjs_syntax
module J = Js_syntax

open Prelude
open Js_pretty

open String

let idx = ref 0

let mk_id str = 
  idx := !idx + 1;
  "%" ^ str ^ (string_of_int !idx)

let split_regexp s =
  let before_flags = String.rindex s '/' in
  (* Index 1 always, because regexps look like /foo/g, so we cut off
   * the initial / *)
  let pattern = String.sub s 1 (before_flags - 1) in
  let flags = String.sub s (before_flags + 1) (((String.length s) - before_flags) - 1) in
  (pattern, flags)

let rec jse_to_exprjs (e : J.expr) : E.expr =
  match e with
    | J.This (p) -> E.ThisExpr (p)
    | J.Id (p, i) -> 
      E.BracketExpr(p, E.IdExpr (p, "%context"), E.String (p, i))
    | J.Lit (p, l) -> 
      let result = match l with 
        | J.Null -> E.Null (p)
        | J.Bool (b) -> if b then E.True (p) else E.False (p)
        | J.Num (n) -> E.Num (p, n)
        | J.Str (s) -> E.String (p, s) 
        | J.Regexp (s) ->
          let (pattern_part, flags_part) = split_regexp s in
          E.NewExpr (p, E.IdExpr (p, "%RegExpGlobalFuncObj"),
                     [E.String (p, pattern_part);
                      E.String (p, flags_part)])
      in result
  | J.Array (p, el) -> 
      E.ArrayExpr (p, List.map jse_to_exprjs el)
  | J.Object (p, mem_lst) ->
      let rec prop_to_str prop = match prop with
        (J.PropId s | J.PropStr s) -> s
        | J.PropNum n ->
          let maybedotted = string_of_float n in
          let i = String.length maybedotted in
          if String.get maybedotted (i - 1) == '.' 
            then String.sub maybedotted 0 (i - 1) 
            else maybedotted
      and m_to_pr m = match m with
        | J.Field (name, e) -> 
          (p, prop_to_str name, E.Data (jse_to_exprjs e))
        | J.Get (nm, sel) ->
          let name = prop_to_str nm and parent = E.IdExpr (p, "%context") in
          (p, name, E.Getter (name, srcElts p sel parent))
        | J.Set (nm, argnm, sel) ->
          let name = prop_to_str nm and parent = E.IdExpr (p, "%context") in
          let let_body = srcElts p sel parent in
          let inner_let = (* will be stripped off in next stage *)
            E.LetExpr (p, argnm, E.Undefined (p), let_body) in
          (p, name, E.Setter (name, inner_let)) in
      E.ObjectExpr(p, List.map m_to_pr mem_lst)
    | J.Paren (p, el) ->
      let rec unroll = function
        | [] -> E.Undefined (p)
        | [f] -> jse_to_exprjs f
        | f :: rest -> E.SeqExpr (p, jse_to_exprjs f, unroll rest) in
      unroll el
    | J.Func (p, nm, args, body) -> let parent = E.IdExpr (p, "%context") in
      let free_vars = IdSet.elements (J.fv_sel body) in
      let rec fvl_to_letchain fvl final = match fvl with
        | [] -> final
        | first :: rest -> let newnm = "%%" ^ first in
          E.LetExpr (p, newnm, E.Undefined (p), fvl_to_letchain rest final) in
      let last = srcElts p body parent in
      let wrapper = fvl_to_letchain free_vars in
      let fun_expr = match nm with
        | Some s ->
          let rec_obj = mk_id "rec_store" in
          let func_id = mk_id "rec_func" in
          E.LetExpr (p, rec_obj, E.ObjectExpr (p, [(p, "%rec_prop", E.Data (E.Undefined (p)))]),
          E.LetExpr (p, func_id,
            E.FuncExpr(p, args,
              E.LetExpr (p, "%%" ^ s, E.Undefined (p),
                wrapper
                  (E.SeqExpr (p, 
                    E.AssignExpr (p, 
                      E.IdExpr (p, "%context"), 
                      E.String (p, s), 
                      E.BracketExpr (p, E.IdExpr (p, rec_obj), E.String (p, "%rec_prop"))), 
                    last)))),
            E.SeqExpr (p,
              E.AssignExpr (p, E.IdExpr (p, rec_obj),
                               E.String (p, "%rec_prop"),
                               E.IdExpr (p, func_id)),
              E.IdExpr (p, func_id))))
        | None -> E.FuncExpr (p, args, wrapper last) in
      strict_wrapper p body fun_expr
    | J.Bracket (p, e1, e2) -> 
      E.BracketExpr (p, jse_to_exprjs e1, jse_to_exprjs e2)
    | J.Dot (p, e, nm) ->
      E.BracketExpr (p, jse_to_exprjs e, E.String (p, nm))
    | J.New (p, c, al) ->
      let map = Prelude.map in
      let argl = map (fun a -> jse_to_exprjs a) al in
      E.NewExpr (p, jse_to_exprjs c, argl)
    | J.Prefix (p, pop, r) -> E.PrefixExpr (p, pop, jse_to_exprjs r)
    | J.UnaryAssign (p, aop, r) -> E.PrefixExpr (p, aop, jse_to_exprjs r)
    | J.Infix (p, iop, l, r) ->
      E.InfixExpr (p, iop, jse_to_exprjs l, jse_to_exprjs r)
    | J.Cond (p, e1, e2, e3) ->  
      E.IfExpr (p, jse_to_exprjs e1, jse_to_exprjs e2, jse_to_exprjs e3)
    | J.Assign (p, aop, l, r) ->
      let el = jse_to_exprjs l
      and er = jse_to_exprjs r in
      let target = match el with
        | E.BracketExpr (p, ll, rr) -> ll
        | _ -> E.IdExpr (p, "%context")
      and left = match el with
        | E.BracketExpr (p, ll, rr) -> rr
        | _ -> el in
      begin match aop with
        | "=" -> E.AssignExpr (p, target, left, er)
        | _ -> let iop = String.sub aop 0 ((String.length aop) - 1) in
          E.AssignExpr (p, target, left,
            E.InfixExpr (p, iop, E.BracketExpr (p, target, left), er))
      end
    | J.List (p, el) -> let rec unroll = function
      | [] -> E.Undefined (p)
      | [f] -> jse_to_exprjs f
      | f :: rest -> E.SeqExpr (p, jse_to_exprjs f, unroll rest) in
    unroll el
    | J.Call (p, J.Id (_, "___unsafeLookupIdentifier"), [J.Lit (_, J.Str id)]) ->
      E.IdExpr (p, id)
    | J.Call (p, J.Id (_, "___takeS5Snapshot"), []) ->
      E.HintExpr (p, "___takeS5Snapshot", E.Null p)
    | J.Call (p, e, el) -> let xl = List.map jse_to_exprjs el in 
      E.AppExpr (p, jse_to_exprjs e, xl)

and block p b = jss_to_exprjs (J.Block (p, b))

and vdj_to_vde v p = match v with
  | J.VarDecl (id, e) -> match e with
    | None -> E.Undefined (p)
    | Some x -> let init_val = jse_to_exprjs x in
      let context = E.IdExpr (p, "%context") and fld_str = E.String (p, id) in
      E.AssignExpr (p, context, fld_str, init_val)

and jss_to_exprjs (s : J.stmt) : E.expr = 
  match s with
  | J.Block (p, sl) ->
    let rec unroll = function
      | [] -> E.Undefined (p)
      | [f] -> jss_to_exprjs f
      | f :: rest -> E.SeqExpr (p, jss_to_exprjs f, unroll rest) in
    unroll sl
  | J.Var (p, vdl) -> 
    let rec unroll vl = match vl with
      | [] -> E.Undefined (p)
      | [f] -> vdj_to_vde f p
      | f :: rest -> E.SeqExpr(p, vdj_to_vde f p, unroll rest) in
    unroll vdl
  | J.Empty (p) -> E.Undefined (p)
  | J.Expr (p, e) -> jse_to_exprjs e
  | J.If (p, e1, s2, s3) -> let alt = match s3 with
    | None -> E.Undefined (p)
    | Some s -> jss_to_exprjs s in
    E.IfExpr (p, jse_to_exprjs e1, jss_to_exprjs s2, alt)
  | J.DoWhile (p, b, t) ->
    let body = jss_to_exprjs b in
    let test = jse_to_exprjs t in
    E.LabelledExpr (p, "%before",
      E.WhileExpr (p,
        E.LabelledExpr (p, "%%dowhile", test),
        body))
  | J.While (p, t, b) ->
    let desugared = jss_to_exprjs b in
    E.LabelledExpr (p, "%before",
      E.WhileExpr (p, jse_to_exprjs t, desugared))
  | J.ForInVar (p, vd, exp, bdy) ->
    let nm = match vd with J.VarDecl (nm, _) -> nm in
    E.LabelledExpr (p, "%before",
      E.ForInExpr (p, nm, jse_to_exprjs exp, jss_to_exprjs bdy))
  | J.ForIn (p, e1, e2, bdy) ->
    let nm = match e1 with J.Id (_, i) -> i | _ -> failwith "what" in
    E.LabelledExpr (p, "%before",
      E.ForInExpr (p, nm, jse_to_exprjs e2, jss_to_exprjs bdy))
  | J.ForVar (p, vdl, e2, e3, bdy) ->
    let rec unroll = function
      | [] -> E.Undefined (p)
      | [f] -> vdj_to_vde f p
      | f :: rest -> E.SeqExpr (p, vdj_to_vde f p, unroll rest) in
    let rec init3 a = match a with
      | None -> E.Undefined (p)
      | Some a -> jse_to_exprjs a
    and init2 b = match b with
      | None -> E.True (p)
      | Some b -> jse_to_exprjs b in
    let inner_let = 
      E.LetExpr (p, "%%after", init3 e3, jss_to_exprjs bdy) in
    E.SeqExpr (p, unroll vdl,
      E.LabelledExpr (p, "%before",
        E.WhileExpr (p, init2 e2, inner_let)))
  | J.For (p, e1, e2, e3, body) -> 
    let rec init1 a = match a with
      | None -> E.Undefined (p)
      | Some a -> jse_to_exprjs a
    and init2 b = match b with
      | None -> E.True (p)
      | Some b -> jse_to_exprjs b in
    let inner_let = 
      E.LetExpr (p, "%%after", init1 e3, jss_to_exprjs body) in
    E.SeqExpr (p, init1 e1,
      E.LabelledExpr (p, "%before",
        E.WhileExpr (p, init2 e2, inner_let)))
  | J.Labeled (p, id, s) -> E.LabelledExpr (p, id, jss_to_exprjs s)
  | J.Continue (p, id) -> let lbl = match id with
    | None -> "%continue" | Some s -> s in
    E.BreakExpr (p, lbl, E.Undefined (p))
  | J.Break (p, id) ->
    let lbl = match id with None -> "%before" | Some s -> s in
    E.BreakExpr (p, lbl, E.Undefined (p))
  | J.Return (p, e) -> let rval = match e with
    | None -> E.Undefined (p)
    | Some x -> jse_to_exprjs x in
    E.BreakExpr (p, "%ret", rval)
  | J.Try (p, body, catch, finally) -> 
    begin match catch, finally with
      | None, None -> failwith "Should not happen!  No catch AND no finally"
      | None, Some finally -> 
        E.TryFinallyExpr (p, block p body, block p finally)
      | Some (param, blck), None ->
        E.TryCatchExpr (p, block p body, param, block p blck)
      | Some (param, catch), Some finally ->
        E.TryFinallyExpr (p, 
                          E.TryCatchExpr (p, block p body, param, block p catch),
                          block p finally)
    end 
  | J.Throw (p, e) -> E.ThrowExpr (p, jse_to_exprjs e)
  | J.Switch (p, disc, cl) ->
    let case = function 
      | J.Case (p, e, s) -> E.Case (p, jse_to_exprjs e, jss_to_exprjs s)
      | J.Default (p, s) -> E.Default (p, jss_to_exprjs s) in
    let map = Prelude.map in
    E.SwitchExpr (p, jse_to_exprjs disc, map case cl)
  | J.With (p, obj, body) -> E.WithExpr (p, jse_to_exprjs obj, jss_to_exprjs body)
  | J.Debugger _ -> failwith "Debugger statements not implemented"

and srcElts p (ss : J.srcElt list) (context : E.expr) : E.expr =
  let se_to_e se = match se with
    | J.Stmt (s) -> jss_to_exprjs s
    | J.FuncDecl (nm, args, body) ->
      strict_wrapper p body (E.FuncStmtExpr (p, nm, args, create_context p body context)) in
  let reordered = J.reorder_sel ss in
  match reordered with
    | [] -> E.Undefined (p)
    | [first] -> se_to_e first
    | first :: rest -> E.SeqExpr (p, se_to_e first, srcElts p rest context) 

and create_context p (ss : J.srcElt list) (parent : E.expr) : E.expr = 
  let rec fvl_to_letchain fvl final = match fvl with
    | [] -> final
    | first :: rest -> let newnm = "%%" ^ first in
      E.LetExpr (p, newnm, E.Undefined (p), fvl_to_letchain rest final) in
  let free_vars = IdSet.elements (J.fv_sel ss) in
  let reordered = J.reorder_sel ss in
  let last = srcElts p reordered parent in
  fvl_to_letchain free_vars last

and strict_wrapper p body func =
    if J.is_strict_mode body
    then E.StrictExpr (p, func)
    else func

let js_to_exprjs p ss parent =
  let wrapper expr =
    if J.is_strict_mode ss
    then E.StrictExpr (p, expr)
    else E.NonstrictExpr (p, expr) in
  (J.used_vars_sel ss, wrapper (create_context p ss parent))

