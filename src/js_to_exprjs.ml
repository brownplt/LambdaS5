module E = Exprjs_syntax
module J = Js_syntax

open Prelude
open Js_print

exception ParseError

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
        | J.Regexp (s) -> E.RegExpr (p, s)
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
          (p, name, E.Getter (name, srcElts sel parent))
        | J.Set (nm, argnm, sel) ->
          let name = prop_to_str nm and parent = E.IdExpr (p, "%context") in
          let let_body = srcElts sel parent in
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
      let last = srcElts body parent in
      let funcbody = match nm with
        | Some s ->
          E.LetExpr (p, "%%" ^ s, E.Undefined (p),
            E.SeqExpr (p, 
              E.AssignExpr (p, 
                E.IdExpr (p, "%context"), 
                E.String (p, s), 
                E.FuncExpr (p, args, last)), 
              last))
        | None -> last in
      E.FuncExpr (p, args, fvl_to_letchain free_vars funcbody)
    | J.Bracket (p, e1, e2) -> 
      E.BracketExpr (p, jse_to_exprjs e1, jse_to_exprjs e2)
    | J.Dot (p, e, nm) ->
      E.BracketExpr (p, jse_to_exprjs e, E.String (p, nm))
    | J.New (p, c, al) -> let argl = map (fun a -> jse_to_exprjs a) al in
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
      let e_asgn = match aop with
        | "=" -> E.AssignExpr (p, target, left, er)
        | "*=" -> 
          E.AssignExpr (p, target, left, 
            E.InfixExpr (p, "*", E.BracketExpr (p, target, left), er))
        | "/=" -> 
          E.AssignExpr (p, target, left, 
            E.InfixExpr (p, "/", E.BracketExpr (p, target, left), er))
        | "%=" -> 
          E.AssignExpr (p, target, left, 
            E.InfixExpr (p, "%", E.BracketExpr (p, target, left), er))
        | "+=" ->
          E.AssignExpr (p, target, left, 
            E.InfixExpr (p, "+", E.BracketExpr (p, target, left), er))
        | "-=" -> 
          E.AssignExpr (p, target, left, 
            E.InfixExpr (p, "-", E.BracketExpr (p, target, left), er))
        | _ -> failwith "unimplemented assign op" in
      e_asgn
    | J.List (p, el) -> let rec unroll = function
      | [] -> E.Undefined (p)
      | [f] -> jse_to_exprjs f
      | f :: rest -> E.SeqExpr (p, jse_to_exprjs f, unroll rest) in
    unroll el
  | J.Call (p, e, el) -> let xl = List.map jse_to_exprjs el in 
    E.AppExpr (p, jse_to_exprjs e, xl)

and block p b = jss_to_exprjs (J.Block (p, b))

and vdj_to_vde v p = match v with
  | J.VarDecl (id, e) -> let init_val = match e with
    | None -> E.Undefined (p)
    | Some x -> jse_to_exprjs x in
    let context = E.IdExpr (p, "%context") and fld_str = E.String (p, id) in
    E.AssignExpr (p, context, fld_str, init_val)
  | _ -> failwith ("vdj_to_vde didn't get a J.VarDecl")

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
    let rec body = jss_to_exprjs b
    and we = E.WhileExpr (p, jse_to_exprjs t, body) in
    E.SeqExpr (p, body, we)
  | J.While (p, t, b) ->
    let rec context = E.IdExpr (p, "%context")
    and desugared = jss_to_exprjs b in
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
    E.SwitchExpr (p, jse_to_exprjs disc, map case cl)
  | J.With _ -> raise ParseError
  | J.Debugger _ -> failwith "Debugger statements not implemented"

and srcElts (ss : J.srcElt list) (context : E.expr) : E.expr =
  let p = dummy_pos in
  let se_to_e se = match se with
    | J.Stmt (s) -> jss_to_exprjs s
    | J.FuncDecl (nm, args, body) ->
      E.FuncStmtExpr (p, nm, args, create_context body context) in
  let reordered = J.reorder_sel ss in
  match reordered with
    | [] -> E.Undefined (p)
    | [first] -> se_to_e first
    | first :: rest -> E.SeqExpr (p, se_to_e first, srcElts rest context) 

and create_context (ss : J.srcElt list) (parent : E.expr) : E.expr = 
  let p = dummy_pos in
  let rec fvl_to_letchain fvl final = match fvl with
    | [] -> final
    | first :: rest -> let newnm = "%%" ^ first in
      E.LetExpr (p, newnm, E.Undefined (p), fvl_to_letchain rest final) in
  let free_vars = IdSet.elements (J.fv_sel ss) in
  let reordered = J.reorder_sel ss in
  let last = srcElts reordered parent in
  fvl_to_letchain free_vars last

let js_to_exprjs = create_context
