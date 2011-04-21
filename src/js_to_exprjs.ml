module E = Exprjs_syntax
module J = Js_syntax

open Prelude
open Js_print

let rec jse_to_exprjs (e : J.expr) : E.expr =
  match e with
    | J.This (p) -> E.ThisExpr (p)
    | J.Id (p, i) -> E.IdExpr(p, i)
    | J.Lit (p, l) -> 
      let result = match l with 
        | J.Null -> E.Null (p)
        | J.Bool (b) -> if b then E.True (p) else E.False (p)
        | J.Num (n) -> E.Num (p, n)
        | J.Str (s) -> E.String (p, s) in result
    | J.Array (p, el) -> E.ArrayExpr (p, List.map jse_to_exprjs el)
    | J.Object (p, mem_lst) ->
      let rec prop_to_str prop = match prop with
        (J.PropId s | J.PropStr s) -> s
        | J.PropNum n -> string_of_float n
      and m_to_pr m = match m with
        | J.Field (name, e) -> 
          (p, prop_to_str name, E.Data (jse_to_exprjs e))
        | J.Get (name, body) -> let ns = prop_to_str name in
          (p, ns, E.Getter (ns, E.FuncExpr (p, [], srcElts body)))
        | J.Set (name, arg, body) -> let ns = prop_to_str name in
          (p, ns, E.Setter (ns, E.FuncExpr (p, [arg], srcElts body))) in
      E.ObjectExpr(p, List.map m_to_pr mem_lst)
    | J.Func (p, nm, args, body) -> E.FuncExpr (p, args, srcElts body)
    | J.Bracket (p, e1, e2) -> 
      E.BracketExpr (p, jse_to_exprjs e1, jse_to_exprjs e2)
    | J.Dot (p, e, nm) ->
      E.BracketExpr (p, jse_to_exprjs e, E.String (p, nm))
    | _ -> failwith "unimplemented expression type"

and lst_to_seqexpr (l : 'a list) (f : ('a -> E.expr)) (p : J.pos) : E.expr = 
  match l with
  | [] -> E.Undefined (p)
  | [first] -> f first
  | first :: rest -> E.SeqExpr (p, f first, lst_to_seqexpr rest f p)

and jss_to_exprjs (s : J.stmt) : E.expr = 
  match s with
  | J.Block (p, bl) -> lst_to_seqexpr bl jss_to_exprjs p
  | J.Var (p, vdl) -> 
    let rec vdj_to_vde v = match v with
      | J.VarDecl (id, e) -> match e with
        | None -> E.VarDeclExpr (p, id, E.Undefined (p))
        | Some x -> E.VarDeclExpr (p, id, jse_to_exprjs x)
    and unroll vl = match vl with
      | [] -> E.Undefined (p)
      | [f] -> vdj_to_vde f
      | f :: rest -> E.SeqExpr(p, vdj_to_vde f, unroll rest) in
    unroll vdl
  | J.Expr (p, e) -> jse_to_exprjs e (* ExpressionStatement *)
  | J.Labeled (p, id, s) -> E.LabelledExpr (p, id, jss_to_exprjs s)
  | J.Continue (p, id) -> let lbl = match id with
    | None -> "loopstart" | Some s -> s in
    E.BreakExpr (p, lbl, E.Undefined (p))
  | J.Break (p, id) -> let lbl = match id with
    | None -> "loopend" | Some s -> s in 
    E.BreakExpr (p, lbl, E.Undefined (p))
  | J.Return (p, e) -> let rval = match e with
    | None -> E.Undefined (p)
    | Some x -> jse_to_exprjs x in
    E.BreakExpr (p, "ret", rval)
  | J.For (p, e1, e2, e3, body) -> 
    let rec init1 a = match a with 
      | None -> E.Undefined (p)
      | Some a -> jse_to_exprjs a
    and init2 b = match b with
      | None -> E.True (p)
      | Some b -> jse_to_exprjs b in
    let innerwhile = 
      E.WhileExpr (p, init2 e2, 
        E.SeqExpr (p, E.LabelledExpr (p, "loopstart", jss_to_exprjs body), 
        init1 e3)) in
    E.SeqExpr (p, init1 e1,
      E.SeqExpr (p, innerwhile,
        E.LabelledExpr (p, "loopend", E.Undefined (p))))
  | _ -> failwith "unimplemented statement type"

and srcElts (ss : J.srcElt list) : E.expr =
  let rec p = dummy_pos
  and se_to_e se = match se with
    | J.Stmt (s) -> jss_to_exprjs s
    | J.FuncDecl (nm, args, body) ->
      E.FuncStmtExpr (p, nm, args, srcElts body) in
  match ss with
    | [] -> E.Undefined (p)
    | [first] -> se_to_e first
    | first :: rest -> E.SeqExpr (p, se_to_e first, srcElts rest)
