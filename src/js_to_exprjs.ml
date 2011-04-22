module E = Exprjs_syntax
module J = Js_syntax

open Prelude
open Js_print

(*
 *and expr =
  | This of pos
  | Id of pos * id
  | Lit of pos * lit
  | Array of pos * expr list
  | Object of pos * mem list
  | Paren of pos * expr list
  | Func of pos * id option * id list * srcElt list
  | Bracket of pos * expr * expr
  | Dot of pos * expr * id
  | New of pos * expr * expr list
  | Prefix of pos * prefixOp  * expr
  | UnaryAssign of pos * unaryAssignOp * expr
  | Infix of pos * infixOp * expr * expr
  | Cond of pos * expr * expr * expr
  | Assign of pos * assignOp * expr * expr
  | List of pos * expr list
  | Call of pos * expr * expr list
  *)

let rec jse_to_exprjs (e : J.expr) (context : E.expr) : E.expr =
  match e with
    | J.This (p) -> E.ThisExpr (p)
    | J.Id (p, i) -> (*E.IdExpr(p, i)*)
      E.BracketExpr(p, E.IdExpr (p, "%context"), E.String (p, i))
    | J.Lit (p, l) -> 
      let result = match l with 
        | J.Null -> E.Null (p)
        | J.Bool (b) -> if b then E.True (p) else E.False (p)
        | J.Num (n) -> E.Num (p, n)
        | J.Str (s) -> E.String (p, s) in result
    | J.Array (p, el) -> 
      E.ArrayExpr (p, List.map (fun x -> jse_to_exprjs x context) el)
    | J.Object (p, mem_lst) ->
      let rec prop_to_str prop = match prop with
        (J.PropId s | J.PropStr s) -> s
        | J.PropNum n -> string_of_float n
      and m_to_pr m = match m with
        | J.Field (name, e) -> 
          (p, prop_to_str name, E.Data (jse_to_exprjs e context))
        | J.Get (name, body) -> let ns = prop_to_str name in
          (p, ns, E.Getter (ns, E.FuncExpr (p, [], srcElts body context)))
        | J.Set (name, arg, body) -> let ns = prop_to_str name in
          (p, ns, E.Setter (ns, E.FuncExpr (p, [arg], srcElts body context))) in
      E.ObjectExpr(p, List.map m_to_pr mem_lst)
    | J.Func (p, nm, args, body) -> E.FuncExpr (p, args, srcElts body context)
    | J.Bracket (p, e1, e2) -> 
      E.BracketExpr (p, jse_to_exprjs e1 context, jse_to_exprjs e2 context)
    | J.Dot (p, e, nm) ->
      E.BracketExpr (p, jse_to_exprjs e context, E.String (p, nm))
    | J.Assign (p, aop, l, r) -> 
      let el = jse_to_exprjs l context
      and er = jse_to_exprjs r context in
      let target = match el with
        | E.BracketExpr (p, ll, rr) -> ll
        | _ -> E.IdExpr (p, "%context")
      and property = match el with
        | E.BracketExpr (p, ll, rr) -> rr
        | _ -> el in
      let e_asgn = match aop with
        | "=" -> E.AssignExpr (p, target, property, er)
        | _ -> failwith "only assign op implemented is =" in
      e_asgn
    | J.Call (p, e, el) -> let xl = List.map (fun x -> jse_to_exprjs x context) el in 
      E.AppExpr (p, jse_to_exprjs e context, xl)
    | e -> failwith "unimplemented expression type"

and jss_to_exprjs (s : J.stmt) (context : E.expr) : E.expr = 
  match s with
  | J.Block (p, sl) ->
    let rec unroll = function
      | [] -> E.Undefined (p)
      | [f] -> jss_to_exprjs f context
      | f :: rest -> E.SeqExpr (p, jss_to_exprjs f context, unroll rest) in
    unroll sl
  | J.Var (p, vdl) -> 
    let rec vdj_to_vde v = match v with
      | J.VarDecl (id, e) -> match e with
        | None -> E.AssignExpr (p, E.IdExpr (p, "%context"), E.String (p, id), E.Undefined (p)) 
        | Some x -> let r = jse_to_exprjs x context in 
          E.AssignExpr (p, E.IdExpr (p, "%context"), E.String (p, id), r)
    and unroll vl = match vl with
      | [] -> E.Undefined (p)
      | [f] -> vdj_to_vde f
      | f :: rest -> E.SeqExpr(p, vdj_to_vde f, unroll rest) in
    unroll vdl
  | J.Expr (p, e) -> jse_to_exprjs e context
  | J.Labeled (p, id, s) -> E.LabelledExpr (p, id, jss_to_exprjs s context)
  | J.Continue (p, id) -> let lbl = match id with
    | None -> "loopstart" | Some s -> s in
    E.BreakExpr (p, lbl, E.Undefined (p))
  | J.Break (p, id) -> let lbl = match id with
    | None -> "loopend" | Some s -> s in 
    E.BreakExpr (p, lbl, E.Undefined (p))
  | J.Return (p, e) -> let rval = match e with
    | None -> E.Undefined (p)
    | Some x -> jse_to_exprjs x context in
    E.BreakExpr (p, "%ret", rval)
  | J.For (p, e1, e2, e3, body) -> 
    let rec init1 a = match a with 
      | None -> E.Undefined (p)
      | Some a -> jse_to_exprjs a context
    and init2 b = match b with
      | None -> E.True (p)
      | Some b -> jse_to_exprjs b context in
    let innerwhile = 
      E.WhileExpr (p, init2 e2, 
        E.SeqExpr (p, E.LabelledExpr (p, "loopstart", jss_to_exprjs body context), 
        init1 e3)) in
    E.SeqExpr (p, init1 e1,
      E.SeqExpr (p, innerwhile,
        E.LabelledExpr (p, "loopend", E.Undefined (p))))
  | _ -> failwith "unimplemented statement type"

and srcElts (ss : J.srcElt list) (parent : E.expr) : E.expr =
  let rec p = dummy_pos
  and parent_prop = (p, "parent", E.Data(parent))
  and context = E.ObjectExpr (p, [parent_prop])
  and srcElts (ss : J.srcElt list) (parent : E.expr) : E.expr =
    let se_to_e se = match se with
      | J.Stmt (s) -> jss_to_exprjs s context
      | J.FuncDecl (nm, args, body) ->
        E.FuncStmtExpr (p, nm, args, srcElts body context) in
     match ss with
      | [] -> E.Undefined (p)
      | [first] -> se_to_e first
      | first :: rest -> E.SeqExpr (p, se_to_e first, srcElts rest parent) in
  E.LetExpr (p, "%context", context, srcElts ss parent)

