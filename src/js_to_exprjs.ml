module E = Exprjs_syntax
module J = Js_syntax

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
    | J.Bracket (p, e1, e2) -> 
      E.BracketExpr (p, jse_to_exprjs e1, jse_to_exprjs e2)
    | _ -> failwith "unimplemented expression type"

and jss_to_exprjs (s : J.stmt) : E.expr = 
  match s with
  | J.Block (p, bl) -> 
    let rec unroll sl = match sl with
      | [] -> E.Undefined (p)
      | [f] -> jss_to_exprjs f
      | f :: rest -> E.SeqExpr (p, jss_to_exprjs f, unroll rest) in
    unroll bl
  | J.For (p, e1, e2, e3, body) -> 
    let rec init1 a = match a with 
      | None -> E.Undefined p 
      | Some a -> jse_to_exprjs a
    and init2 b = match b with
      | None -> E.True p
      | Some b -> jse_to_exprjs b in
    E.SeqExpr(p, init1 e1,
      E.WhileExpr(p, init2 e2, 
        E.SeqExpr(p, jss_to_exprjs body, init1 e3)))
  | _ -> failwith "unimplemented statement type"

and srcElts (ss : J.srcElt list) : E.expr = failwith "nyi"
