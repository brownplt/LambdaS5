module E = Exprjs_syntax
module J = Js_syntax

let rec jse_to_exprjs (e : J.expr) : E.expr =
        match e with
        | J.This (p) -> E.ThisExpr (p)
        | _ -> failwith "unimplemented expression type"

let rec jss_to_exprjs (s : J.stmt) : E.expr = 
        match s with
        | J.For (p, e1, e2, e3, body) -> 
          let rec init1 a = match a with 
            None -> E.Undefined p 
            | Some a -> jse_to_exprjs a
          and init2 b = match b with
            None -> E.True p
            | Some b -> jse_to_exprjs b in
          E.SeqExpr(p, init1 e1,
            E.WhileExpr(p, init2 e2, 
              E.SeqExpr(p, jss_to_exprjs body, init1 e3)))
        | _ -> failwith "unimplemented statement type"
