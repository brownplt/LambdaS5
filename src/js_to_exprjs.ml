module E = Exprjs_syntax
module J = Js_syntax

let rec jss_to_exprjs (s : J.stmt) : E.expr = 
        match s with
        | J.For (p, e1, e2, e3, body) -> 
            let init e = match e with None -> E.Undefined p 
                                    | Some e -> jse_to_exprjs e in
          E.SeqExpr (p, init e1, E.WhileExpr(p, jse_to_exprjs e2,
          E.SeqExpr(p, jss_to_exprjs body, jse_to_exprjs e3)
        | _ -> failwith "no statements yet"

let rec jse_to_exprjs (e : J.expr) : E.expr =
        match e with
        | J.This (p) -> E.Id (p, "this")
        |
        | _ -> failwith "no expressions yet"
