module E = Exprjs_syntax
module J = Js_syntax

let rec js_to_exprjs (e : J.expr) : E.expr =
        match e with
        | J.This (p) -> E.Id (p, "this")
        | _ -> failwith "no expressions yet"
