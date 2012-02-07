open Js_syntax
open Format
open FormatExt
open Prelude

let rec pretty_lit = function
  | Null -> text "null"
  | Bool (b) -> text (string_of_bool b)
  | Num (n) -> text (string_of_float n)
  | Str (s) -> text s
  | Regexp (s) -> squish [text "/"; text s; text "/"]

and pretty_propname = function
  | PropId (s) -> text s
  | PropStr (s) -> text s
  | PropNum (n) -> text (string_of_float n)

and pretty_mem = function
  | Field (pn, e) -> parens (sep [text "Field"; pretty_propname pn; pretty_expr e])
  | Get (pn, sel) -> parens (sep [text "Getter"; pretty_propname pn; 
                                  braces (vert (map pretty_se sel))])
  | Set (pn, arg, sel) -> parens (sep [text "Getter"; pretty_propname pn; parens (text arg);
                                  braces (vert (map pretty_se sel))])

and pretty_se = function
  | Stmt s -> pretty_stmt s
  | FuncDecl (f, args, body) ->
    sep [text "function "; squish [text f; parens (inter (text ", ") (map text args))];
         braces (vert (map pretty_se body))]

and pretty_expr = function
  | This (p) -> text "this"
  | Id (p, id) -> text id
  | Lit (p, l) -> pretty_lit l
  | Array (p, el) -> parens (sep (text "Array" :: map pretty_expr el))
  | Object (p, ml) -> parens (vert (text "Object" :: map pretty_mem ml))
  | Paren (p, el) -> parens (sep (text "Paren" :: map pretty_expr el))
  | Func (p, nm, args, sel) ->
    let ns = match nm with
      | None -> "_"
      | Some s -> s in
    parens (sep [text "Func";
                 squish [text ns; parens (inter (text ", ") (map text args))];
                 braces (vert (map pretty_se sel))])
  | Bracket (p, e1, e2) -> parens (sep [text "Bracket"; pretty_expr e1; pretty_expr e2])
  | Dot (p, e, id) -> parens (sep [text "Dot"; pretty_expr e; text id])
  | New (p, e, el) -> sep [text "new"; 
                           squish [pretty_expr e; parens (inter (text ", ") (map pretty_expr el))]]
  | Call (_, f, args) -> squish [pretty_expr f; parens (inter (text ", ") (map pretty_expr args))]
  | List (_, es) -> brackets (sep (map pretty_expr es))
  | Assign (_, aOp, lhs, rhs) -> horz [pretty_expr lhs; text aOp; pretty_expr rhs]
  | Cond (_, test, trueBranch, falseBranch) -> parens (horz [pretty_expr test; text "?"; 
                                                             pretty_expr trueBranch; text ":";
                                                             pretty_expr falseBranch])
  | Infix (_, iOp, left, right) -> horz [pretty_expr left; text iOp; pretty_expr right]
  | UnaryAssign (_, op, e) -> squish [pretty_expr e; text op]
  | Prefix (_, op, e) -> squish [text op; pretty_expr e]

and pretty_vardecl = function
  | VarDecl (id, None) -> text id
  | VarDecl (id, Some e) -> horz [text id; text "="; pretty_expr e]

and pretty_expOpt = function
  | None -> text ""
  | Some e -> pretty_expr e

and pretty_case = function
  | Default (_, stmt) -> sep [text "default:"; pretty_stmt stmt]
  | Case (_, e, stmt) -> sep [text "case"; pretty_expr e; text ":"; pretty_stmt stmt]

and pretty_stmt = function
  | Block (_, block) -> braces (vert (map pretty_stmt block))
  | Var (_, vars) -> sep [text "var"; vert (map pretty_vardecl vars)]
  | Empty _ -> text ""
  | Expr (_, e) -> pretty_expr e
  | If (_, e, trueBranch, None) -> 
    sep [text "if"; parens (pretty_expr e); braces (pretty_stmt trueBranch)]
  | If (_, e, trueBranch, Some falseBranch) -> 
    sep [text "if"; parens (pretty_expr e); 
         braces (pretty_stmt trueBranch); 
         text "else"; braces (pretty_stmt falseBranch)]
  | DoWhile (_, body, cond) -> sep [text "do"; braces (pretty_stmt body); 
                                    text "while"; parens (pretty_expr cond)]
  | While (_, cond, body) -> sep [text "while"; parens (pretty_expr cond);
                                  braces (pretty_stmt body)]
  | For (_, init, test, incr, body) -> 
    sep [text "for"; parens (inter (text "; ") [pretty_expOpt init; 
                                                pretty_expOpt test; 
                                                pretty_expOpt incr]);
         braces (pretty_stmt body)]
  | ForVar (_, init, test, incr, body) -> 
    sep [text "for"; parens (inter (text "; ")
                               [horz [text "var"; vert (map pretty_vardecl init)];
                                pretty_expOpt test; 
                                pretty_expOpt incr]);
         braces (pretty_stmt body)]
  | ForIn (_, e, obj, body) ->
    sep [text "for"; parens (horz [pretty_expr e; text "in"; pretty_expr obj]);
         braces (pretty_stmt body)]
  | ForInVar (_, e, obj, body) ->
    sep [text "for"; parens (horz [text "var"; pretty_vardecl e; text "in"; pretty_expr obj]);
         braces (pretty_stmt body)]
  | Labeled (_, id, stmt) -> sep [text id; text ":"; braces (pretty_stmt stmt)]
  | Continue (_, None) -> text "continue"
  | Continue (_, Some id) -> horz [text "continue"; text id]
  | Break (_, None) -> text "break"
  | Break (_, Some id) -> horz [text "break"; text id]
  | Return (_, None) -> text "return"
  | Return (_, Some e) -> horz [text "return"; pretty_expr e]
  | With (_, expr, stmt) ->
    sep [text "with"; parens (pretty_expr expr); braces (pretty_stmt stmt)]
  | Switch (_, test, cases) ->
    sep [text "switch"; parens (pretty_expr test); braces (vert (map pretty_case cases))]
  | Throw (_, e) -> horz [text "throw"; pretty_expr e]
  | Try (p, block, catch, finally) ->
    let finallyFmt = 
      match finally with
      | None -> []
      | Some block -> [sep [text "finally"; pretty_stmt (Block (p, block))]] in
    let catchFmt =
      match catch with
      | None -> finallyFmt
      | Some (id, block) -> 
        (sep [text "catch"; parens (text id); pretty_stmt (Block (p, block))]) :: finallyFmt in
    sep (text "try" :: pretty_stmt (Block (p, block)) :: catchFmt)
  | Debugger _ -> text "debugger"


and pretty_program prog = vert (map pretty_se prog)
