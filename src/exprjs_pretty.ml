open Prelude
open Exprjs_syntax

open Format
open FormatExt

let rec exp e = match e with
  | True (_) -> text "true"
  | False (_) -> text "false"
  | Num (_, n) -> text (string_of_float n)
  | Undefined (_) -> text "undefined"
  | Null (_) -> text "null"
  | String (_, s) -> text ("\"" ^ s ^ "\"")
  | ArrayExpr (_, el) -> parens (horz (map exp el))
  | ObjectExpr (_, pl) -> braces (horz (map prop pl))
  | ThisExpr (_) -> text "this"
  | IdExpr (_, nm) -> text nm
  | BracketExpr (_, e1, e2) ->  
    squish [exp e1; 
      (brackets (horz [exp e2;]))];
  | NewExpr (_, e1, el) -> text "new " (*TODO: finish*)
  | PrefixExpr (_, op, ex) -> horz [text op; exp ex;]
  | InfixExpr (_, op, l, r) -> horz [exp l; text op; exp r]
  | IfExpr (_, tst, thn, els) -> parens (vert 
      [text "if"; exp tst; exp thn; exp els])
  | AssignExpr (_, o, pr, vl) -> 
    parens (horz [text "assign"; exp o; exp pr; exp vl;])
  | AppExpr (_, f, args) ->
    let al = map exp args in
    parens (horz [text "app"; exp f; horz al;])
  | FuncExpr (_, prms, bdy) -> let pl = map text prms in
    parens (horz [text "fun"; horz pl; exp bdy;])
  | LetExpr (_, nm, vl, rst) ->
    parens (vert [text "let"; text nm; exp vl; exp rst;])
  | SeqExpr (_, e1, e2) ->
    parens (vert [text "seq"; exp e1; exp e2;])
  | WhileExpr (_, tst, bdy) -> 
    parens (vert [horz [text "while"; exp tst;]; exp bdy])
  | LabelledExpr (_, lbl, expr) ->
    parens (horz [text "lbl"; text lbl; exp expr;])
  | BreakExpr (_, lbl, expr) -> 
    parens (horz [text "brk"; text lbl; exp expr;])
  | ForInExpr (_, nm, vl, bdy) ->
    parens (vert [horz [text "forin"; text nm; exp vl]; exp bdy])
  | TryCatchExpr (_, b1, nm, b2) ->
    parens (vert [text "tryc"; exp b1; text nm; exp b2;])
  | TryFinallyExpr (_, b1, b2) ->
    parens (vert [text "tryf"; exp b1; exp b2;])
  | ThrowExpr (_, expr) -> parens (horz [text "throw"; exp expr;])
  | FuncStmtExpr (_, nm, args, bdy) -> let al = map text args in
    parens (vert [text "fstmt"; text nm; horz al; exp bdy;])
  | HintExpr (_, nm, expr) -> parens (horz [text "hint"; text nm; exp expr;])

and prop p = match p with
| (_, nm, Data (expr)) -> brackets (horz [text nm; text "="; exp expr;])
| (_, nm, Getter (s, expr)) -> brackets (horz [text "get"; text nm; text "="; exp expr;])
| (_, nm, Setter (s, expr)) -> brackets (horz [text "set"; text nm; text "="; exp expr;])
