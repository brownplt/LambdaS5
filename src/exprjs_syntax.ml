open Prelude

type expr = 
  | True of pos
  | False of pos
  | Num of pos * float
  | Undefined of pos
  | Null of pos
  | String of pos * string
  | ArrayExpr of pos * expr list
  | ObjectExpr of pos * (pos * string * prop) list
  | BracketExpr of pos * expr * expr
  | AssignExpr of pos * expr * expr * expr
  | Id of pos * ident
  | NewExpr of pos * expr * expr list
  | AppExpr of pos * expr * expr list
  | PrefixExpr of pos * id * expr
  | InfixExpr of pos * id * expr * expr
  | IfExpr of pos * expr * expr * expr
  | FuncExpr of pos * id list * expr
  | FuncStmtExpr of pos * id * id list * expr
  | LetExpr of pos * id * expr * expr
  | RecExpr of pos * id * expr * expr
  | SeqExpr of pos * expr * expr
  | WhileExpr of pos * expr * expr
  | LabelledExpr of pos * id * expr
  | BreakExpr of pos * id * expr
  | ForInExpr of pos * id * expr * expr
  | VarDeclExpr of pos * id * expr
  | TryCatchExpr of pos * expr * id * expr
  | TryFinallyExpr of pos * expr * expr
  | ThrowExpr of pos * expr
and prop =
  | Data of expr
  | Accessor of expr option * expr option
(******************************************************************************)

module S = JavaScript_syntax

let rec expr (e : S.expr) = match e with
  | _ -> failwith "No JS -> exprjs defined yet"

    
