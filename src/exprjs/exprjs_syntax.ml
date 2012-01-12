open Prelude

type expr = 
  | True of pos
  | False of pos
  | Num of pos * float
  | Undefined of pos
  | Null of pos
  | String of pos * string
  | ArrayExpr of pos * expr list
  | RegExpr of pos * string
  | ObjectExpr of pos * (pos * string * prop) list
  | ThisExpr of pos
  | IdExpr of pos * id
  | BracketExpr of pos * expr * expr
  | NewExpr of pos * expr * expr list
  | PrefixExpr of pos * id * expr
  | InfixExpr of pos * id * expr * expr
  | IfExpr of pos * expr * expr * expr
  | AssignExpr of pos * expr * expr * expr
  | AppExpr of pos * expr * expr list
  | FuncExpr of pos * id list * expr
  | LetExpr of pos * id * expr * expr
  | SeqExpr of pos * expr * expr
  | WhileExpr of pos * expr * expr
  | LabelledExpr of pos * id * expr
  | BreakExpr of pos * id * expr
  | ForInExpr of pos * id * expr * expr
  | TryCatchExpr of pos * expr * id * expr
  | TryFinallyExpr of pos * expr * expr
  | ThrowExpr of pos * expr
  | SwitchExpr of pos * expr * case list
  | FuncStmtExpr of pos * id * id list * expr
  | HintExpr of pos * string * expr

and prop =
  | Data of expr
  | Getter of id * expr
  | Setter of id * expr

and case =
  | Case of pos * expr * expr
  | Default of pos * expr

let pos_of_expr expr = match expr with
  | True (pos) -> pos
  | False (pos) -> pos
  | Num (pos, _) -> pos
  | Undefined (pos) -> pos
  | Null (pos) -> pos
  | String (pos, _) -> pos
  | ArrayExpr (pos, _) -> pos
  | RegExpr (pos, _) -> pos
  | ObjectExpr (pos, _) -> pos
  | ThisExpr (pos) -> pos
  | IdExpr (pos, _) -> pos
  | BracketExpr (pos, _, _) -> pos
  | NewExpr (pos, _, _) -> pos
  | PrefixExpr (pos, _, _) -> pos
  | InfixExpr (pos, _, _, _) -> pos
  | IfExpr (pos, _, _, _) -> pos
  | AssignExpr (pos, _, _, _) -> pos
  | AppExpr (pos, _, _) -> pos
  | FuncExpr (pos, _, _) -> pos
  | LetExpr (pos, _, _, _) -> pos
  | SeqExpr (pos, _, _) -> pos
  | WhileExpr (pos, _, _) -> pos
  | LabelledExpr (pos, _, _) -> pos
  | BreakExpr (pos, _, _) -> pos
  | ForInExpr (pos, _, _, _) -> pos
  | TryCatchExpr (pos, _, _, _) -> pos
  | TryFinallyExpr (pos, _, _) -> pos
  | ThrowExpr (pos, _) -> pos
  | SwitchExpr (pos, _, _) -> pos
  | FuncStmtExpr (pos, _, _, _) -> pos
  | HintExpr (pos, _, _) -> pos
