open Prelude

type expr = 
  | True of Pos.t
  | False of Pos.t
  | Num of Pos.t * float
  | Undefined of Pos.t
  | Null of Pos.t
  | String of Pos.t * string
  | ArrayExpr of Pos.t * expr list
  | RegExpr of Pos.t * string
  | ObjectExpr of Pos.t * (Pos.t * string * prop) list
  | ThisExpr of Pos.t
  | IdExpr of Pos.t * id
  | BracketExpr of Pos.t * expr * expr
  | NewExpr of Pos.t * expr * expr list
  | PrefixExpr of Pos.t * id * expr
  | InfixExpr of Pos.t * id * expr * expr
  | IfExpr of Pos.t * expr * expr * expr
  | AssignExpr of Pos.t * expr * expr * expr
  | AppExpr of Pos.t * expr * expr list
  | FuncExpr of Pos.t * id list * expr
  | LetExpr of Pos.t * id * expr * expr
  | SeqExpr of Pos.t * expr * expr
  | WhileExpr of Pos.t * expr * expr
  | LabelledExpr of Pos.t * id * expr
  | BreakExpr of Pos.t * id * expr
  | ForInExpr of Pos.t * id * expr * expr
  | TryCatchExpr of Pos.t * expr * id * expr
  | TryFinallyExpr of Pos.t * expr * expr
  | ThrowExpr of Pos.t * expr
  | SwitchExpr of Pos.t * expr * case list
  | FuncStmtExpr of Pos.t * id * id list * expr
  | WithExpr of Pos.t * expr * expr
  | StrictExpr of Pos.t * expr
  | NonstrictExpr of Pos.t * expr
  | HintExpr of Pos.t * string * expr

and prop =
  | Data of expr
  | Getter of id * expr
  | Setter of id * expr

and case =
  | Case of Pos.t * expr * expr
  | Default of Pos.t * expr

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
  | WithExpr (pos, _, _) -> pos
  | StrictExpr (pos, _) -> pos
  | NonstrictExpr (pos, _) -> pos
  | HintExpr (pos, _, _) -> pos
