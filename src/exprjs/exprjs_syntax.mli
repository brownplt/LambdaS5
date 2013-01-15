(** A simplified syntax for JavaScript. The primary simplification is
    that statements are eliminated. Expr{_ JS} is an expression-based syntax.

    We map JavaScript's statements to Expr{_ JS}'s control operators. Some
    statements map trivially to Expr{_ JS}. Others, such as switch and return,
    require less-obvious transformations. See the implementation for details.

    Expr{_ JS} has let-bindings [LetExpr]. We use let-bindings for some
    transformations. However, we do not transform [VarDeclStmt]s into
    let-bindings at this stage. Therefore, Expr{_ JS} uses both lexical scope
    and scope objects. *)
open Prelude

type expr = 
  | True of Pos.t
  | False of Pos.t
  | Num of Pos.t * float
  | Undefined of Pos.t
  | Null of Pos.t
  | String of Pos.t * string
  | ArrayExpr of Pos.t * expr list
  | ObjectExpr of Pos.t * (Pos.t * string * prop) list
      (** Object properties are transformed into string literals *)
  | ThisExpr of Pos.t
  | IdExpr of Pos.t * id (** let-bound identifiers *)
  | JSIdExpr of Pos.t * id (** identifiers from JS source *)
  | BracketExpr of Pos.t * expr * expr
  | NewExpr of Pos.t * expr * expr list
  | PrefixExpr of Pos.t * id * expr
  | InfixExpr of Pos.t * id * expr * expr
  | IfExpr of Pos.t * expr * expr * expr
  | ObjAssignExpr of Pos.t * expr * expr * expr
  | AssignExpr of Pos.t * id * expr
  | JSAssignExpr of Pos.t * id * expr
  | AppExpr of Pos.t * expr * expr list
  | FuncExpr of Pos.t * id list * expr
  | LetExpr of Pos.t * id * expr * expr 
      (** We need let-expressions to simplify statements. *)
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
      (** We leave function statements in place, so that they can be lifted
          for JavaScript to turned into letrecs for Typed JavaScript. *)
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

val pos_of_expr : expr -> Pos.t

  (*
   *
val from_javascript : JavaScript_syntax.prog -> expr

val from_javascript_expr : JavaScript_syntax.expr -> expr

(** locally defined functions. *)
val locals : expr -> IdSet.t
*)
