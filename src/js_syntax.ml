(** ES5 abstract syntax, based on the grammar for the concrete syntax in the
    ES5 spec. Unlike the grammar, which specifies multiple kinds of expressions
    and statements to disambigous concrete inputs, the AST collapes these. *)

type pos = Prelude.pos

type id = string

type infixOp = string
type assignOp = string
type unaryAssignOp = string
type prefixOp = string

type lit =
  | Null
  | Bool of bool
  | Num of float
  | Str of string
           
type propName =
  | PropId of string
  | PropStr of string
  | PropNum of float

type mem =
  | Field of propName * expr
  | Get of propName * srcElt list
  | Set of propName * id * srcElt list

and expr =
  | This of pos
  | Id of pos * id
  | Lit of pos * lit
  | Array of pos * expr list
  | Object of pos * mem list
  | Paren of pos * expr list
  | Func of pos * id option * id list * srcElt list
  | Bracket of pos * expr * expr
  | Dot of pos * expr * id
  | New of pos * expr * expr list
  | Prefix of pos * prefixOp  * expr
  | UnaryAssign of pos * unaryAssignOp * expr
  | Infix of pos * infixOp * expr * expr
  | Cond of pos * expr * expr * expr
  | Assign of pos * assignOp * expr * expr
  | List of pos * expr list
  | Call of pos * expr * expr list

and case =
  | Case of pos * expr * stmt
  | Default of pos * stmt
          
and varDecl =
  | VarDecl of id * expr option
          
and stmt =
  | Block of pos * block
  | Var of pos * varDecl list
  | Empty of pos
  | Expr of pos * expr
  | If of pos * expr * stmt * stmt option
  | DoWhile of pos * stmt * expr
  | While of pos * expr * stmt
  | For of pos * expr option * expr option * expr option * stmt
  | ForVar of pos * varDecl list * expr option * expr option * stmt
  | ForIn of pos * expr * expr * stmt
  | ForInVar of pos * varDecl * expr * stmt
  | Labeled of pos * id * stmt
  | Continue of pos * id option
  | Break of pos * id option
  | Return of pos * expr option
  | With of pos * expr * stmt
  | Switch of pos * expr * case list
  | Throw of pos * expr
  | Try of pos * block * catch * finally
  | Debugger of pos

and block = stmt list

and catch = (id * block) option

and finally = block option

and srcElt =
  | Stmt of stmt
  | FuncDecl of id * id list * srcElt list

type program = srcElt list
