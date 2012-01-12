(** ES5 abstract syntax, based on the grammar for the concrete syntax in the
    ES5 spec. Unlike the grammar, which specifies multiple kinds of expressions
    and statements to disambigous concrete inputs, the AST collapes these. *)

open Prelude

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
  | Regexp of string
           
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

let rec fv (s : stmt) : Prelude.IdSet.t = 
  let mf vd = match vd with VarDecl (nm, _) -> IdSet.singleton nm
  and c_to_fv c = match c with
    | Case (_, _, ss) -> fv ss
    | Default (_, ss) -> fv ss in
  match s with
  | Continue _
  | Break _
  | Throw _
  | Debugger _
  | Expr _
  | Return _ -> IdSet.empty
  | Block (_, b) -> IdSetExt.unions (map fv b)
  | Var (_, vdl) ->
    IdSetExt.unions (map mf vdl)
  | Empty _ -> IdSet.empty
  | If (_, _, s1, s2) -> let init2 ss = match ss with
    | None -> IdSet.empty
    | Some x -> fv x in
    IdSetExt.unions [fv s1; init2 s2]
  | DoWhile (_, bdy, _) -> fv bdy
  | While (_, _, bdy) -> fv bdy
  | For (_, _, _, _, bdy) -> fv bdy
  | ForVar (_, vdl, _, _, bdy) -> IdSetExt.unions ((fv bdy) :: (map mf vdl))
  | ForIn (_, _, _, bdy) -> fv bdy
  | ForInVar (_, vd, _, bdy) -> IdSet.union (mf vd) (fv bdy)
  | Labeled (_, _, ss) -> fv ss
  | With (_, _, bdy) -> fv bdy
  | Switch (_, _, cl) -> IdSetExt.unions (map c_to_fv cl)
  | Try (_, b, c, f) -> 
    let init_b = IdSetExt.unions (map fv b)
    and init_c = let result = match c with
      | None -> IdSet.empty
      | Some (nm, bl) -> IdSetExt.unions (map fv bl) in result
    and init_f = let result = match f with
      | None -> IdSet.empty
      | Some x -> IdSetExt.unions (map fv x) in result in
    IdSetExt.unions [init_b; init_c; init_f]


(* All identifiers that don't appear in var declarations, so that we can assign
 * to the global object if necessary *)
let rec used_vars_sel (sel : srcElt list) : Prelude.IdSet.t =
  let rec used_vars_expr e = match e with
    | This _ -> IdSet.empty
    | Id (_, nm) -> IdSet.singleton nm
    | Lit _ -> IdSet.empty
    | Array (_, el) -> IdSetExt.unions (map used_vars_expr el)
    | Object (_, ml) ->
      let mem_var m = match m with
        | Field (_, me) -> used_vars_expr me
        | Get (_, sel) | Set (_, _, sel) -> used_vars_sel sel in
      IdSetExt.unions (map mem_var ml)
    | Paren (_, el) -> IdSetExt.unions (map used_vars_expr el)
    | Func (_, _, _, sel) -> used_vars_sel sel
    | Bracket (_, e1, e2) -> IdSet.union (used_vars_expr e1) (used_vars_expr e2)
    | Dot (_, e1, _) -> used_vars_expr e1
    | New (_, ex, el) -> 
      IdSet.union (used_vars_expr ex) (IdSetExt.unions (map used_vars_expr el))
    | Prefix (_, _, e1) -> used_vars_expr e1
    | UnaryAssign (_, _, e1) -> used_vars_expr e1
    | Infix (_, _, e1, e2) -> IdSet.union (used_vars_expr e1) (used_vars_expr e2)
    | Cond (_, e1, e2, e3) -> IdSetExt.unions (map used_vars_expr [e1; e2; e3])
    | Assign (_, _, e1, e2) -> IdSet.union (used_vars_expr e1) (used_vars_expr e2)
    | List (_, el) -> IdSetExt.unions (map used_vars_expr el)
    | Call (_, e1, el) ->
      IdSet.union (used_vars_expr e1) (IdSetExt.unions (map used_vars_expr el)) in

  let rec used_vars_stmt s = 
    let evars ex = match ex with 
      | None -> IdSet.empty 
      | Some (exp) -> used_vars_expr exp
    and svars st = match st with
      | None -> IdSet.empty
      | Some (stm) -> used_vars_stmt stm in
    match s with
    | Block (_, sl) -> IdSetExt.unions (map used_vars_stmt sl)
    (* setters/getters for declared vars handled elsewhere *)
    | Var _ -> IdSet.empty 
    | Empty _ -> IdSet.empty
    | Expr (_, e) -> used_vars_expr e
    | If (_, tst, cns, alt) -> 
      let alt_vars = svars alt in
      IdSetExt.unions [used_vars_expr tst; used_vars_stmt cns; alt_vars]
    | DoWhile (_, s, e) | While (_, e, s) -> 
      IdSet.union (used_vars_stmt s) (used_vars_expr e)
    | For (_, e1, e2, e3, bdy) ->
      let found_vars = IdSetExt.unions (map evars [e1; e2; e3]) in
      IdSet.union found_vars (used_vars_stmt bdy)
    | ForVar (_, _, e1, e2, bdy) ->
      let found_vars = IdSetExt.unions (map evars [e1; e2]) in
      IdSet.union found_vars (used_vars_stmt bdy)
    | ForIn (_, e1, e2, bdy) ->
      let found_vars = IdSetExt.unions (map used_vars_expr [e1; e2]) in
      IdSet.union found_vars (used_vars_stmt bdy)
    | ForInVar (_, _, e, bdy) ->
      IdSet.union (used_vars_expr e) (used_vars_stmt bdy)
    | Labeled (_, _, bdy) -> used_vars_stmt bdy
    | Continue _ | Break _ -> IdSet.empty
    | Return (_, e) -> evars e
    | With _ -> IdSet.empty
    | Switch (_, e, cl) ->
      let case_vars c = match c with
        | Case (_, e, st) -> IdSet.union (used_vars_expr e) (used_vars_stmt st)
        | Default (_, st) -> used_vars_stmt st in
      IdSet.union (used_vars_expr e) (IdSetExt.unions (map case_vars cl))
    | Throw (_, e) -> used_vars_expr e
    | Try (_, sl, c, f) ->
      let catch_vars c = match c with 
        | None -> IdSet.empty 
        | Some ((_, sl)) -> IdSetExt.unions (map used_vars_stmt sl) in
      let fin_vars f = match f with
        | None -> IdSet.empty
        | Some sl -> IdSetExt.unions (map used_vars_stmt sl) in
      IdSetExt.unions [IdSetExt.unions (map used_vars_stmt sl); 
                                        catch_vars c; 
                                        fin_vars f]
    | Debugger _ -> IdSet.empty in

  let used_vars_se se = match se with
    | Stmt s -> used_vars_stmt s
    | FuncDecl (nm, args, bdy) -> 
      IdSet.union (IdSet.singleton nm) (used_vars_sel bdy) in

  match sel with
    | [] -> IdSet.empty
    | se :: rest -> IdSet.union (used_vars_se se) (used_vars_sel rest)

(* Free vars in a program, without descending into nested functions *)
let rec fv_sel (sel : srcElt list) : Prelude.IdSet.t = 
  match sel with
  | [] -> IdSet.empty
  | first :: rest -> let fv_f = match first with
    | Stmt s -> fv s
    | FuncDecl _ -> IdSet.empty in
    IdSet.union fv_f (fv_sel rest)

and getfd_lst sel = match sel with
  | [] -> []
  | (Stmt _) :: rest -> getfd_lst rest
  | fd :: rest -> fd :: getfd_lst rest

and removefd_lst sel = match sel with
  | [] -> []
  | (FuncDecl _) :: rest -> removefd_lst rest
  | s :: rest -> s :: removefd_lst rest

and reorder_sel sel = List.append (getfd_lst sel) (removefd_lst sel)
