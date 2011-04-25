open Prelude

module E = Exprjs_syntax
module S = Es5_syntax

(*type expr = 
  | True of pos
  | False of pos
  | Num of pos * float
  | Undefined of pos
  | Null of pos
  | String of pos * string
  | ArrayExpr of pos * expr list
  | ObjectExpr of pos * (pos * string * prop) list
  | ThisExpr of pos
  | VarExpr of pos * id
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
  | VarDeclExpr of pos * id * expr
  | TryCatchExpr of pos * expr * id * expr
  | TryFinallyExpr of pos * expr * expr
  | ThrowExpr of pos * expr
  | FuncStmtExpr of pos * id * id list * expr
  | HintExpr of pos * string * expr
and prop =
  | Data of expr
  | Getter of id * expr
  | Setter of id * expr
  *)

let rec exprjs_to_ljs (e : E.expr) : S.exp = match e with
  | E.True (p) -> S.True (p)
  | E.False (p) -> S.False (p)
  | E.Num (p, n) -> S.Num (p, n)
  | E.Undefined (p) -> S.Undefined (p)
  | E.Null (p) -> S.Null (p)
  | E.String (p, s) -> S.String (p, s)
  | E.IdExpr (p, nm) -> S.Id (p, nm)
  | E.BracketExpr (p, l, r) -> 
    let o = exprjs_to_ljs l
    and f = exprjs_to_ljs r in
    let normal = S.GetField (p, o, f, S.Null (p))
    and lookup = s_lookup f in
    let result = match l with
      | E.IdExpr (p, nm) -> if nm <> "%context" then normal else lookup
      | _ -> normal in
    result
  | E.InfixExpr (p, op, l, r) -> S.Op2 (p, op, exprjs_to_ljs l, exprjs_to_ljs r)
  | E.ObjectExpr (p, pl) ->
    let rec ejsprop_to_sprop pr = match pr with
      | E.Data (e) -> 
          let rec v = exprjs_to_ljs e
          and d = { S.value = v; S.writable = true; } in
          S.Data (d, true, true)
      | E.Getter (nm, e) -> failwith "getters unimplemented"
      | E.Setter (nm, e) -> failwith "setters unimplemented"
    and tuple_to_prop t = match t with
      (p, s, pr) -> (s, ejsprop_to_sprop pr)
    and form_props props = match props with
      | [] -> []
      | first :: rest -> (tuple_to_prop first) :: form_props rest in
    S.Object (p, S.d_attrs, form_props pl)
  | E.AssignExpr (p, obj, pr, vl) -> 
    let sobj = exprjs_to_ljs obj
    and spr = exprjs_to_ljs pr
    and svl = exprjs_to_ljs vl in
    S.SetField (p, sobj, spr, svl, S.Null (p)) (* TODO: Args object is null for now *)
  | E.SeqExpr (p, e1, e2) -> S.Seq (p, exprjs_to_ljs e1, exprjs_to_ljs e2)
  (* TODO: There's a comment in exprjs_syntax re: FuncStmtExpr.  Not sure
   * what it means. *)
  | E.AppExpr (p, e, el) -> let sl = List.map (fun x -> exprjs_to_ljs x) el in
    let parent_arg = S.Id (p, "%context") in
    S.App (p, exprjs_to_ljs e, parent_arg :: sl)
  | E.FuncExpr (p, args, body) -> get_lambda p args body
  | E.FuncStmtExpr (p, nm, args, body) -> 
    let inner_lambda = get_lambda p args body in
    S.SetField (p, S.Id (p, "%context"), S.String (p, nm), inner_lambda, S.Null (p))
  | E.LetExpr (p, nm, vl, body) -> 
    let sv = exprjs_to_ljs vl
    and sb = exprjs_to_ljs body in
    S.Let (p, nm, sv, sb)
  | E.BreakExpr (p, id, e) ->
    S.Break (p, id, exprjs_to_ljs e)
  | _ -> failwith "unimplemented exprjs type"

and get_lambda p args body = 
  let arg_to_prop arg = 
      (arg, S.Data ({ S.value = S.Id (p, arg); S.writable = true; }, true, true)) in
    let rec ncontext_aprops = List.map (fun arg -> arg_to_prop arg) args
    and parent_prop = 
      ("%parent", S.Data ({ S.value = S.Id (p, "%parent"); S.writable = false; }, true, true))
    and ncontext_props = parent_prop :: ncontext_aprops
    and ncontext = S.Object (p, S.d_attrs, ncontext_props) in
    let rec inner_body = exprjs_to_ljs body
    and inner_let = S.Let (p, "%context", ncontext, inner_body)
    and inner_lbl = S.Label (p, "%ret", inner_let) in
    S.Lambda (p, "%parent" :: args, inner_lbl)

and s_lookup prop =
  let p = dummy_pos in
    S.Rec (p, "lookup",
    S.Lambda (p, ["k"; "obj";], 
      S.If (p, 
        S.Op2 (p, "stx=", S.Id (p, "obj"), S.Undefined (p)),
        S.Undefined (p),
        S.Let (p, "f", 
          S.GetField (p, S.Id (p, "obj"), S.Id (p, "k"), S.Null (p)),
          S.If (p, S.Op2 (p, "stx=", S.Id (p, "f"), S.Undefined (p)),
            S.App (p, S.Id (p, "lookup"), 
              [S.Id (p, "k"); 
              S.GetField (p, S.Id (p, "obj"), S.String(p, "%parent"), S.Null (p));]),
            S.Id (p, "f"))))),
    S.App (p, S.Id (p, "lookup"), [prop; S.Id (p, "%context");]))
