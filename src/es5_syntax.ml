open Prelude

type attr =
  | Value
  | Getter
  | Setter
  | Config
  | Writable
  | Enum

let string_of_attr attr = match attr with
  | Value -> "#value"
  | Getter -> "#getter"
  | Setter -> "#setter"
  | Config -> "#config"
  | Writable -> "#writable"
  | Enum -> "#enum"

(* Borrowed from prelude *)
module AttrOrderedType = struct
  type t = attr
  let compare = Pervasives.compare
end

module AttrMap = Map.Make (AttrOrderedType)

type op1 = 
  | Op1Prefix of id
  | Prim1 of string

type op2 = 
  | Op2Infix of id
  | Prim2 of string

type op3 =
  | Op3Prefix of id
  | Prim3 of string

type exp =
  | EConst of pos * JavaScript_syntax.const
  | EId of pos * id
  | EObject of pos * (string * exp) list *
      (string * (attr * exp) list) list
      (** object, field, new value, args object *)
  | EUpdateFieldSurface of pos * exp * exp * exp * exp
      (** object, field, args object *)
  | EGetFieldSurface of pos * exp * exp * exp
  | EAttr of pos * attr * exp * exp
  | ESetAttr of pos * attr * exp * exp * exp
  | EUpdateField of pos * exp * exp * exp * exp * exp
  | EGetField of pos * exp * exp * exp * exp
  | EDeleteField of pos * exp * exp
  | ESet of pos * id * exp
  | EOp1 of pos * op1 * exp
  | EOp2 of pos * op2 * exp * exp
  | EOp3 of pos * op3 * exp * exp * exp
  | EIf of pos * exp * exp * exp
  | EApp of pos * exp * exp list
  | ESeq of pos * exp * exp
  | ELet of pos * id * exp * exp
  | EFix of pos * id * exp
  | ELabel of pos * id * exp
  | EBreak of pos * id * exp
  | ETryCatch of pos * exp * exp
      (** Catch block must be an [ELambda] *)
  | ETryFinally of pos * exp * exp
  | EThrow of pos * exp
  | ELambda of pos * id list * exp

(******************************************************************************)

let rename (x : id) (y : id) (exp : exp) : exp = 
  let rec ren exp = match exp with
    | EConst _ -> exp
    | EId (p, z) -> EId (p, if z = x then y else z)
    | EObject (p, attrs, fields) -> 
	let ren_attr (name, value) = (name, ren value) in
	let ren_field (name, attrs) = (name, map ren_attr attrs) in
	  EObject (p, map ren_attr attrs, map ren_field fields)
    | EUpdateFieldSurface (p, o, e1, e2, args) ->
	EUpdateFieldSurface (p, ren o, ren e1, ren e2, ren args)
    | EUpdateField (p, o1, o2, e1, e2, args) -> 
	EUpdateField (p, ren o1, ren o2, ren e1, ren e2, ren args)
    | EGetFieldSurface (p, o, e, args) ->
	EGetFieldSurface (p, ren o, ren e, ren args)
    | EGetField (p, o1, o2, e, args) ->
	EGetField (p, ren o1, ren o2, ren e, ren args)
    | EDeleteField (p, o, e) ->
	EDeleteField (p, ren o, ren e)
    | EAttr (p, a, o, f) ->
	EAttr (p, a, ren o, ren f)
    | ESetAttr (p, a, o, f, v) ->
	ESetAttr (p, a, ren o, ren f, ren v)
    | EOp1 (p, o, e) -> EOp1 (p, o, ren e)
    | EOp2 (p, o, e1, e2) -> EOp2 (p, o, ren e1, ren e2)
    | EOp3 (p, o, e1, e2, e3) -> EOp3 (p, o, ren e1, ren e2, ren e3)
    | EIf (p, e1, e2, e3) -> EIf (p, ren e1, ren e2, ren e3)
    | EApp (p, f, args) -> EApp (p, ren f, map ren args)
    | ESeq (p, e1, e2) -> ESeq (p, ren e1, ren e2)
    | ESet (p, z, e) -> 
	if x = z then ESet (p, y, ren e) else ESet (p, z, ren e)
    | ELet (p, z, e1, e2) -> 
        ELet (p, z, ren e1, if x = z then e2 else ren e2)
    | EFix (p, z, body) ->
        if z = x then exp
        else EFix (p, z, ren body)
    | ELabel (p, l, e) -> ELabel (p, l, ren e)
    | EBreak (p, l, e) -> EBreak (p, l, ren e)
    | ETryCatch (p, e1, e2) -> ETryCatch (p, ren e1, ren e2)
    | ETryFinally (p, e1, e2) -> ETryFinally (p, ren e1, ren e2)
    | EThrow (p, e) -> EThrow (p, ren e)
    | ELambda (p, args, body) ->
        if List.mem x args then exp
        else ELambda (p, args, ren body)
  in ren exp


let rec fv (exp : exp) : IdSet.t = match exp with
  | EConst _ -> IdSet.empty
  | EId (_, x) -> IdSet.singleton x
  | EObject (_, attrs, fields) -> 
      let attr (name, value) = fv value in
      let field (name, attrs) = 
	IdSetExt.unions (map attr attrs) in
	IdSetExt.unions (List.append (map attr attrs) (map field fields))
  | EUpdateField (_, o1, o2, e1, e2, args) -> 
      IdSetExt.unions (map fv [o1; o2; e1; e2; args])
  | EGetField (_, o1, o2, e, args) ->
      IdSetExt.unions (map fv [o1; o2; e; args])
  | EUpdateFieldSurface (_, o, e1, e2, args) -> 
      IdSetExt.unions (map fv [o; e1; e2; args])
  | EGetFieldSurface (_, o, e, args) ->
      IdSetExt.unions (map fv [o; e; args])
  | EDeleteField (_, o, e) -> IdSet.union (fv o) (fv e)
  | EAttr (_, _, o, f) ->
      IdSetExt.unions (map fv [o; f])
  | ESetAttr (_, _, o, f, v) ->
      IdSetExt.unions (map fv [o; f; v])
  | EOp1 (_, _, e) -> fv e
  | EOp2 (_, _, e1, e2) -> IdSet.union (fv e1) (fv e2)
  | EOp3 (_, _, e1, e2, e3) -> IdSetExt.unions (map fv [e1; e2; e3])
  | EIf (_, e1, e2, e3) -> IdSetExt.unions (map fv [e1; e2; e3])
  | EApp (_, f, args) -> IdSetExt.unions (map fv (f :: args))
  | ESeq (_, e1, e2) -> IdSet.union (fv e1) (fv e2)
  | ESet (_, x, e) -> IdSet.union (fv e) (IdSet.singleton x)
  | ELet (_, x, e1, e2) -> IdSet.union (fv e1) (IdSet.remove x (fv e2))
  | EFix (_, x, body) ->
      IdSet.union (fv body) (IdSet.remove x (fv body))
  | ELabel (_, _, e) -> fv e
  | EBreak (_, _, e) -> fv e
  | ETryCatch (_, e1, e2) -> IdSet.union (fv e1) (fv e2)
  | ETryFinally (_, e1, e2) -> IdSet.union (fv e1) (fv e2)
  | EThrow (_, e) ->  fv e
  | ELambda (_, args, body) -> IdSet.diff (fv body) (IdSetExt.from_list args)
