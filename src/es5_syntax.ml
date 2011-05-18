open Prelude

type pattr =
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

type exp =
  | Null of pos
  | Undefined of pos
  | String of pos * string
  | Num of pos * float
  | True of pos
  | False of pos
  | Id of pos * id
  | Object of pos * attrs * (string * prop) list
      (* GetAttr (pos, property, object, field name) *)
  | GetAttr of pos * pattr * exp * exp
      (* SetAttr (pos, property, object, field name, new value) *)
  | SetAttr of pos * pattr * exp * exp * exp
  | GetField of pos * exp * exp * exp (*pos, left, right, args object *)
  | SetField of pos * exp * exp * exp * exp (* pos, obj, field, new val, args *)
  | DeleteField of pos * exp * exp (* pos, obj, field *)
  | SetBang of pos * id * exp
  | Op1 of pos * string * exp
  | Op2 of pos * string * exp * exp
  | If of pos * exp * exp * exp
  | App of pos * exp * exp list
  | Seq of pos * exp * exp
  | Let of pos * id * exp * exp
  | Rec of pos * id * exp * exp
  | Label of pos * id * exp
  | Break of pos * id * exp
  | TryCatch of pos * exp * exp
      (** Catch block must be an [ELambda] *)
  | TryFinally of pos * exp * exp
  | Throw of pos * exp
  | Lambda of pos * id list * exp
  | Eval of pos * exp
and data =       
    {value : exp;
     writable : bool; }
and accessor =       
    {getter : exp;
     setter : exp; }
and prop =
  | Data of data * bool * bool
  | Accessor of accessor * bool * bool
and attrs =
    { primval : exp option;
      code : exp option;
      proto : exp option;
      klass : string;
      extensible : bool; }

(* Some useful defaults for these things, to avoid typing too much *)
let d_attrs = 
  { primval = None;
    code = None;
    proto = Some (Null dummy_pos);
    klass = "Object";
    extensible = true; }

let d_data =
  { value = Undefined dummy_pos;
    writable = true; }

let d_accessor = 
  { getter = Undefined dummy_pos;
    setter = Undefined dummy_pos; }

(******************************************************************************)

let rename (x : id) (y : id) (exp : exp) : exp = 
  let rec ren exp = 
    let ren_opt o = match o with Some exp -> Some (ren exp) | None -> None in
    let rec ren_attrs 
        { primval = vexp; code = cexp; proto = pexp; klass = str; extensible = b; } =
      { primval = vexp; code = ren_opt cexp; proto = ren_opt pexp; klass = str; extensible = b; }
    in
    let rec ren_attr (a : prop) = match a with
      | Data ({ value=exp; writable=b }, c, e) -> 
        Data ({ value=ren exp; writable=b }, c, e) 
      | Accessor ({ getter=gexp; setter=sexp}, c, e) ->
        Accessor ({ getter=ren gexp; setter=ren sexp }, c, e) in
    match exp with
      | Null _
      | Undefined _
      | Num _
      | True _
      | False _
      | String _ -> exp
      | Id (p, z) -> Id (p, if z = x then y else z)
      | Object (p, attrs, fields) -> 
	let ren_field (name, attr) = (name, ren_attr attr) in
	Object (p, ren_attrs attrs, map ren_field fields)
      | SetField (p, o, e1, e2, args) ->
        SetField (p, ren o, ren e1, ren e2, ren args)
      | GetField (p, o, e, args) ->
        GetField (p, ren o, ren e, ren args)
      | DeleteField (p, o, e) ->
        DeleteField (p, ren o, ren e)
      | GetAttr (p, a, o, f) ->
        GetAttr (p, a, ren o, ren f)
      | SetAttr (p, a, o, f, v) ->
        SetAttr (p, a, ren o, ren f, ren v)
      | Op1 (p, o, e) -> Op1 (p, o, ren e)
      | Op2 (p, o, e1, e2) -> Op2 (p, o, ren e1, ren e2)
      | If (p, e1, e2, e3) -> If (p, ren e1, ren e2, ren e3)
      | App (p, f, args) -> App (p, ren f, map ren args)
      | Seq (p, e1, e2) -> Seq (p, ren e1, ren e2)
      | SetBang (p, z, e) -> 
	if x = z then SetBang (p, y, ren e) else SetBang (p, z, ren e)
      | Let (p, z, e1, e2) -> 
        Let (p, z, ren e1, if x = z then e2 else ren e2)
      | Rec (p, z, bind, body) ->
        let bind' = ren bind in
        Rec (p, z, bind', if x = x then body else ren body)
      | Label (p, l, e) -> Label (p, l, ren e)
      | Break (p, l, e) -> Break (p, l, ren e)
      | TryCatch (p, e1, e2) -> TryCatch (p, ren e1, ren e2)
      | TryFinally (p, e1, e2) -> TryFinally (p, ren e1, ren e2)
      | Throw (p, e) -> Throw (p, ren e)
      | Lambda (p, args, body) ->
        if List.mem x args then exp
        else Lambda (p, args, ren body)
  in ren exp
  
let rec fv (exp : exp) : IdSet.t = match exp with
  | Null _
  | Undefined _
  | Num _
  | True _
  | False _
  | String _ -> IdSet.empty
  | Id (_, x) -> IdSet.singleton x
  | Object (_, attrs, fields) -> 
    let fv_opt o = match o with Some e -> fv e | None -> IdSet.empty in
    let fv_attrs { proto=pexp; code=cexp; } =
      IdSet.union (fv_opt pexp) (fv_opt cexp) in
    let field (name, prop) = match prop with
      | Data ({ value=vexp; }, _, _) -> fv vexp
      | Accessor ({ getter=gexp; setter=sexp; }, _, _) -> 
        IdSet.union (fv gexp) (fv sexp) in
    IdSetExt.unions (List.append [fv_attrs attrs] (map field fields))
  | SetField (_, o1, e1, e2, args) -> 
    IdSetExt.unions (map fv [o1; e1; e2; args])
      (*
      let toadd = match o1 with
        | Id (_, "%context") ->
          let i = match e1 with
            | String (_, s) -> IdSet.singleton s
            | _ -> IdSet.empty in i
        | _ -> IdSet.empty in
      IdSetExt.unions (toadd :: (map fv [o1; e1; e2; args]))
      *)
  | GetField (_, o1, e, args) ->
      IdSetExt.unions (map fv [o1; e; args])
  | DeleteField (_, o, e) -> IdSet.union (fv o) (fv e)
  | GetAttr (_, _, o, f) ->
      IdSetExt.unions (map fv [o; f])
  | SetAttr (_, _, o, f, v) ->
      IdSetExt.unions (map fv [o; f; v])
  | Op1 (_, _, e) -> fv e
  | Op2 (_, _, e1, e2) -> IdSet.union (fv e1) (fv e2)
  | If (_, e1, e2, e3) -> IdSetExt.unions (map fv [e1; e2; e3])
  | App (_, f, args) -> IdSetExt.unions (map fv (f :: args))
  | Seq (_, e1, e2) -> IdSet.union (fv e1) (fv e2)
  | SetBang (_, x, e) -> IdSet.union (fv e) (IdSet.singleton x)
  | Let (_, x, e1, e2) -> IdSet.union (fv e1) (IdSet.remove x (fv e2))
  | Rec (_, x, bind, body) ->
      IdSet.union (fv bind) (IdSet.remove x (fv body))
  | Label (_, _, e) -> fv e
  | Break (_, _, e) -> fv e
  | TryCatch (_, e1, e2) -> IdSet.union (fv e1) (fv e2)
  | TryFinally (_, e1, e2) -> IdSet.union (fv e1) (fv e2)
  | Throw (_, e) ->  fv e
  | Lambda (_, args, body) -> IdSet.diff (fv body) (IdSetExt.from_list args)
