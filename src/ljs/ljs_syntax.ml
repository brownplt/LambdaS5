open Prelude

type oattr = 
  | Proto
  | Klass
  | Extensible
  | Primval
  | Code

let string_of_oattr oattr = match oattr with
  | Proto -> "#proto"
  | Klass -> "#class"
  | Extensible -> "#extensible"
  | Primval -> "#primval"
  | Code -> "#code"

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
  | Config -> "#configurable"
  | Writable -> "#writable"
  | Enum -> "#enumerable"

type exp =
  | Null of Pos.t
  | Undefined of Pos.t
  | String of Pos.t * string
  | Num of Pos.t * float
  | True of Pos.t
  | False of Pos.t
  | Id of Pos.t * id
  | Object of Pos.t * attrs * (string * prop) list
      (* GetAttr (Pos.t, property, object, field name) *)
  | GetAttr of Pos.t * pattr * exp * exp
      (* SetAttr (Pos.t, property, object, field name, new value) *)
  | SetAttr of Pos.t * pattr * exp * exp * exp
  | GetObjAttr of Pos.t * oattr * exp
  | SetObjAttr of Pos.t * oattr * exp * exp
  | GetField of Pos.t * exp * exp * exp (*Pos.t, left, right, args object *)
  | SetField of Pos.t * exp * exp * exp * exp (* Pos.t, obj, field, new val, args *)
  | DeleteField of Pos.t * exp * exp (* Pos.t, obj, field *)
  | OwnFieldNames of Pos.t * exp
  | SetBang of Pos.t * id * exp
  | Op1 of Pos.t * string * exp
  | Op2 of Pos.t * string * exp * exp
  | If of Pos.t * exp * exp * exp
  | App of Pos.t * exp * exp list
  | Seq of Pos.t * exp * exp
  | Let of Pos.t * id * exp * exp
  | Rec of Pos.t * id * exp * exp (** value bound must be an [ELambda] *)
  | Label of Pos.t * id * exp
  | Break of Pos.t * id * exp
  | TryCatch of Pos.t * exp * exp
      (** Catch block must be an [ELambda] *)
  | TryFinally of Pos.t * exp * exp
  | Throw of Pos.t * exp
  | Lambda of Pos.t * id list * exp
  | Eval of Pos.t * exp
  | Hint of Pos.t * string * exp
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
    proto = Some (Null Pos.dummy);
    klass = "Object";
    extensible = true; }

let d_data =
  { value = Undefined Pos.dummy;
    writable = true; }

let d_accessor = 
  { getter = Undefined Pos.dummy;
    setter = Undefined Pos.dummy; }

let pos_of exp = match exp with
  | Null pos -> pos
  | Undefined pos -> pos
  | String (pos, _) -> pos
  | Num (pos, _) -> pos
  | True pos -> pos
  | False pos -> pos
  | Id (pos, _) -> pos
  | Object (pos, _, _) -> pos
  | GetAttr (pos, _, _, _) -> pos
  | SetAttr (pos, _, _, _, _) -> pos
  | GetObjAttr (pos, _, _) -> pos
  | SetObjAttr (pos, _, _, _) -> pos
  | GetField (pos, _, _, _) -> pos 
  | SetField (pos, _, _, _, _) -> pos 
  | DeleteField (pos, _, _) -> pos
  | OwnFieldNames (pos, _) -> pos
  | SetBang (pos, _, _) -> pos
  | Op1 (pos, _, _) -> pos
  | Op2 (pos, _, _, _) -> pos
  | If (pos, _, _, _) -> pos
  | App (pos, _, _) -> pos
  | Seq (pos, _, _) -> pos
  | Let (pos, _, _, _) -> pos
  | Rec (pos, _, _, _) -> pos
  | Label (pos, _, _) -> pos
  | Break (pos, _, _) -> pos
  | TryCatch (pos, _, _) -> pos
  | TryFinally (pos, _, _) -> pos
  | Throw (pos, _) -> pos
  | Lambda (pos, _, _) -> pos
  | Eval (pos, _) -> pos
  | Hint (pos, _, _) -> pos

