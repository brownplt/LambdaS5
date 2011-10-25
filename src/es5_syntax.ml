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
  | Config -> "#configurable"
  | Writable -> "#writable"
  | Enum -> "#enumerable"

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
  | Rec of pos * id * exp * exp (** value bound must be an [ELambda] *)
  | Label of pos * id * exp
  | Break of pos * id * exp
  | TryCatch of pos * exp * exp
      (** Catch block must be an [ELambda] *)
  | TryFinally of pos * exp * exp
  | Throw of pos * exp
  | Lambda of pos * id list * exp
  | Eval of pos * exp
  | Hint of pos * string * exp
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
  | GetField (pos, _, _, _) -> pos 
  | SetField (pos, _, _, _, _) -> pos 
  | DeleteField (pos, _, _) -> pos
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
