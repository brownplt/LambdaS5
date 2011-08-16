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

