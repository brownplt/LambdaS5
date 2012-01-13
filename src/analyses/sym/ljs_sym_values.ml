open Prelude
open Ljs_syntax

type JSType = 
  | TNull
  | TUndef
  | TString
  | TBool
  | TNum
  | TObj
  | TFun of int (* arity *)
  | TAny

type value =
  | Null
  | Undefined
  | Num of float
  | String of string
  | True
  | False
      (* A VarCell can contain an ObjCell, but not vice versa.  This
      mimics the semantics of heap-like object refs alongside mutable
      variables *)
  | VarCell of value ref 
      (* Objects shouldn't have VarCells in them, but can have any of
      the other kinds of values *)
  | ObjCell of (attrsv * (propv IdMap.t)) ref
  | Closure of (value list -> path -> int -> (result list * exresult list))
  | Sym of sym_exp (* symbolic expression *)
and 
  sym_exp =
  | Concrete of value 
  | SId of id
  | SOp1 of string * sym_exp
  | SOp2 of string * sym_exp * sym_exp
  | SApp of sym_exp * sym_exp list
and result = value * path
and exval = 
  | Break of label * value
  | Throw of value
and label = string
and exresult = exval * path


and path = { constraints : sym_exp list;
             vars : var list; }

and var = id * string

and
  attrsv = { code : value option;
             proto : value;
             extensible : bool;
             klass : string;
             primval : value option; }
and
  propv = 
  | Data of datav * bool * bool
  | Accessor of accessorv * bool * bool
and datav = { value : value; writable : bool; }
and accessorv = { getter : value; setter : value; }

let d_attrsv = { primval = None;
                 code = None; 
                 proto = Undefined; 
                 extensible = false; 
                 klass = "LambdaJS internal"; }

type env = value IdMap.t


let mtPath = { constraints = []; vars = []; }
