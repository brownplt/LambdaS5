open Prelude
open Ljs_syntax



type jsType = 
  | TNull
  | TUndef
  | TString
  | TBool
  | TNum
  | TObj
  | TFun of int (* arity *)
  | TAny

type typeEnv = jsType IdMap.t
exception TypeError of string

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
  sym_exp = (* a-normal form: nested sym_exp are only SId or Concrete *)
  | Concrete of value 
  | SId of id
  | SLet of id * sym_exp
  | SIsTrue of sym_exp
  | SIsFalse of sym_exp
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
             vars : typeEnv ; }

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


let mtPath = { constraints = []; vars = IdMap.empty; }

let add_var id ty p = 
  let { constraints = cs ; vars = vs } = p in
  { constraints = cs ; vars = IdMap.add id ty vs }

let ty_to_string t = match t with
  | TNull -> "TNull"
  | TUndef -> "TUndef"
  | TString -> "TString"
  | TBool -> "TBool"
  | TNum -> "TNum"
  | TObj -> "TObj"
  | TFun arity -> "TFun(" ^ (string_of_int arity) ^ ")"
  | TAny -> "TAny"


let check_type id t p =
  let { constraints = cs ; vars = vs } = p in
  try 
    let found = IdMap.find id vs in
    if found = TAny || found = t then () (* simple subtyping from Any down to whatever *)
    else begin 
      Printf.printf "Known type of %s is %s, wanted %s\n" id (ty_to_string found) (ty_to_string t);
      raise (TypeError id)
    end
  with Not_found -> failwith ("[interp] unknown symbolic var" ^ id)

let add_constraint c p =
  let { constraints = cs ; vars = vs } = p in
  { constraints = c :: cs; vars = vs }

     
