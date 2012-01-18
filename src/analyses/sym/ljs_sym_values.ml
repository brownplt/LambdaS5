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
  | TData
  | TAccessor

type typeEnv = jsType IdMap.t
exception TypeError of string


type value =
  | Null
  | Undefined
  | Num of float
  | String of string
  | True
  | False
  | VarCell of value ref 
  | ObjCell of (attrsv * (propv IdMap.t)) ref
  | Closure of (value list -> ctx -> int -> (result list * exresult list))
  | Sym of id (* symbolic value *)
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
   
and exval = 
  | Break of label * value
  | Throw of value
and label = string

and result = value * ctx
and exresult = exval * ctx
and ctx = { constraints : sym_exp list;
            vars : typeEnv ; }

(* language of constraints *)
and sym_exp =
  | Concrete of value 
  | SId of id
  | SOp1 of string * sym_exp
  | SOp2 of string * sym_exp * sym_exp
  | SApp of sym_exp * sym_exp list
  | SLet of id * sym_exp
  | SCastJS of jsType * sym_exp
  | SUncastJS of jsType * sym_exp
  | SAssert of sym_exp
  | SAnd of sym_exp list
  | SOr of sym_exp list
  | SNot of sym_exp
  | SImplies of sym_exp * sym_exp
  | SIsMissing of sym_exp
  | SGetField of id * id


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
  | TData -> "TData"
  | TAccessor -> "TAccessor"


let check_type id t p =
  let { constraints = cs ; vars = vs } = p in
  try 
    let found = IdMap.find id vs in
    if found = t then p
    else if found = TAny then
      { constraints = cs ; vars = IdMap.add id t vs }
    else begin 
      Printf.printf "Known type of %s is %s, wanted %s\n" id (ty_to_string found) (ty_to_string t);
      raise (TypeError id)
    end
  with Not_found -> failwith ("[interp] unknown symbolic var" ^ id)

let add_constraint c p =
  let { constraints = cs ; vars = vs } = p in
  { constraints = c :: cs; vars = vs }

     
let add_constraints cs p = 
  let { constraints = cs'; vars = vs } = p in
  { constraints = List.rev_append cs cs'; vars = vs }