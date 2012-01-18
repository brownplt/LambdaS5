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
  | VarCell of Store.loc (* can only point to a Value (see below) *)
  | ObjCell of Store.loc (* can only point to ObjLit (see below) *)
  | Closure of (value list -> ctx -> int -> (result list * exresult list))
  | Sym of id (* symbolic value *)
and cell = Value of value | ObjLit of (attrsv * (propv IdMap.t))
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
            vars : typeEnv ;
            store : (cell Store.t) }

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


let mtPath = { constraints = []; vars = IdMap.empty; store = Store.empty; }

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
  let { constraints = cs ; vars = vs; store = s; } = p in
  try 
    let found = IdMap.find id vs in
    if found = t then p
    else if found = TAny then
      { constraints = cs ; vars = IdMap.add id t vs ; store = s; }
    else begin 
      Printf.printf "Known type of %s is %s, wanted %s\n" id (ty_to_string found) (ty_to_string t);
      raise (TypeError id)
    end
  with Not_found -> failwith ("[interp] unknown symbolic var" ^ id)

let add_var id ty ctx = 
  { ctx with vars = IdMap.add id ty ctx.vars }
    
let add_constraint c ctx =
  { ctx with constraints = c :: ctx.constraints }
     
let add_constraints cs ctx =
  { ctx with constraints = List.rev_append cs ctx.constraints }

let sto_alloc v ctx = 
  let (loc, sto) = Store.alloc v ctx.store in
  (loc, { ctx with store = sto })

let sto_update loc v ctx = 
  { ctx with store = Store.update loc v ctx.store }

let sto_lookup loc ctx = Store.lookup loc ctx.store
