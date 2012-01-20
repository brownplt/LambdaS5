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

type typeEnv = (jsType * string) IdMap.t
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
            time : int ;
            store : (cell Store.t) }

(* language of constraints *)
and sym_exp =
  | Concrete of value 
  | STime of int
  | SLoc of Store.loc
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


let mtPath = { constraints = []; vars = IdMap.empty; store = Store.empty; time = 0 }

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

let add_var id ty hint ctx = 
  { ctx with vars = IdMap.add id (ty, hint) ctx.vars }

let has_var id ctx = 
  IdMap.mem id ctx.vars

let fresh_var = 
  let count = ref 0 in
  (fun prefix t hint pc ->
    incr count;
    let nvar = "%%" ^ prefix ^ (string_of_int !count) in
    (nvar, (add_var nvar t hint pc)))

let const_string f pc = 
  let str = "S_" ^ f in
  if has_var str pc then (str, pc)
  else (str, (add_var str TString f pc))

let add_const_str pc s =
  let (s_id, pc') = const_string s pc in
  (Sym s_id, pc')


let check_type id t p =
  let { constraints = cs ; vars = vs; store = s; time = time} = p in
  try 
    let (found, hint) = IdMap.find id vs in
    if t = TAny or found = t then p
    else if found = TAny then
      { constraints = cs ; vars = IdMap.add id (t, hint) vs ; store = s; time = time}
    else begin 
      Printf.printf "Known type of %s is %s, wanted %s\n" id (ty_to_string found) (ty_to_string t);
      raise (TypeError id)
    end
  with Not_found -> failwith ("[interp] unknown symbolic var" ^ id)

let add_constraint c ctx =
  { ctx with constraints = c :: ctx.constraints }
     
let add_constraints cs ctx =
  { ctx with constraints = List.rev_append cs ctx.constraints }

let sto_alloc v ctx = 
  let (loc, sto) = Store.alloc v ctx.store in
  (loc, { ctx with store = sto })

let sto_update_field loc v field newval ctx = 
  let { constraints = cs; vars = vs; time = t; store = s } = ctx in
  let cs' = match v with
    | Value (Closure _) ->
      List.rev_append 
        [
          (SAssert (SApp(SId "heapUpdatedAt", [STime (t+1); SLoc loc])))
        ] cs 
    | Value value ->
      List.rev_append 
        [
          (SAssert (SApp(SId "updateFieldPre", [SApp(SId "lookup", [STime t; SLoc loc]); Concrete field])));
          (SAssert (SApp(SId "updateFieldPost", [SApp(SId "lookup", [STime (t+1); SLoc loc]); 
                                                 SApp(SId "lookup", [STime t; SLoc loc]);
                                                 Concrete field;
                                                 newval])));
          (SAssert (SApp(SId "heapUpdatedAt", [STime (t+1); SLoc loc])))
        ] cs 
    | ObjLit (attrs, props) -> 
      List.rev_append 
        [
          (SAssert (SApp(SId "heapUpdatedAt", [STime (t+1); SLoc loc])))
        ] cs 
  in
  { constraints = cs'; vars = vs; time = t+1; store = Store.update loc v ctx.store }

let sto_update loc v ctx = 
  let { constraints = cs; vars = vs; time = t; store = s } = ctx in
  let cs' = match v with
    | Value (Closure _) -> 
      List.rev_append 
        [
          (SAssert (SApp(SId "heapUpdatedAt", [STime (t+1); SLoc loc])))
        ] cs 
    | Value value ->
      List.rev_append 
        [
          (SAssert (SApp(SId "=", [SApp(SId "lookup", [STime t; SLoc loc]); Concrete value])));
          (SAssert (SApp(SId "heapUpdatedAt", [STime (t+1); SLoc loc])))
        ] cs 
    | ObjLit (attrs, props) -> 
      List.rev_append 
        [
          (SAssert (SApp(SId "heapUpdatedAt", [STime (t+1); SLoc loc])))
        ] cs 
  in
  { constraints = cs'; vars = vs; time = t+1; store = Store.update loc v ctx.store }

let sto_lookup loc ctx = 
  Store.lookup loc ctx.store (* in *)
  (* match ret with *)
  (* | Value (Sym id) -> (ret,  *)
  (*                      add_constraint (SAssert (SApp(SId "stx=", [SId id; SApp(SId "lookup", [STime ctx.time; SLoc loc])]))) ctx) *)
  (* | _ -> (ret, ctx) *)
