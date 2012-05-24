open Prelude
open Ljs_syntax




type jsType = 
  | TNull
  | TUndef
  | TString
  | TSymString
  | TBool
  | TNum
  | TObj
  | TFun of int (* arity *)
  | TAny
  | TData
  | TAccessor

type typeEnv = (jsType * string) IdMap.t
exception TypeError of string

(* Used internally where we can have symbolic values or concrete values,
 * namely for attrs *)
type symbool = BTrue | BFalse | BSym of id
type symstring = SString of string | SSym of id

type value =
  (* Scalar types *)
  | Null
  | Undefined
  | Num of float
  | String of string
  | True
  | False
  | Closure of (value list -> ctx -> int -> (result list * exresult list))
  (* ObjPtr is a pointer to an obj in the object store *)
  | ObjPtr of Store.loc
  (* NewSym is an uninitialized symbolic value,
   * which could either be a SymScalar or an ObjPtr *)
  | NewSym of id * Store.loc list (* TODO explain this list *)
  (* SymScalar is a symbolic value of a scalar type
   * (i.e. not a pointer or object) *)
  | SymScalar of id

and objlit =
  | ConObj of objfields
  | SymObj of objfields
  (* Placeholder for uninitialized sym objects
   * Holds the locs of all objects in the store when it was created *)
  | NewSymObj of Store.loc list
and objfields = { attrs: attrsv;
                  conps: propv IdMap.t; (* props with concrete field names *)
                  symps: propv IdMap.t; } (* props with symbolic field names *)
and
  attrsv = { code : Store.loc option; (* will be a Closure *)
             proto : Store.loc; (* ObjPtr, Null, or SymScalar asserted to be Null *)
             extensible : symbool;
             klass : symstring; (* string *)
             primval : Store.loc option; }
and (* Each prop has three attrs: value/accessor, enum, config *)
  propv =
  | Data of datav * symbool * symbool
  | Accessor of accessorv * symbool * symbool
(* Properties hold the location of their values in the value store.
 * Data props also have annother attr: writable *)
and datav = { value : Store.loc; writable : symbool; }
and accessorv = { getter : Store.loc; setter : Store.loc; }
   
and exval = 
  | Break of label * value
  | Throw of value
and label = string

and result = value * ctx
and exresult = exval * ctx

and sto_type = { objs : objlit Store.t; vals : value Store.t }
and ctx = { constraints : sym_exp list;
            vars : typeEnv ;
            time : int ;
            store : sto_type }

(* language of constraints *)
and sym_exp =
  | Hint of string
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

type env = Store.loc IdMap.t

(* Used within GetField and SetField only *)
type field_type = SymField of id | ConField of id

let is_equal a b = SApp (SId "=", [a; b])
let is_not_equal a b = SNot (is_equal a b)

(* TODO what are these? *)
let is_num t l = SApp(SId "isNum", [t; l])
let is_undef t l = SApp(SId "isUndef", [t; l])
let is_null t l = SApp(SId "isNull", [t; l])
let is_absent t l = SApp(SId "isAbsent", [t; l])
let is_bool t l = SApp(SId "isBool", [t; l])
let is_str t l = SApp(SId "isStr", [t; l])
let is_fun t l = SApp(SId "isFun", [t; l])
let is_objcell t l = SApp(SId "isObjCell", [t; l])
let is_obj t l = SApp(SId "isObj", [t; l])

let lookup_store t l = SApp(SId "lookup", [t; l])

let lookup_field o f = SApp(SId "lookupField", [o; f])
let add_dataField o f v w e c = SApp(SId "addField", [o; f; v; w; e; c])
let update_dataField o f v = SApp(SId "updateField", [o; f; v])
  

(* monad *)
let return v (pc : ctx) = ([(v,pc)], [])
let throw v (pc : ctx) = ([], [(v, pc)])
let also_return v pc (rets,exns) = ((v,pc)::rets,exns)
let also_throw v pc (rets,exns) = (rets,(v,pc)::exns)
let combine (r1,e1) (r2,e2) = (List.rev_append r1 r2, List.rev_append e1 e2)
let none = ([],[])

(* usually, the types are
   bind_both ((ret : result list), (exn : exresult list)) 
   (f : result -> (result list * exresult list))
   (g : exresult -> (result list * exresult list)) 
   : (result list * exresult list)
   but in fact the function is slightly more polymorphic than that *)
let bind_both (ret, exn) f g =
  let f_ret = List.map f ret in
  let g_exn = List.map g exn in
  List.fold_left (fun (rets,exns) (ret',exn') -> (List.rev_append ret' rets, List.rev_append exn' exns))
    (List.fold_left (fun (rets,exns) (ret',exn') -> (List.rev_append ret' rets, List.rev_append exn' exns))
       none f_ret)
    g_exn
let bind (ret,exn) f = bind_both (ret,exn) f (fun x -> ([], [x]))
let bind_exn (ret,exn) g = bind_both (ret,exn) (fun x -> ([x], [])) g

let mtPath = { constraints = []; vars = IdMap.empty; store = { objs = Store.empty; vals = Store.empty }; time = 0 }

let ty_to_string t = match t with
  | TNull -> "TNull"
  | TUndef -> "TUndef"
  | TString -> "TString"
  | TSymString -> "TSymString"
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
  (SymScalar s_id, pc')

let field_str field ctx = 
  match field with
  | SymField f -> (f, add_var f TSymString f ctx)
  | ConField f -> const_string f ctx

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

let add_assert a = add_constraint (SAssert a)
let add_let a b = add_constraint (SLet (a, b))

let sto_alloc_val v ctx = 
  let (loc, sto) = Store.alloc v ctx.store.vals in
(*   Printf.eprintf "allocing loc %s in vals\n" (Store.print_loc loc); *)
  (loc, { ctx with store = { ctx.store with vals = sto } })

let sto_alloc_obj v ctx = 
  let (loc, sto) = Store.alloc v ctx.store.objs in
(*   Printf.eprintf "allocing loc %s in objs\n" (Store.print_loc loc); *)
  (loc, { ctx with store = { ctx.store with objs = sto } })

let sto_update_val loc v ctx = 
  { ctx with store = { ctx.store with
    vals = Store.update loc v ctx.store.vals } }

let sto_update_obj loc ov ctx = 
  { ctx with store = { ctx.store with
    objs = Store.update loc ov ctx.store.objs } }

let sto_lookup_obj loc ctx = 
(*   Printf.eprintf "looking for %s in objs\n" (Store.print_loc loc); *)
  Store.lookup loc ctx.store.objs

let sto_lookup_val loc ctx = 
(*   Printf.eprintf "looking for %s in vals\n" (Store.print_loc loc); *)
  Store.lookup loc ctx.store.vals

let hint s pc = add_constraint (Hint s) pc

(* Returns the loc of a newly allocated SymScalar *)
let alloc_sym_scalar name hint_s pc =
  let (sym_id, pc) = fresh_var name TAny hint_s pc in
  let (sym_loc, pc) = sto_alloc_val (SymScalar sym_id) pc in
  (sym_loc, pc)

let alloc_sym_scalar_opt name hint_s pc =
  let (sym_loc, pc') = alloc_sym_scalar name hint_s pc in
  combine
    (return (Some sym_loc) pc')
    (return None pc)

(* Creates a new symbolic boolean to be used as an attr *)
let new_sym_bool name hint_s pc =
  let (sym_id, pc) = fresh_var name TBool hint_s pc in
  (BSym sym_id, pc)

(* Creates a new symbolic string to be used as an attr *)
let new_sym_string name hint_s pc =
  let (sym_id, pc) = fresh_var name TString hint_s pc in
  (SSym sym_id, pc)

(* Creates a NewSym given a list of locs. Should only be used alone when creating the
 * prototypes for symbolic objects (since a sym obj's proto uses the same list of locs.
 * All other new sym allocation should use new_sym *)
let new_sym_from_locs locs name hint pc = 
  let (sym_id, pc) = fresh_var name TAny hint pc in
  (* Create a new symbolic object placeholder, and add it to the store.
   * This will account for the possibility that the new sym is a
   * pointer to an unknown symbolic object. This obj will be init'd later 
   * using init_sym_obj below. *)
  let (new_loc, pc) = sto_alloc_obj (NewSymObj locs) pc in
  (* include the just-allocated location *)
  (NewSym (sym_id, new_loc::locs), pc)

(* Creates a new symbolic value. Does not allocate it in the store. *)
let new_sym hint pc = 
  (* Get locs of all objects in the store so we can branch
   * once we know the type of this sym value *)
  new_sym_from_locs (map fst (Store.bindings pc.store.objs)) "" hint pc

(* Creates a new sym obj whose attributes are all symbolic. Most are scalars, or scalar
 * opts, except for the prototype, which could be a scalar (hopefully Null) or an obj, so
 * we use a NewSym. The locs for this NewSym (i.e., the locs of every object it could be
 * equal to) should be the same as the locs for the sym obj we are init'ing, since the
 * proto would had to have exist before this obj. *)
let init_sym_obj locs loc hint_s pc =
  let (sym_ext, pc) = new_sym_bool "extensible" "extensible attr" pc in
  let (sym_klass, pc) = new_sym_string "klass" "klass attr" pc in
  (*let pc = hint ("new klass at " ^ Store.print_loc klass_loc) pc in*)
  bind (uncurry return (new_sym_from_locs locs "proto"
                          ("new %proto for " ^ (Store.print_loc loc)) pc))
    (fun (proto, pc) ->
      let (proto_loc, pc) = sto_alloc_val proto pc in
      bind (alloc_sym_scalar_opt "code" "code attr" pc)
        (fun (code_loc_opt, pc) ->
          bind (alloc_sym_scalar_opt "primval" "primval attr" pc)
            (fun (pv_loc_opt, pc) ->
              let ret = (SymObj {
                attrs = { code = code_loc_opt; proto = proto_loc; extensible = sym_ext;
                          klass = sym_klass; primval = pv_loc_opt };
                conps = IdMap.empty;
                symps = IdMap.empty
              }) in
              return ret (sto_update_obj loc ret pc))))
