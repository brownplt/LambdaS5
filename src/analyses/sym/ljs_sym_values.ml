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
             proto : Store.loc;
             extensible : bool;
             klass : Store.loc;
             primval : Store.loc option; }
and
  propv = 
  | Data of datav * bool * bool
  | Accessor of accessorv * bool * bool
(* Properties hold the location of their values in the value store *)
and datav = { value : Store.loc; writable : bool; }
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

let sto_alloc_val v ctx = 
  let (loc, sto) = Store.alloc v ctx.store.vals in
(*   Printf.eprintf "allocing loc %s in vals\n" (Store.print_loc loc); *)
  (loc, { ctx with store = { ctx.store with vals = sto } })

let sto_alloc_obj v ctx = 
  let (loc, sto) = Store.alloc v ctx.store.objs in
(*   Printf.eprintf "allocing loc %s in objs\n" (Store.print_loc loc); *)
  (loc, { ctx with store = { ctx.store with objs = sto } })

let sto_update_field loc v field newval ctx = 
  let { constraints = cs; vars = vs; time = t; store = s } = ctx in
  let cs' = cs 
    (*match v with*)
    (* | (Closure _) -> *)
    (*   List.rev_append  *)
    (*     [ *)
    (*       (SAssert (SApp(SId "heapUpdatedAt", [STime (t+1); SLoc loc]))) *)
    (*     ] cs  *)
    (* | value -> *)
    (*   List.rev_append  *)
    (*     [ *)
    (*       (SAssert (SApp(SId "updateFieldPre", [SApp(SId "lookup", [STime t; SLoc loc]); Concrete field]))); *)
    (*       (SAssert (SApp(SId "updateFieldPost", [SApp(SId "lookup", [STime (t+1); SLoc loc]);  *)
    (*                                              SApp(SId "lookup", [STime t; SLoc loc]); *)
    (*                                              Concrete field; *)
    (*                                              newval]))); *)
    (*       (SAssert (SApp(SId "heapUpdatedAt", [STime (t+1); SLoc loc]))) *)
    (*     ] cs  *)
    (*| (attrs, props) -> *)
    (*  List.rev_append *)
    (*    [*)
    (*      (SAssert (SApp(SId "heapUpdatedAt", [STime (t+1); SLoc loc])))*)
    (*    ] cs *)
  in
  { constraints = cs'; vars = vs; time = t+1; store = {s with objs = Store.update loc v ctx.store.objs} }

let sto_update_val loc v ctx = 
  let { constraints = cs; vars = vs; time = t; store = s } = ctx in
  let cs' = cs (* match v with*)
  (*  | (Closure _) -> *)
  (*    List.rev_append *)
  (*      [*)
  (*        (SAssert (SApp(SId "heapUpdatedAt", [STime (t+1); SLoc loc])))*)
  (*      ] cs *)
  (*  | value ->*)
  (*    List.rev_append *)
  (*      [*)
  (*        (SAssert (SApp(SId "=", [SApp(SId "lookup", [STime t; SLoc loc]); Concrete value])));*)
  (*        (SAssert (SApp(SId "heapUpdatedAt", [STime (t+1); SLoc loc])))*)
  (*      ] cs *)
  in
  { constraints = cs'; vars = vs; time = t+1; 
    store = { ctx.store with vals = Store.update loc v ctx.store.vals } }

let sto_update_obj loc v ctx = 
  let { constraints = cs; vars = vs; time = t; store = s } = ctx in
  let cs' = cs (* match v with *)
    (* | (attrs, props) ->  *)
      (*List.rev_append *)
      (*  [*)
      (*    (SAssert (SApp(SId "heapUpdatedAt", [STime (t+1); SLoc loc])))*)
      (*  ] cs *)
  in
  { constraints = cs'; vars = vs; time = t+1; 
    store = {ctx.store with objs = Store.update loc v ctx.store.objs } }

let sto_lookup_obj loc ctx = 
(*   Printf.eprintf "looking for %s in objs\n" (Store.print_loc loc); *)
  (Store.lookup loc ctx.store.objs, ctx)

let sto_lookup_val loc ctx = 
(*   Printf.eprintf "looking for %s in vals\n" (Store.print_loc loc); *)
  let ret = Store.lookup loc ctx.store.vals  in 
  (ret, ctx)
  (*match ret with *)
  (*| SymScalar id -> *)
  (*  (ret,*)
  (*   add_constraint (SAssert (SApp(SId "stx=", [SId id; SApp(SId "lookup", [STime ctx.time; SLoc loc])]))) ctx)*)
  (*| _ -> (ret, ctx)*)

let hint s pc = add_constraint (Hint s) pc

let new_sym_scalar name hint_s pc =
  let (sym_id, pc) = fresh_var name TAny hint_s pc in
  let (sym_loc, pc) = sto_alloc_val (SymScalar sym_id) pc in
  (sym_loc, pc)

let new_opt_sym_val name hint_s pc =
  let (symval, pc') = (new_sym_scalar name hint_s pc) in
  combine (return (Some symval) (hint ("Some " ^ hint_s) pc')) none (* (return None pc) *)

let new_sym_helper locs hint pc = 
  let (sym_id, pc) = fresh_var "" TAny hint pc in
  let (new_loc, pc) = sto_alloc_obj (NewSymObj locs) pc in
  (* include the just-allocated location *)
  (NewSym (sym_id, new_loc::locs), pc)

let new_sym hint pc = 
  (* Get locs of all objects in the store so we can branch
   * once we know the type of this sym value *)
  new_sym_helper (map fst (Store.bindings pc.store.objs)) hint pc

let new_sym_obj existing_locs loc hint_s pc =
  (* Create a new symbolic object, and add it to the store.
   * This will account for the possibility that the new sym is a
   * pointer pointing to an unknown symbolic object. *)
  bind (new_opt_sym_val "code" "code field" pc)
    (fun (code_loc, pc) ->
      bind (combine (return true (hint "extensible = true" pc)) (return false pc))
        (fun (extensible, pc) ->
          let (klass_loc, pc) = new_sym_scalar "klass" "klass attr" pc in
          let pc = hint ("new klass at " ^ Store.print_loc klass_loc) pc in
          bind (new_opt_sym_val "primval" "primval attr" pc)
            (fun (primval_loc, pc) ->
              bind (uncurry return (new_sym_helper existing_locs "proto" (hint ("new %proto for " ^ (Store.print_loc loc)) pc)))
                (fun (proto, pc) ->
                  let (proto_loc, pc) = sto_alloc_val proto pc in
                  let ret = (SymObj {
                    attrs = { code = code_loc; proto = proto_loc; extensible = extensible;
                              klass = klass_loc; primval = primval_loc };
                    conps = IdMap.empty;
                    symps = IdMap.empty
                  }) in
                  return ret (sto_update_obj loc ret pc)))))
