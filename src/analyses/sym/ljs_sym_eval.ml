open Prelude
module S = Ljs_syntax
open Format
open Ljs
open Ljs_sym_values
open Ljs_sym_delta
open Ljs_sym_z3
open Ljs_pretty
open Unix
open SpiderMonkey
open Exprjs_to_ljs
open Js_to_exprjs
open Str

(* flag for debugging *)
let print_store = true

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


let val_sym v = match v with SymScalar x -> (SId x) | _ -> (Concrete v)


let bool b = match b with
  | true -> True
  | false -> False
    
let unbool b ctx = match b with
  | True -> true
  | False -> false
  | _ -> failwith ("tried to unbool a non-bool" ^ (Ljs_sym_pretty.val_to_string b))

let interp_error pos message =
  "[interp] (" ^ string_of_position pos ^ ") " ^ message


(* let string_to_num = *)
(*   let cache = IdHashtbl.create 10 in *)
(*   let count = ref 0 in *)
(*   (fun s -> *)
(*     try IdHashtbl.find s *)
(*     with Not_found -> *)
(*       incr count; IdHashtbl.add s !count; *)
(*       !count) *)
    
let rec apply p func args pc depth = match func with
  | Closure c -> c args pc depth
  (* | ObjPtr c -> begin match !c with *)
  (*     | ({ code = Some cvalue }, _) -> *)
  (*       apply p cvalue args pcs *)
  (*     | _ -> failwith "Applied an object without a code attribute" *)
  (* end *)
  | _ -> failwith (interp_error p 
                     ("Applied non-function, was actually " ^ 
                         Ljs_sym_pretty.val_to_string func))

let get_con_props { conps = con_props } = con_props
let get_sym_props { symps = sym_props } = sym_props
let set_con_props o con_props = { o with conps = con_props }
let set_sym_props o sym_props = { o with symps = sym_props }

(* EUpdateField-Add *)
(* ES5 8.12.5, step 6 *)
let add_field_helper force obj field newval pc get_props set_props = match obj with
  | ObjPtr loc -> begin match sto_lookup_obj loc pc with
    | { attrs = { extensible = ext; }} as o, pc ->
      if not (force || ext) then return Undefined pc else
      let vloc, pc = sto_alloc_val newval pc in
      let newO = set_props o
        (IdMap.add field
           (Data ({ value = vloc; writable = true; }, true, true))
           (get_props o)) in
      return newval (sto_update_obj loc newO pc)
    (*| _, _ -> return Undefined pc [> TODO: Check error in case of non-extensible <]*)
    (* | Value _, _ -> failwith "[interp][add_field] Somehow storing a Value through an ObjPtr" *)
  end
  | _ -> failwith ("[interp] add_field given non-object.")

let add_field = add_field_helper false
(* If we get a field from a sym obj, we might need to add
 * a field without checking extensibility *)
let add_field_force = add_field_helper true

(* (\* Both functions (because a property can satisfy writable and not_writable) *\) *)
(* let rec writable prop = match prop with *)
(*   | Data ({ writable = true; }, _, _) -> true *)
(*   | _ -> false *)

(* let rec not_writable prop = match prop with *)
(*   | Data ({ writable = false; }, _, _) -> true *)
(*   | _ -> false *)


(* Gets an attr of a prop of an object *)
let get_attr attr props field pc = 
  if (not (IdMap.mem field props)) then undef
  else begin match (IdMap.find field props), attr with
    | Data (_, _, config), S.Config
    | Accessor (_, _, config), S.Config -> bool config
    | Data (_, enum, _), S.Enum
    | Accessor (_, enum, _), S.Enum -> bool enum
    | Data ({ writable = b; }, _, _), S.Writable -> bool b
    | Data ({ value = vloc; }, _, _), S.Value -> fst (sto_lookup_val vloc pc)
    | Accessor ({ getter = gloc; }, _, _), S.Getter -> fst (sto_lookup_val gloc pc)
    | Accessor ({ setter = sloc; }, _, _), S.Setter -> fst (sto_lookup_val sloc pc)
    | _ -> failwith "bad access of attribute"
  end
  (*| _ -> failwith ("[interp] get-attr didn't get a string.")*)

(*
  The goal here is to maintain a few invariants (implied by 8.12.9
  and 8.10.5), while keeping things simple from a semantic
  standpoint.  The errors from 8.12.9 and 8.10.5 can be defined in
  the environment and enforced that way.  The invariants here make it
  more obvious that the semantics can't go wrong.  In particular, a
  property
  
  1.  Has to be either an accessor or a data property, and;
  
  2.  Can't change attributes when Config is false, except for
  a. Value, which checks Writable
  b. Writable, which can change true->false
*)
(*let rec set_attr attr obj field newval pc = match obj, field with*)
(*  | ObjPtr loc, String f_str -> *)
(*    let { attrs = { extensible = ext; }; conps = props; } as o, pc = sto_lookup_obj loc pc in*)
(*    if not (IdMap.mem f_str props) then*)
(*      if ext then*)
(*        let newprop, pc = match attr with*)
(*          | S.Getter ->*)
(*            let vloc, pc = sto_alloc_val newval pc in *)
(*            let uloc, pc = sto_alloc_val Undefined pc in*)
(*            (Accessor ({ getter = vloc; setter = uloc; },*)
(*                      false, false), pc)*)
(*          | S.Setter ->*)
(*            let vloc, pc = sto_alloc_val newval pc in *)
(*            let uloc, pc = sto_alloc_val Undefined pc in*)
(*            (Accessor ({ getter = uloc; setter = vloc; },*)
(*                      false, false), pc)*)
(*          | S.Value ->*)
(*            let vloc, pc = sto_alloc_val newval pc in *)
(*            (Data ({ value = vloc; writable = false; }, false, false), pc)*)
(*          | S.Writable ->*)
(*            let uloc, pc = sto_alloc_val Undefined pc in*)
(*            (Data ({ value = uloc; writable = unbool newval pc },*)
(*                  false, false), pc)*)
(*          | S.Enum ->*)
(*            let uloc, pc = sto_alloc_val Undefined pc in*)
(*            (Data ({ value = uloc; writable = false },*)
(*                  unbool newval pc, true), pc)*)
(*          | S.Config ->*)
(*            let uloc, pc = sto_alloc_val Undefined pc in*)
(*            (Data ({ value = uloc; writable = false },*)
(*                  true, unbool newval pc), pc) in*)
(*        let newO = { o with conps = IdMap.add f_str newprop props } in*)
(*        return (bool true) (sto_update_obj loc newO pc)*)
(*      else*)
(*        failwith "[interp] Extending inextensible object ."*)
(*    else*)
(*      (* 8.12.9: "If a field is absent, then its value is considered*)
(*         to be false" -- we ensure that fields are present and*)
(*         (and false, if they would have been absent). *)*)
(*      let newprop, pc = match (IdMap.find f_str props), attr, newval with*)
(*        [> S.Writable true -> false when configurable is false <]*)
(*        | Data ({ writable = true } as d, enum, config), S.Writable, new_w ->*)
(*          (Data ({ d with writable = unbool new_w pc }, enum, config), pc)*)
(*        | Data (d, enum, true), S.Writable, new_w ->*)
(*          (Data ({ d with writable = unbool new_w pc }, enum, true), pc)*)
(*        [> Updating values only checks writable <]*)
(*        | Data ({ writable = true } as d, enum, config), S.Value, v ->*)
(*          let vloc, pc = sto_alloc_val v pc in*)
(*          (Data ({ d with value = vloc }, enum, config), pc)*)
(*        [> If we had a data property, update it to an accessor <]*)
(*        | Data (d, enum, true), S.Setter, setterv ->*)
(*          let sloc, pc = sto_alloc_val setterv pc in*)
(*          let uloc, pc = sto_alloc_val Undefined pc in*)
(*          (Accessor ({ getter = uloc; setter = sloc }, enum, true), pc)*)
(*        | Data (d, enum, true), S.Getter, getterv ->*)
(*          let gloc, pc = sto_alloc_val getterv pc in*)
(*          let uloc, pc = sto_alloc_val Undefined pc in*)
(*          (Accessor ({ getter = gloc; setter = uloc }, enum, true), pc)*)
(*        [> Accessors can update their getter and setter properties <]*)
(*        | Accessor (a, enum, true), S.Getter, getterv ->*)
(*          let gloc, pc = sto_alloc_val getterv pc in*)
(*          (Accessor ({ a with getter = gloc }, enum, true), pc)*)
(*        | Accessor (a, enum, true), S.Setter, setterv ->*)
(*          let sloc, pc = sto_alloc_val setterv pc in*)
(*          (Accessor ({ a with setter = sloc }, enum, true), pc)*)
(*        [> An accessor can be changed into a data property <]*)
(*        | Accessor (a, enum, true), S.Value, v ->*)
(*          let vloc, pc = sto_alloc_val v pc in*)
(*          (Data ({ value = vloc; writable = false; }, enum, true), pc)*)
(*        | Accessor (a, enum, true), S.Writable, w ->*)
(*          let uloc, pc = sto_alloc_val Undefined pc in*)
(*          (Data ({ value = uloc; writable = unbool w pc; }, enum, true), pc)*)
(*        [> enumerable and configurable need configurable=true <]*)
(*        | Data (d, _, true), S.Enum, new_enum ->*)
(*          (Data (d, unbool new_enum pc, true), pc)*)
(*        | Data (d, enum, true), S.Config, new_config ->*)
(*          (Data (d, enum, unbool new_config pc), pc)*)
(*        | Data (d, enum, false), S.Config, False ->*)
(*          (Data (d, enum, false), pc)*)
(*        | Accessor (a, enum, true), S.Config, new_config ->*)
(*          (Accessor (a, enum, unbool new_config pc), pc)*)
(*        | Accessor (a, enum, true), S.Enum, new_enum ->*)
(*          (Accessor (a, unbool new_enum pc, true), pc)*)
(*        | Accessor (a, enum, false), S.Config, False ->*)
(*          (Accessor (a, enum, false), pc)*)
(*        | _ -> failwith "[interp] bad property set"*)
(*      in begin*)
(*        let newO = { o with conps = IdMap.add f_str newprop props } in*)
(*        return (bool true) (sto_update_obj loc newO pc)*)
(*      end*)
(*  | _ -> failwith ("[interp] set-attr didn't get an object and a string")*)

(* 8.10.5, steps 7/8 "If iscallable(getter) is false and getter is not
   undefined..." *)

(* and fun_obj value = match value with *)
(*   | ObjPtr c -> begin match !c with *)
(*       | { code = Some (Closure cv) }, _ -> true *)
(*       | _ -> false *)
(*   end *)
(*   | Undefined -> false *)
(*   | _ -> false *)
    
let rec eval jsonPath maxDepth depth exp env (pc : ctx) : result list * exresult list = 
  (* printf "In eval %s %d %d %s\n" jsonPath maxDepth depth *)
  (*   (Ljs_pretty.exp exp Format.str_formatter; Format.flush_str_formatter()); *)
  if print_store then printf "%s\n" (Ljs_sym_pretty.store_to_string pc.store);
  if (depth >= maxDepth) then none
  else 
    let nestedEval = eval jsonPath maxDepth in
    let eval = eval jsonPath maxDepth depth in 
    (* eval_sym should be called to eval an expression e that is part of an expression
     * which determines whether e is a scalar or a pointer. For instance, the expression
     * e + 1 means e must be a scalar. But the expression e[0] means that e is a pointer.
     * In either case, eval_sym should be used to evaluate e.
     * 
     * First evals e, then checks if the result is a NewSym.
     * If so, initializes it (TODO explain init'ing) and returns the new value.
     * If not, then just returns the value stored for that id.
     *)
    let eval_sym exp env pc =
      bind
        (eval exp env pc)
        (fun (v, pc) -> match v with
        | NewSym (id, obj_locs) ->

          let branch newval pc = return newval
            (* Update every location in the store that has a NewSym
             * with the same id, since that sym value has now been init'd *)
            { pc with store = { pc.store with vals =
              Store.mapi
                (fun loc v -> match v with
                  | NewSym (id', _) -> if id' = id then newval else v
                  | _ -> v)
                pc.store.vals }}
          in

          (* One branch for if its a scalar *)
          let scalar_branch = branch (SymScalar id) pc in
          (* Branches for each object it could point to *)
          let ptr_branches =
            List.fold_left
              (fun branches obj_loc ->
                 combine (branch (ObjPtr obj_loc) pc) branches)
              none obj_locs
          in
          (* One branch if it's a new symbolic object *)
          let objv = {
            symbolic = true;
            (* TODO figure out what attrs an empty sym object has *)
            (* all should be symbolic values of the proper type *)
            (* attrs should be locs like props are *)
            attrs = { code = None; proto = Null; extensible = true;
                      klass = "Object"; primval = None; };
            conps = IdMap.empty;
            symps = IdMap.empty;
          } in
          let (obj_loc, pc_new) = sto_alloc_obj objv pc in
          let new_branch = branch (ObjPtr obj_loc) pc_new in
          combine scalar_branch (combine ptr_branches new_branch)

        | _ -> return v pc)
    in

    match exp with
      | S.Hint (_, _, e) -> eval e env pc
      | S.Undefined _ -> return Undefined pc 
      | S.Null _ -> return Null pc 
      | S.String (_, s) -> let (_, pc) = add_const_str pc s in return (String s) pc
      | S.Num (_, n) -> return (Num n) pc
      | S.True _ -> return True pc
      | S.False _ -> return False pc
      | S.Id (p, x) -> (uncurry return) begin
        if x = "%%newsym" then 
          new_sym ("%%newsym at " ^ (string_of_position p)) pc
        else
          try sto_lookup_val (IdMap.find x env) pc
          with Not_found -> failwith (interp_error p
            ("Unbound identifier: " ^ x ^ " in identifier lookup at "))
        end

      | S.Lambda (p, xs, e) -> 
        let bind_arg arg x (m, pc) = 
          let (loc, pc') = sto_alloc_val arg pc in 
          (IdMap.add x loc m, pc')
        in
        return 
          (Closure (fun args pc depth -> 
            if (List.length args) != (List.length xs) then
              arity_mismatch_err p xs args pc
            else
              let (env_xs, pc_xs) = (List.fold_right2 bind_arg args xs (env, pc)) in
              nestedEval (depth+1) e env_xs pc_xs))
          pc

      | S.Op1 (p, op, e) ->
        bind 
          (eval_sym e env pc)
          (fun (e_val, pc') -> 
            let (t,ret_ty) = typeofOp1 op in 
            try 
              match e_val with
              | SymScalar id -> 
                let pc'' = check_type id t pc' in
                let (ret_op1, pc''') = fresh_var ("P1_" ^ op ^ "_") ret_ty ("return from " ^ op) pc'' in
                return (SymScalar ret_op1)
                  (add_constraint (SLet (ret_op1, SOp1 (op, SId id))) pc''')
              | _ -> 
                try
                  let (ret, pc'') = op1 pc' op e_val in
                  return ret pc''
                with PrimError msg -> throw (Throw (String msg)) pc'
            with TypeError _ -> none)
          
      | S.Op2 (p, op, e1, e2) -> 
        bind
          (eval_sym e1 env pc)
          (fun (e1_val, pc') ->
            bind 
              (eval_sym e2 env pc')
              (fun (e2_val, pc'') -> 
                let (t1, t2, ret_ty) = typeofOp2 op in
                match e1_val, e2_val with
                | SymScalar _, SymScalar _
                | SymScalar _, _
                | _, SymScalar _ -> begin 
                  try 
                    let (sym_e1, pc1) = match e1_val with
                      | SymScalar id -> (SId id, check_type id t1 pc'')
                      | _ -> (Concrete e1_val, pc'') in
                    let (sym_e2, pc2) = match e2_val with
                      | SymScalar id -> (SId id, check_type id t2 pc1)
                      | _ -> (Concrete e2_val, pc1) in
                    let (ret_op, pc3) = fresh_var ("P2_" ^ op ^ "_") ret_ty ("return from " ^ op) pc2 in
                    return (SymScalar ret_op)
                      (add_constraint (SLet (ret_op, SOp2(op, sym_e1, sym_e2))) pc3)
                  with TypeError id -> none 
                end
                | _ ->
                  try
                    let (ret, pc''') = op2 pc'' op e1_val e2_val in
                    return ret pc'''
                  with PrimError msg -> throw (Throw (String msg)) pc''))
          
      | S.If (p, c, t, f) ->
        bind 
          (eval_sym c env pc)
          (fun (c_val, pc') -> 
            match c_val with
            | True -> eval t env pc'
            | SymScalar id -> 
              let true_pc = add_constraint (SAssert (SCastJS (TBool, SId id))) pc' in
              let false_pc  = add_constraint (SAssert (SNot (SCastJS (TBool, SId id)))) pc' in
              combine
                (if is_sat true_pc then (eval t env true_pc)
                 else none)
                (if is_sat false_pc then (eval f env false_pc)
                 else none)
            | _ -> eval f env pc')
          
      | S.App (p, f, args) -> 
        bind 
          (eval_sym f env pc)
          (fun (f_val, pc_f) ->
            let args_pcs : (value list * ctx) list * (exval * ctx) list =
              List.fold_left 
                (fun avpcs arg ->
                  bind avpcs
                    (fun ((argvs : value list), (pcs : ctx)) -> 
                      bind 
                        (* We don't need to eval_sym the args because
                         * they will be rebound in the closure created
                         * for the function body in the S.Lambda case *)
                        (eval arg env pcs)
                        (fun (argv, pcs') ->
                          return (argvs @ [argv]) pcs')))
                ([([], pc_f)], []) args in
            bind args_pcs
              (fun (argvs, pcs) ->
                match f_val with
                | SymScalar f -> 
                  let ((fid : string), (fpc : ctx)) = fresh_var "F" (TFun (List.length argvs)) "function to be applied" pcs in
                  let (argvs : sym_exp list) = List.map val_sym argvs in
                  let ((vs : sym_exp list), (pcs' : ctx)) = List.fold_left
                    (fun (vals, p) exp -> (vals@[exp], p))
                    ([], fpc) argvs in
                  let (res_id, res_pc) = fresh_var "AP" TAny "result of function call" pcs' in 
                  return (SymScalar res_id)
                    (add_constraint (SLet (res_id, (SApp (SId fid, vs))))
                       (add_constraint (SLet (fid, (SId f))) res_pc))
                | _ -> apply p f_val argvs pcs depth))
          
      | S.Seq (p, e1, e2) -> 
        bind 
          (eval e1 env pc) 
          (fun (_, pc') -> eval e2 env pc')

      | S.Let (p, x, e, body) ->
        bind
          (eval e env pc)
          (fun (e_val, pc') -> 
            let (loc, pc'') = sto_alloc_val e_val pc' in 
            eval body (IdMap.add x loc env) pc'')
          
      | S.Rec (p, x, e, body) ->
        let (loc, pc') = sto_alloc_val Undefined pc in
        let env' = IdMap.add x loc env in
        bind
          (eval e env' pc')
          (fun (ev_val, pc') -> 
            let pc'' = sto_update_val loc ev_val pc' in 
            eval body env' pc'')

      | S.SetBang (p, x, e) -> begin
        try
          let loc = IdMap.find x env in
          bind 
            (eval e env pc)
            (fun (e_val, pc') ->
              let pc'' = sto_update_val loc e_val pc' in
              return e_val pc'')
        with Not_found ->
          failwith ("[interp] Unbound identifier: " ^ x ^ " in set! at " ^
                       (string_of_position p))
      end

      | S.Object (p, attrs, props) -> begin 
        (* TODO which of these do we need to eval_sym? *)
        match attrs with
        | { S.primval = valexp;
            S.proto = protoexp;
            S.code = codexp;
            S.extensible = ext;
            S.klass = kls; } ->

          let opt_lift (results, exns) = (map (fun (v, pc) -> (Some v, pc)) results, exns) in
          bind
            (match valexp with
            | None -> return None pc
            | Some vexp -> opt_lift (eval vexp env pc))
            (fun (v, pc_v) ->
              bind
                (match protoexp with
                | None -> return Undefined pc_v
                | Some pexp -> eval_sym pexp env pc_v)
                (fun (p, pc_p) ->
                  bind
                    (match codexp with
                    | None -> return None pc_p
                    | Some cexp -> opt_lift (eval cexp env pc_p))
                    (fun (c, pc_c) ->
                      let attrsv =
                        { primval = v; proto = p; code = c;
                          extensible = ext; klass = kls }
                      in
                      let eval_prop prop pc = match prop with
                        | S.Data ({ S.value = vexp; S.writable = w; }, enum, config) ->
                          bind (eval vexp env pc)
                            (fun (v2, pc_v2) ->
                              let v2loc, pc_v2 = sto_alloc_val v2 pc_v2 in
                              return (Data ({ value = v2loc; writable = w; }, enum, config)) pc_v2)
                        (* TODO do we need eval_sym? *)
                        | S.Accessor ({ S.getter = ge; S.setter = se; }, enum, config) ->
                          bind (eval ge env pc)
                            (fun (v2, pc_v2) ->
                              let v2loc, pc_v2 = sto_alloc_val v2 pc_v2 in
                              bind (eval se env pc_v2)
                                (fun (v3, pc_v3) ->
                                  let v3loc, pc_v3 = sto_alloc_val v3 pc_v3 in
                                  return (Accessor ({ getter = v2loc; setter = v3loc}, enum, config)) pc_v3))
                      in
                      let propvs_pcs  = 
                        List.fold_left
                          (fun maps_pcs (name, prop) -> 
                            bind maps_pcs
                              (fun (map, pc) ->
                                bind 
                                  (eval_prop prop pc)
                                  (fun (propv, pc_v) -> 
                                    let (_, pc') = const_string name pc_v in
                                    return (IdMap.add name propv map) pc')))
                          ([(IdMap.empty, pc_c)], []) props in
                      bind propvs_pcs
                        (fun (propvs, pc_psv) -> 
                          let objv = { symbolic = false; attrs = attrsv;
                                       conps = propvs; symps = IdMap.empty; } in
                          let (loc, pc_obj) = sto_alloc_obj objv pc_psv in
                          return (ObjPtr loc) pc_obj))))
      end
        
      | S.GetAttr (p, attr, obj, field) ->
        failwith "GetAttr NYI"
        (*let rec sym_get_attr attr obj field pc = *)
        (*  try*)
        (*    match (obj, field) with*)
        (*    | ObjPtr loc, String f ->*)
        (*        let { conps = props }, pc = sto_lookup_obj loc pc in*)
        (*        return (get_attr attr props f pc) pc*)
        (*    | Sym o_id, String f ->*)
        (*      let (fn_id, pc') = const_string f pc in*)
        (*      [> todo: assert that (SId fn_id) = (Concrete f) <]*)
        (*      sym_get_attr attr obj (Sym fn_id) pc'*)
        (*    | ObjPtr loc, Sym f ->*)
        (*        let { symps = props }, pc = sto_lookup_obj loc pc in*)
        (*        return (get_attr attr props f pc) pc*)
        (*    [>| ObjPtr loc, Sym f_id -> begin<]*)
        (*      [>let { symps = props }, pc = sto_lookup_obj loc pc in<]*)
        (*      [>combine<]*)
        (*      [>  (IdMap.fold (fun fieldName _ results -><]*)
        (*      [>    let (fn_id, pc') = const_string fieldName pc in<]*)
        (*      [>    let pc'' = add_constraint<]*)
        (*      [>      (SAssert (SApp(SId "=",<]*)
        (*      [>                     [SId f_id; SId fn_id]))) pc' in<]*)
        (*      [>    let (ret_gf, pc''') = fresh_var "GF_" TAny ("@" ^ (Store.print_loc loc) ^ "[\"" ^ fieldName ^ "\"]#" ^ (Ljs_syntax.string_of_attr attr)) pc'' in<]*)
        (*      [>    also_return (Sym ret_gf)<]*)
        (*      [>      (add_constraint <]*)
        (*      [>         (SLet (ret_gf, Concrete (get_attr attr obj (String fieldName) pc'''))) pc''')<]*)
        (*      [>      results)<]*)
        (*      [>     props none)<]*)
        (*      [>  (let none_of = IdMap.fold<]*)
        (*      [>     (fun fieldName _ pc -><]*)
        (*      [>       let (fn_id, pc) = const_string fieldName pc in<]*)
        (*      [>       add_constraint<]*)
        (*      [>         (SAssert (SNot (SApp (SId "=", [SCastJS (TString, SId f_id);<]*)
        (*      [>                                         SCastJS (TString, SId fn_id)])))) pc)<]*)
        (*      [>     props pc in<]*)
        (*      [>   let (ret_gf, pc''') = fresh_var "GF_" TAny <]*)
        (*      [>     ("@" ^ (Store.print_loc loc) ^ "[UNKNOWN]#" ^ (Ljs_syntax.string_of_attr attr))<]*)
        (*      [>     none_of in<]*)
        (*      [>   return (Sym ret_gf)<]*)
        (*      [>     (add_constraint (SLet (ret_gf, Concrete undef)) pc'''))<]*)
        (*    [>end<]*)
        (*    | Sym o_id, Sym f_id ->*)
        (*      let pc_types = check_type o_id TObj (check_type f_id TString pc) in*)
        (*      let (ret_gf, pc'') = fresh_var "GF_" TAny *)
        (*        (o_id ^ "[" ^ f_id ^ "]#" ^ (Ljs_syntax.string_of_attr attr)) pc_types in*)
        (*      let field = SGetField (o_id, f_id) in*)
        (*      let missing = (return (Sym ret_gf) *)
        (*                       (add_constraints [(SAssert (SIsMissing field));*)
        (*                                         (SLet (ret_gf, (Concrete undef)))] pc'')) in*)
        (*      let pc_present = (add_constraints [(SAssert (SNot (SIsMissing field)));*)
        (*                                         (SLet (f_id, field))] pc'') in*)
        (*      (match attr with*)
        (*      | S.Value -> *)
        (*        let pc_present = check_type f_id TData pc_present in*)
        (*        let pc' = add_constraint (SLet (ret_gf, SApp(SId "value", [SId f_id]))) pc_present in*)
        (*        also_return (Sym ret_gf) pc' missing*)
        (*      | S.Writable ->*)
        (*        let pc_present = check_type f_id TData pc_present in*)
        (*        let pc' = add_constraint (SLet (ret_gf, SApp(SId "writable", [SId f_id]))) pc_present in*)
        (*        also_return (Sym ret_gf) (add_constraint (SAssert (SId ret_gf)) pc')*)
        (*          (also_return (Sym ret_gf) (add_constraint (SAssert (SNot (SId ret_gf))) pc')*)
        (*             missing)*)
        (*      | S.Enum ->*)
        (*        let pc' = add_constraint (SLet (ret_gf, SApp(SId "enumerable", [SId f_id]))) pc_present in*)
        (*        also_return (Sym ret_gf) (add_constraint (SAssert (SId ret_gf)) pc')*)
        (*          (also_return (Sym ret_gf) (add_constraint (SAssert (SNot (SId ret_gf))) pc')*)
        (*             missing)*)
        (*      | S.Config ->*)
        (*        let pc' = add_constraint (SLet (ret_gf, SApp(SId "config", [SId f_id]))) pc_present in*)
        (*        also_return (Sym ret_gf) (add_constraint (SAssert (SId ret_gf)) pc')*)
        (*          (also_return (Sym ret_gf) (add_constraint (SAssert (SNot (SId ret_gf))) pc')*)
        (*             missing)*)
        (*      | S.Getter ->*)
        (*        let pc_present = check_type f_id TAccessor pc_present in*)
        (*        let pc' = add_constraint (SLet (ret_gf, SApp(SId "getter", [SId f_id]))) pc_present in*)
        (*        also_return (Sym ret_gf) pc' missing*)
        (*      | S.Setter ->*)
        (*        let pc_present = check_type f_id TAccessor pc_present in*)
        (*        let pc' = add_constraint (SLet (ret_gf, SApp(SId "setter", [SId f_id]))) pc_present in*)
        (*        also_return (Sym ret_gf) pc' missing)*)
        (*    | _ -> failwith ("[interp] GetAttr got a non-object or a non-string field name: (get-attr "*)
        (*                     ^ Ljs_sym_pretty.val_to_string obj ^ " "*)
        (*                     ^  Ljs_sym_pretty.val_to_string field ^ ")")*)
        (*  with TypeError _ -> none*)
        (*in*)
        (*bind (eval obj env pc)*)
        (*  (fun (obj_val, pc_obj) ->*)
        (*    bind (eval field env pc_obj)*)
        (*      (fun (f_val, pc_f) -> sym_get_attr attr obj_val f_val pc_f))*)

      | S.GetObjAttr _ -> failwith "[sym_eval] GetObjAttr NYI"
      | S.SetObjAttr _ -> failwith "[sym_eval] SetObjAttr NYI"
 
      (* Invariants on the concrete and symbolic field maps in an object:
       * 1) All field names in both maps are distinct from
       *    all other field names in both maps
       *
       * These are the only constraints imposed by our representation. All other
       * constraints must be checked by Z3.
       *)
      | S.GetField (p, obj_ptr, f, args) ->
        (* ptr_get is the original object ptr we get from, whereas
         * ptr_check could be any object ptr in the prototype chain. *)
        let rec sym_get_field ptr_get ptr_check field getter_params pc depth =
          (* Let [same] be the type of field (symbolic or concrete)
           * and [diff] be the opposite. get_both_props produces
           * a pair ([same] props, [diff] props) *)
          match field with String _ | SymScalar _ -> begin
          let (f, get_both_props, get_props, set_props) = match field with
          | String f    -> (f, (fun { conps = cons; symps = syms; } -> (cons, syms)),
                            get_con_props, set_con_props)
          | SymScalar f -> (f, (fun { conps = cons; symps = syms; } -> (syms, cons)),
                            get_sym_props, set_sym_props)
          | _ -> failwith "get_field given non-string/sym field, but should have already caught it"
          in

          try match ptr_check with
          | Null -> begin match ptr_get with
            | Null -> return Undefined pc
            | ObjPtr loc ->
              let { symbolic = is_sym; }, pc = sto_lookup_obj loc pc in
              if is_sym
              (* For sym objs, if field not found, make a new sym value and add it
               * to the object at that field, then return it *)
              then
                let (symv, pc) = new_sym ("get_field at " ^
                                    (string_of_position p)) pc in
                add_field_force ptr_get f symv pc get_props set_props
              (* For con objs, if field not found, return Undef *)
              else return Undefined pc
            | _ -> failwith "get_field given non-object, but should have already caught it"
            end
          | ObjPtr obj_loc ->
            (* If f is present in the [same] field map, we simply get its value
             * If f is not present in the [same] field map, either
             *    a) f is equal to one of the [diff] field names
             *    b) f is equal to one of the [same] field names
             *    c) f is not equal to any of the field names, so we check the prototype
             *
             * -- Note that (b) is infeasible in the concrete case, but makes the branches
             *    symmetric with the way we handle symbolic field names. The infeasibility
             *    of (b) is not imposed by our object invariants, so we fall back on
             *    Z3 to catch it rather than try to catch it ourselves.
             *)
            let { attrs = { proto = proto; }} as objv, pc = sto_lookup_obj obj_loc pc in
            let same_props, diff_props = get_both_props objv in

            let return_prop v pc = match v with
              | Data ({ value = vloc; }, _, _) ->
                (uncurry return) (sto_lookup_val vloc pc)
              | Accessor ({ getter = gloc; }, _, _) ->
                let g, pc = sto_lookup_val gloc pc in
                apply p g getter_params pc depth
            in

            (* If f is present in the [same] field map, we simply get its value *)
            begin try
              let v = IdMap.find f same_props in 
              return_prop v pc
            (* If f is not present in the [same] field map, either *)
            with Not_found -> 
              (*    a) f is equal to one of the [diff] field names *)
              (*    b) f is equal to one of the [same] field names *)
              let branches = List.fold_left
                (fun branches (f', v) ->
                  let (f'_const, pc') = const_string f' pc in
                  let pc'' = add_constraint
                    (SAssert (SApp (SId "=", [SId f; SId f'_const]))) pc' in
                  combine (return_prop v pc'') branches)
                none
                (List.concat (map IdMap.bindings [same_props; diff_props])) in
              (*    c) f is not equal to any of the field names, so we check the prototype *)
              let assert_none_equal = IdMap.fold
                (fun f' _ pc ->
                  let (f', pc') = const_string f' pc in
                  let pc'' = add_constraint
                    (SAssert (SNot (SApp (SId "=", [SId f; SId f'])))) pc' in
                  pc'') in
              let none_pc = assert_none_equal same_props
                              (assert_none_equal diff_props pc) in
              let none_branch = sym_get_field ptr_get proto field
                                  getter_params none_pc depth in
              combine none_branch branches
            end

          | _ -> throw (Throw (String "get_field on a non-object")) pc
          with TypeError _ -> none
          end
          | _ -> throw (Throw (String ("get_field called with non-string/sym field: " ^
                               Ljs_sym_pretty.val_to_string field))) pc
          (*| _ -> failwith (interp_error p*)
          (*                   "get_field on a non-object.  The expression was (get-field "*)
          (*                 ^ Ljs_sym_pretty.val_to_string obj1*)
          (*                 ^ " " ^ Ljs_sym_pretty.val_to_string (List.nth getter_params 0)*)
          (*                 ^ " " ^ Ljs_sym_pretty.val_to_string field ^ ")")*)
        in
        bind (eval_sym obj_ptr env pc)
          (fun (obj_ptrv, pc_o) -> 
            bind (eval_sym f env pc_o) 
              (fun (fv, pc_f) -> 
                bind (eval args env pc_f)
                  (fun (argsv, pc') ->
                    sym_get_field obj_ptrv obj_ptrv fv [obj_ptrv; argsv] pc' depth)))

          

      | S.SetField (p, obj, f, v, args) ->
        (*Printf.printf "******* In SetField\n";*)
        let rec sym_set_field objCheck objSet field newval setter_params pc depth = 
          (* Let [same] be the type of f (symbolic or concrete) and [diff] be the opposite
           * Whenever we set a field, it is set on the original object
           *
           * If f is present in the [same] field map, we simply set its value
           * If f is not present in the [same] field map, either
           *    a) f is equal to one of the [same] field names
           *    b) f is equal to one of the [diff] field names
           *    c) f is not equal to any of the field names, so we check the prototype
           *      - if the object doesn't have a prototype, add the field
           *)
          (* get_props should produce a pair ([same] props, [diff] props) *)
          (* set_same should take an object and a new [same] props map
           *  and produce a new object with the new [same] props map *)
          (* set_diff should do the same for [diff] props *)
          let set_field obj_loc f get_props set_same set_diff = 
            let { attrs = { proto = proto; }} as objv, pc = sto_lookup_obj obj_loc pc in
            let same_props, diff_props = get_props objv in

            (* Update the property at fieldName in props.
             * Should only be called when fieldName is guaranteed to be present. *)
            let update_prop set_props fieldName props pc =
              try match IdMap.find fieldName props with
              | Data ({ writable = true; }, enum, config) ->
                let vloc, pc = sto_alloc_val newval pc in
                let newO = set_props objv
                  (IdMap.add fieldName
                     (Data ({ value = vloc; writable = true }, enum, config))
                     props) in
                let (z3field, pc') = const_string fieldName pc in
                return newval (sto_update_field obj_loc newO (SymScalar z3field) (Concrete newval) pc') (* TODO what's this?? probably don't need the prev line either *)
              | Accessor ({ setter = sloc; }, _, _) ->
                let s, pc = sto_lookup_val sloc pc in
                apply p s setter_params pc depth
              | _ -> failwith "SetField NYI for non-writable fields"
              with Not_found -> failwith ("Impossible! update_prop was called with" ^
                " a field name that wasn't present in the field map")
            in
            let update_same = update_prop set_same in
            let update_diff = update_prop set_diff in

            (* Creates branches for each property f' in the given property map where
             * f is asserted equal to f' and the new value is stored at f'.*)
            let prop_branches update_fun props = IdMap.fold
              (fun f' _ branches ->
                let (f'_id, pc') = const_string f' pc in
                let pc'' = add_constraint
                  (SAssert (SApp (SId "=", [SId f; SId f'_id]))) pc' in
                combine (update_fun f' props pc'') branches)
              props none
            in
            (* If f is present in the [same] field map, we simply set its value *)
            if IdMap.mem f same_props 
            then update_same f same_props pc
            (* If f is not present in the [same] field map, either *)
            else
            (*    a) f is equal to one of the [diff] field names *)
            (*    b) f is equal to one of the [same] field names *)
            let branches = combine (prop_branches update_diff diff_props)
                             (prop_branches update_same same_props) in
            (*    c) f is not equal to any of the field names, so we check the prototype *)
            let assert_none_equal = IdMap.fold
              (fun f' _ pc ->
                let (f', pc') = const_string f' pc in
                let pc'' = add_constraint
                  (SAssert (SNot (SApp (SId "=", [SId f; SId f'])))) pc' in
                pc'')
            in
            let none_pc = assert_none_equal same_props
                            (assert_none_equal diff_props pc) in
            let none_branch = sym_set_field proto objSet field newval
                                setter_params none_pc depth in
            combine none_branch branches
          in

          (* TODO handle sym objects *)
          match objCheck, field with
          | Null, String f    -> add_field objSet f newval pc get_con_props set_con_props
          | Null, SymScalar f -> add_field objSet f newval pc get_sym_props set_sym_props
          | ObjPtr loc, String f -> set_field loc f
              (fun { conps = cons; symps = syms; } -> (cons, syms)) (* get_props *)
              set_con_props (* set_same_props *)
              set_sym_props (* set_diff_props *)
          | ObjPtr loc, SymScalar f -> set_field loc f
              (fun { conps = cons; symps = syms; } -> (syms, cons)) (* get_props *)
              set_sym_props (* set_same_props *)
              set_con_props (* set_diff_props *)
          (*| Sym id, String f*)
          (*| Sym id, Sym f -> failwith "SetField NYI for sym objects."*)
          | _ -> throw (Throw (String "set_field on a non-object")) pc
          (*| _ -> failwith "[sym_set_field] should not have happened"*)
        in
        bind (eval_sym obj env pc) 
          (fun (objv, pc_o) -> 
            bind (eval_sym f env pc_o) 
              (fun (fv, pc_f) -> 
                bind (eval v env pc_f)
                  (fun (vv, pc_v) -> 
                    bind (eval args env pc_v)
                      (fun (argvs, pc_a) ->
                        sym_set_field objv objv fv vv [objv; argvs] pc_a depth))))

      | S.SetAttr (p, attr, obj, field, newval) ->
        failwith "SetAttr NYI"
        (*bind (eval obj env pc)*)
        (*  (fun (objv, pc_o) -> *)
        (*    bind (eval field env pc_o)*)
        (*      (fun (fv, pc_f) -> *)
        (*        bind (eval newval env pc_f)*)
        (*          (fun (vv, pc_v) ->*)
        (*            set_attr attr objv fv vv pc_v)))*)

                  
      (*
        | S.DeleteField (p, obj, f) ->
        let obj_val = eval obj env in
        let f_val = eval f env in begin
        match (obj_val, f_val) with
        | (ObjPtr c, String s) -> 
        begin match !c with
        | (attrs, props) -> begin try
        match IdMap.find s props with
        | Data (_, _, true) 
        | Accessor (_, _, true) ->
        begin
        c := (attrs, IdMap.remove s props);
        True
        end
        | _ -> False
        with Not_found -> False
        end
        end
        | _ -> failwith ("[interp] Delete field didn't get an object and a string at " 
        ^ string_of_position p 
        ^ ". Instead, it got " 
        ^ Ljs_sym_pretty.to_string obj_val
        ^ " and " 
        ^ Ljs_sym_pretty.to_string f_val)
        end *)


      | S.OwnFieldNames _ -> failwith "[ljs_sym_eval] OwnFieldNames NYI"
          
      | S.Label (p, l, e) -> begin
        bind_exn
          (eval e env pc)
          (fun (e, pc') ->
            match e with
            | Break (l', v) -> if (l = l') then return v pc' else throw e pc'
            | _ -> throw e pc')
      end
      | S.Break (p, l, e) ->
        bind 
          (eval e env pc)
          (fun (v, pc') -> throw (Break (l, v)) pc')
      | S.TryCatch (p, body, catch) -> begin
        bind_exn
          (eval body env pc)
          (fun (e, pc') -> match e with
          | Throw v -> 
            bind
              (eval catch env pc')
              (fun (c, pc'') -> apply p c [v] pc'' depth)
          | _ -> throw e pc')
      end
      | S.TryFinally (p, body, fin) -> 
        bind_both
          (eval body env pc)
          (fun (_, pc') -> eval fin env pc')
          (fun (e, pc') -> 
            bind 
              (eval fin env pc')
              (fun (_, pc'') -> throw e pc''))
      | S.Throw (p, e) -> 
        bind
          (eval e env pc)
          (fun (v, pc') -> throw (Throw v) pc')
      (*
        | S.Eval (p, e) ->
        match eval e env with
        | String s -> eval_op s env jsonPath
        | v -> v
      *)
      | S.DeleteField _ -> failwith "[interp] not yet implemented (DeleteField)"
      | S.Eval _ -> failwith "[interp] not yet implemented (Eval)"



and arity_mismatch_err p xs args pc =
  failwith ("Arity mismatch, supplied " ^ string_of_int (List.length args) ^ 
               " arguments and expected " ^ string_of_int (List.length xs) ^ 
               " at " ^ string_of_position p ^ ". Arg names were: " ^ 
               (List.fold_right (^) (map (fun s -> " " ^ s ^ " ") xs) "") ^ 
               ". Values were: " ^ 
               (List.fold_right (^) (map (fun v -> " " ^ 
                 Ljs_sym_pretty.val_to_string v ^ " ") args) ""))

(* This function is exactly as ridiculous as you think it is.  We read,
   parse, desugar, and evaluate the string, storing it to temp files along
   the way.  We make no claims about encoding issues that may arise from
   the filesystem.  Thankfully, JavaScript is single-threaded, so using
   only a single file works out. 

   TODO(joe): I have no idea what happens on windows. *)
and eval_op str env jsonPath maxDepth pc = 
  let outchan = open_out "/tmp/curr_eval.js" in
  output_string outchan str;
  close_out outchan;
  let cmdstring = 
    (sprintf "%s /tmp/curr_eval.js 1> /tmp/curr_eval.json 2> /tmp/curr_evalerr.json" jsonPath) in
  ignore (system cmdstring);
  let inchan = open_in "/tmp/curr_evalerr.json" in
  let buf = String.create (in_channel_length inchan) in
  really_input inchan buf 0 (in_channel_length inchan);
  let json_err = regexp (quote "SyntaxError") in
  try
    ignore (search_forward json_err buf 0);
    throw (Throw (String "EvalError")) pc
  with Not_found -> begin
    let ast =
      parse_spidermonkey (open_in "/tmp/curr_eval.json") "/tmp/curr_eval.json" in
    try
      let (used_ids, exprjsd) = 
        js_to_exprjs ast (Exprjs_syntax.IdExpr (dummy_pos, "%global")) in
      let desugard = exprjs_to_ljs used_ids exprjsd in
      if (IdMap.mem "%global" env) then
        (Ljs_pretty.exp desugard std_formatter; print_newline ();
         eval jsonPath maxDepth 0 desugard env pc (* TODO: which env? *))
      else
        (failwith "no global")
    with ParseError _ -> throw (Throw (String "EvalError")) pc
  end

let rec eval_expr expr jsonPath maxDepth pc = 
  bind_exn
    (eval jsonPath maxDepth 0 expr IdMap.empty pc)
    (fun (e, pc) -> match e with
    | Throw v ->
      let err_msg = 
        match v with
        | ObjPtr loc -> begin
          let { conps = props }, pc = sto_lookup_obj loc pc in
          try
            match IdMap.find "message" props with
            | Data ({ value = msg_val_loc; }, _, _) ->
              let msg_val, pc = sto_lookup_val msg_val_loc pc in
              (Ljs_sym_pretty.val_to_string msg_val)
            | _ -> (Ljs_sym_pretty.val_to_string v)
          with Not_found -> (Ljs_sym_pretty.val_to_string v)
        end
        | v -> (Ljs_sym_pretty.val_to_string v) in
      throw (str ("Uncaught exception: " ^ err_msg)) pc
    | Break (l, v) -> throw (str ("Broke to top of execution, missed label: " ^ l)) pc)
