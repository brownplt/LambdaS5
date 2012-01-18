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


let val_sym v = match v with Sym x -> (SId x) | _ -> (Concrete v)


let bool b = match b with
  | true -> True
  | false -> False
    
let unbool b = match b with
  | True -> true
  | False -> false
  | _ -> failwith ("tried to unbool a non-bool" ^ (Ljs_sym_pretty.to_string b))

let interp_error pos message =
  "[interp] (" ^ string_of_position pos ^ ") " ^ message

let fresh_var = 
  let count = ref 0 in
  (fun prefix t pc ->
    incr count;
    let nvar = "%%" ^ prefix ^ (string_of_int !count) in
    (nvar, (add_var nvar t pc)))
    
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
  (* | ObjCell c -> begin match !c with *)
  (*     | ({ code = Some cvalue }, _) -> *)
  (*       apply p cvalue args pcs *)
  (*     | _ -> failwith "Applied an object without a code attribute" *)
  (* end *)
  | _ -> failwith (interp_error p 
                     ("Applied non-function, was actually " ^ 
                         Ljs_sym_pretty.to_string func))

let rec get_field p obj1 field getter_params result pc depth = match obj1 with
  | Null -> return Undefined pc (* nothing found *)
  | ObjCell c -> begin
    let ({proto = pvalue; }, props) = !c in
    try match IdMap.find field props with
    | Data ({ value = v; }, _, _) -> return (result v) pc
    | Accessor ({ getter = g; }, _, _) ->
      apply p g getter_params pc depth
    (* Not_found means prototype lookup is necessary *)
    with Not_found ->
      get_field p pvalue field getter_params result pc depth
  end
  | _ -> failwith (interp_error p
                     "get_field on a non-object.  The expression was (get-field "
                   ^ Ljs_sym_pretty.to_string obj1
                   ^ " " ^ Ljs_sym_pretty.to_string (List.nth getter_params 0)
                   ^ " " ^ field ^ ")")


(* EUpdateField-Add *)
(* ES5 8.12.5, step 6 *)
let rec add_field obj field newval result = match obj with
  | ObjCell c -> begin match !c with
    | { extensible = true; } as attrs, props ->
      begin
        c := (attrs, IdMap.add field
          (Data ({ value = newval; writable = true; }, true, true))
          props);
        result newval
      end
    | _ -> result Undefined(* TODO: Check error in case of non-extensible *)
  end
  | _ -> failwith ("[interp] add_field given non-object.")

(* (\* Both functions (because a property can satisfy writable and not_writable) *\) *)
(* let rec writable prop = match prop with *)
(*   | Data ({ writable = true; }, _, _) -> true *)
(*   | _ -> false *)

(* let rec not_writable prop = match prop with *)
(*   | Data ({ writable = false; }, _, _) -> true *)
(*   | _ -> false *)

(* EUpdateField *)
(* ES5 8.12.4, 8.12.5 *)
let rec update_field p obj1 obj2 field newval setter_args result = match obj1 with
  (* 8.12.4, step 4 *)
  | Null -> add_field obj2 field newval result
  | ObjCell c -> begin match !c with
    | { proto = pvalue; } as attrs, props ->
      if (not (IdMap.mem field props)) then
        (* EUpdateField-Proto *)
        update_field p pvalue obj2 field newval setter_args result
      else
        match (IdMap.find field props) with
        | Data ({ writable = true; }, enum, config) ->
          (* This check asks how far down we are in searching *)
          if (not (obj1 == obj2)) then
            (* 8.12.4, last step where inherited.[[writable]] is true *)
            add_field obj2 field newval result
          else begin
            (* 8.12.5, step 3, changing the value of a field *)
            c := (attrs, IdMap.add field
              (Data ({ value = newval; writable = true }, enum, config))
              props);
            result newval
          end
        | Accessor ({ setter = setterv; }, enum, config) ->
          (* 8.12.5, step 5 *)
          apply p setterv setter_args
        | _ -> failwith "Field not writable!"
  end
  | _ -> failwith ("[interp] set_field received (or found) a non-object.  The call was (set-field " ^ Ljs_sym_pretty.to_string obj1 ^ " " ^ Ljs_sym_pretty.to_string obj2 ^ " " ^ field ^ " " ^ Ljs_sym_pretty.to_string newval ^ ")" )

let get_attr attr obj field = match obj, field with
  | ObjCell c, String s -> let (attrs, props) = !c in
      if (not (IdMap.mem s props)) then
        undef
      else
        begin match (IdMap.find s props), attr with
          | Data (_, _, config), S.Config
          | Accessor (_, _, config), S.Config -> bool config
          | Data (_, enum, _), S.Enum
          | Accessor (_, enum, _), S.Enum -> bool enum
          | Data ({ writable = b; }, _, _), S.Writable -> bool b
          | Data ({ value = v; }, _, _), S.Value -> v
          | Accessor ({ getter = gv; }, _, _), S.Getter -> gv
          | Accessor ({ setter = sv; }, _, _), S.Setter -> sv
          | _ -> failwith "bad access of attribute"
        end
  | _ -> failwith ("[interp] get-attr didn't get an object and a string.")

(* (\*  *)
(*    The goal here is to maintain a few invariants (implied by 8.12.9 *)
(*    and 8.10.5), while keeping things simple from a semantic *)
(*    standpoint.  The errors from 8.12.9 and 8.10.5 can be defined in *)
(*    the environment and enforced that way.  The invariants here make it *)
(*    more obvious that the semantics can't go wrong.  In particular, a *)
(*    property *)

(*    1.  Has to be either an accessor or a data property, and; *)

(*    2.  Can't change attributes when Config is false, except for  *)
(*        a. Value, which checks Writable *)
(*        b. Writable, which can change true->false *)
(* *\) *)
(* let rec set_attr attr obj field newval = match obj, field with *)
(*   | ObjCell c, String f_str -> begin match !c with *)
(*       | ({ extensible = ext; } as attrsv, props) -> *)
(*         if not (IdMap.mem f_str props) then *)
(*           if ext then  *)
(*             let newprop = match attr with *)
(*               | S.Getter ->  *)
(*                 Accessor ({ getter = newval; setter = Undefined; },  *)
(*                           false, false) *)
(*               | S.Setter ->  *)
(*                 Accessor ({ getter = Undefined; setter = newval; },  *)
(*                           false, false) *)
(*               | S.Value ->  *)
(*                 Data ({ value = newval; writable = false; }, false, false) *)
(*               | S.Writable -> *)
(*                 Data ({ value = Undefined; writable = unbool newval }, *)
(*                       false, false)  *)
(*               | S.Enum -> *)
(*                 Data ({ value = Undefined; writable = false }, *)
(*                       unbool newval, true)  *)
(*               | S.Config -> *)
(*                 Data ({ value = Undefined; writable = false }, *)
(*                       true, unbool newval) in *)
(*             c := (attrsv, IdMap.add f_str newprop props); *)
(*             true *)
(*           else *)
(*             failwith "[interp] Extending inextensible object ." *)
(*         else *)
(*         (\* 8.12.9: "If a field is absent, then its value is considered *)
(*         to be false" -- we ensure that fields are present and *)
(*         (and false, if they would have been absent). *\) *)
(*           let newprop = match (IdMap.find f_str props), attr, newval with *)
(*             (\* S.Writable true -> false when configurable is false *\) *)
(*             | Data ({ writable = true } as d, enum, config), S.Writable, new_w ->  *)
(*               Data ({ d with writable = unbool new_w }, enum, config) *)
(*             | Data (d, enum, true), S.Writable, new_w -> *)
(*               Data ({ d with writable = unbool new_w }, enum, true) *)
(*             (\* Updating values only checks writable *\) *)
(*             | Data ({ writable = true } as d, enum, config), S.Value, v -> *)
(*               Data ({ d with value = v }, enum, config) *)
(*             (\* If we had a data property, update it to an accessor *\) *)
(*             | Data (d, enum, true), S.Setter, setterv -> *)
(*               Accessor ({ getter = Undefined; setter = setterv }, enum, true) *)
(*             | Data (d, enum, true), S.Getter, getterv -> *)
(*               Accessor ({ getter = getterv; setter = Undefined }, enum, true) *)
(*             (\* Accessors can update their getter and setter properties *\) *)
(*             | Accessor (a, enum, true), S.Getter, getterv -> *)
(*               Accessor ({ a with getter = getterv }, enum, true) *)
(*             | Accessor (a, enum, true), S.Setter, setterv -> *)
(*               Accessor ({ a with setter = setterv }, enum, true) *)
(*             (\* An accessor can be changed into a data property *\) *)
(*             | Accessor (a, enum, true), S.Value, v -> *)
(*               Data ({ value = v; writable = false; }, enum, true) *)
(*             | Accessor (a, enum, true), S.Writable, w -> *)
(*               Data ({ value = Undefined; writable = unbool w; }, enum, true) *)
(*             (\* enumerable and configurable need configurable=true *\) *)
(*             | Data (d, _, true), S.Enum, new_enum -> *)
(*               Data (d, unbool new_enum, true) *)
(*             | Data (d, enum, true), S.Config, new_config -> *)
(*               Data (d, enum, unbool new_config) *)
(*             | Data (d, enum, false), S.Config, False ->  *)
(*               Data (d, enum, false) *)
(*             | Accessor (a, enum, true), S.Config, new_config -> *)
(*               Accessor (a, enum, unbool new_config) *)
(*             | Accessor (a, enum, true), S.Enum, new_enum -> *)
(*               Accessor (a, unbool new_enum, true) *)
(*             | Accessor (a, enum, false), S.Config, False -> *)
(*               Accessor (a, enum, false) *)
(*             | _ -> failwith "[interp] bad property set" *)
(*         in begin *)
(*             c := (attrsv, IdMap.add f_str newprop props); *)
(*             true *)
(*         end *)
(*   end *)
(*   | _ -> failwith ("[interp] set-attr didn't get an object and a string") *)

(* (\* 8.10.5, steps 7/8 "If iscallable(getter) is false and getter is not *)
(*    undefined..." *\) *)

(* and fun_obj value = match value with *)
(*   | ObjCell c -> begin match !c with *)
(*       | { code = Some (Closure cv) }, _ -> true *)
(*       | _ -> false *)
(*   end *)
(*   | Undefined -> false *)
(*   | _ -> false *)
    

let rec eval jsonPath maxDepth depth exp env (pc : ctx) : result list * exresult list = 
  (* printf "In eval %s %d %d %s\n" jsonPath maxDepth depth *)
  (*   (Ljs_pretty.exp exp Format.str_formatter; Format.flush_str_formatter()); *)
  if (depth >= maxDepth) then none
  else 
    let nestedEval = eval jsonPath maxDepth in
    let eval = eval jsonPath maxDepth depth in match exp with
      | S.Hint (_, _, e) -> eval e env pc
      | S.Undefined _ -> return Undefined pc 
      | S.Null _ -> return Null pc 
      | S.String (_, s) -> return (String s) pc
      | S.Num (_, n) -> return (Num n) pc
      | S.True _ -> return True pc
      | S.False _ -> return False pc
      | S.Id (p, x) -> 
        if (String.length x > 2 && String.sub x 0 2 = "%%") then 
          return (Sym x) (add_var x TAny pc)
        else begin
          try
            match IdMap.find x env with
            | VarCell v -> return !v pc
            | _ -> failwith ("[interp] (EId) xpected a VarCell for variable " ^ x ^ 
                                " at " ^ (string_of_position p) ^ 
                                ", but found something else: " ^ Ljs_sym_pretty.to_string (IdMap.find x env))
          with Not_found ->
            failwith ("[interp] Unbound identifier: " ^ x ^ " in identifier lookup at " ^
                         (string_of_position p))
        end

      | S.Lambda (p, xs, e) -> 
        let set_arg arg x m = IdMap.add x (VarCell (ref arg)) m in
        return (Closure (fun args pc' depth -> 
          if (List.length args) != (List.length xs) then
            arity_mismatch_err p xs args
          else
            nestedEval (depth+1) e (List.fold_right2 set_arg args xs env) pc'))
          pc

      | S.Op1 (p, op, e) ->
        bind 
          (eval e env pc)
          (fun (e_val, pc') -> 
            let (t,ret_ty) = typeofOp1 op in 
            try 
              match e_val with
              | Sym id -> 
                let pc'' = check_type id t pc' in
                let (ret_op1, pc''') = fresh_var ("P1_" ^ op ^ "_") ret_ty pc'' in
                return (Sym ret_op1)
                  (add_constraint (SLet (ret_op1, SOp1 (op, SId id))) pc''')
              | _ -> 
                try
                  return (op1 op e_val) pc'
                with PrimError msg -> throw (Throw (String msg)) pc'
            with TypeError _ -> none)
          
      | S.Op2 (p, op, e1, e2) -> 
        bind
          (eval e1 env pc)
          (fun (e1_val, pc') ->
            bind 
              (eval e2 env pc')
              (fun (e2_val, pc'') -> 
                let (t1, t2, ret_ty) = typeofOp2 op in
                match e1_val, e2_val with
                | Sym _, Sym _
                | Sym _, _
                | _, Sym _ -> begin 
                  try 
                    let (sym_e1, pc1) = match e1_val with
                      | Sym id -> (SId id, check_type id t1 pc'')
                      | _ -> (Concrete e1_val, pc'') in
                    let (sym_e2, pc2) = match e2_val with
                      | Sym id -> (SId id, check_type id t2 pc1)
                      | _ -> (Concrete e2_val, pc1) in
                    let (ret_op, pc3) = fresh_var ("P2_" ^ op ^ "_") ret_ty pc2 in
                    return (Sym ret_op)
                      (add_constraint (SLet (ret_op, SOp2(op, sym_e1, sym_e2))) pc3)
                  with TypeError id -> Printf.printf "Check_type couldn't find %s" id; none 
                end
                | _ ->
                  try
                    return (op2 op e1_val e2_val) pc''
                  with PrimError msg -> throw (Throw (String msg)) pc''))
          
      | S.If (p, c, t, f) ->
        bind 
          (eval c env pc)
          (fun (c_val, pc') -> 
            match c_val with
            | True -> eval t env pc'
            | Sym id -> 
              let true_pc = add_constraint (SAssert (SCastJS (TBool, SId id))) pc' in
              let false_pc  = add_constraint (SAssert (SNot (SCastJS (TBool, SId id)))) pc' in
              (fun (r1, e1) (r2, e2) -> (List.rev_append r1 r2, List.rev_append e1 e2))
                (if is_sat true_pc then (eval t env true_pc)
                 else none)
                (if is_sat false_pc then (eval f env false_pc)
                 else none)
            | _ -> eval f env pc')
          
      | S.App (p, f, args) -> 
        bind 
          (eval f env pc)
          (fun (f_val, pc_f) ->
            let args_pcs : (value list * ctx) list * (exval * ctx) list =
              List.fold_left 
                (fun avpcs arg ->
                  bind avpcs
                    (fun ((argvs : value list), (pcs : ctx)) -> 
                      bind 
                        (eval arg env pcs)
                        (fun (argv, pcs') ->
                          return (argvs @ [argv]) pcs')))
                ([([], pc_f)], []) args in
            bind args_pcs
              (fun (argvs, pcs) ->
                match f_val with
                | Sym f -> 
                  let ((fid : string), (fpc : ctx)) = fresh_var "F" (TFun (List.length argvs)) pcs in
                  let (argvs : sym_exp list) = List.map val_sym argvs in
                  let ((vs : sym_exp list), (pcs' : ctx)) = List.fold_left
                    (fun (vals, p) exp -> (vals@[exp], p))
                    ([], fpc) argvs in
                  let (res_id, res_pc) = fresh_var "AP" TAny pcs' in 
                  return (Sym res_id)
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
            eval body (IdMap.add x (VarCell (ref e_val)) env) pc')
          
      | S.Rec (p, x, e, body) ->
        let x' = ref Undefined in
        bind 
          (eval e (IdMap.add x (VarCell x') env) pc)
          (fun (ev_val, pc') -> 
            x' := ev_val;
            eval body (IdMap.add x (VarCell (ref ev_val)) env) pc')

      | S.SetBang (p, x, e) -> begin
        try
          match IdMap.find x env with
          | VarCell v -> 
            bind 
              (eval e env pc)
              (fun (e_val, pc') ->
                v := e_val; return e_val pc')
          | _ -> failwith ("[interp] (ESet) xpected a VarCell for variable " ^ x ^ 
                              " at " ^ (string_of_position p) ^ 
                              ", but found something else.")
        with Not_found ->
          failwith ("[interp] Unbound identifier: " ^ x ^ " in set! at " ^
                       (string_of_position p))
      end

      | S.Object (p, attrs, props) -> begin 
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
                | Some pexp -> eval pexp env pc_v)
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
                              return (Data ({ value = v2; writable = w; }, enum, config)) pc_v2)
                        | S.Accessor ({ S.getter = ge; S.setter = se; }, enum, config) ->
                          bind (eval ge env pc)
                            (fun (v2, pc_v2) ->
                              bind (eval se env pc_v2)
                                (fun (v3, pc_v3) ->
                                  return (Accessor ({ getter = v2; setter = v3}, enum, config)) pc_v3))
                      in
                      let propvs_pcs  = 
                        List.fold_left
                          (fun maps_pcs (name, prop) -> 
                            bind maps_pcs
                              (fun (map, pc) ->
                                bind 
                                  (eval_prop prop pc)
                                  (fun (propv, pc_v) -> 
                                    return (IdMap.add name propv map) pc_v)))
                          ([(IdMap.empty, pc_c)], []) props in
                      bind propvs_pcs
                        (fun (propvs, pc_psv) -> 
                          return (ObjCell (ref (attrsv, propvs))) pc_psv))))
      end
        
      | S.GetAttr (p, attr, obj, field) ->
        let rec sym_get_attr attr obj field pc = 
          try
            match (obj, field) with
            | ObjCell _, String _ -> return (get_attr attr obj field) pc
            | Sym o_id, String f ->
              let (fn_id, pc') = fresh_var ("FN_" ^ f) TString pc in
              (* todo: assert that (SId fn_id) = (Concrete f) *)
              sym_get_attr attr obj (Sym fn_id) pc'
            | ObjCell c, Sym f_id ->
              let (_, props) = !c in
              combine
                (IdMap.fold (fun fieldName _ results ->
                  let (fn_id, pc') = fresh_var ("FN_" ^ fieldName ^ "_") TString pc in
                  let pc'' = add_constraint
                    (SAssert (SApp(SId "=",
                                   [SId f_id; SId fn_id]))) pc' in
                  let (ret_gf, pc''') = fresh_var "GF_" TAny pc'' in
                  also_return (Sym ret_gf)
                    (add_constraint (SLet (ret_gf, Concrete (get_attr attr obj (String fieldName)))) pc''') results)
                   props none)
                (let none_of = IdMap.fold
                   (fun fieldName _ pc ->
                     let (fn_id, pc) = fresh_var ("FN_" ^ fieldName ^ "_") TString pc in
                     add_constraint
                       (SAssert (SNot (SApp (SId "=", [SCastJS (TString, SId f_id);
                                                       SCastJS (TString, SId fn_id)])))) pc)
                   props pc in
                 let (ret_gf, pc''') = fresh_var "GF_" TAny none_of in
                 return (Sym ret_gf)
                   (add_constraint (SLet (ret_gf, Concrete undef)) pc'''))
            | Sym o_id, Sym f_id ->
              let pc_types = check_type o_id TObj (check_type f_id TString pc) in
              let (fn_id, pc') = fresh_var ("FN_" ^ f_id ^ "_") TString pc_types in
              let (ret_gf, pc'') = fresh_var "GF_" TAny pc' in
              let field = SGetField (o_id, f_id) in
              let missing = (return (Sym ret_gf) 
                               (add_constraints [(SAssert (SIsMissing field));
                                                 (SLet (ret_gf, (Concrete undef)))] pc'')) in
              let pc_present = (add_constraints [(SAssert (SNot (SIsMissing field)));
                                                 (SLet (fn_id, field))] pc'') in
              (match attr with
              | S.Value -> 
                let pc_present = check_type fn_id TData pc_present in
                let pc' = add_constraint (SLet (ret_gf, SApp(SId "value", [SId fn_id]))) pc_present in
                also_return (Sym ret_gf) pc' missing
              | S.Writable ->
                let pc_present = check_type fn_id TData pc_present in
                let pc' = add_constraint (SLet (ret_gf, SApp(SId "writable", [SId fn_id]))) pc_present in
                also_return (Sym ret_gf) (add_constraint (SAssert (SId ret_gf)) pc')
                  (also_return (Sym ret_gf) (add_constraint (SAssert (SNot (SId ret_gf))) pc')
                     missing)
              | S.Enum ->
                let pc' = add_constraint (SLet (ret_gf, SApp(SId "enumerable", [SId fn_id]))) pc_present in
                also_return (Sym ret_gf) (add_constraint (SAssert (SId ret_gf)) pc')
                  (also_return (Sym ret_gf) (add_constraint (SAssert (SNot (SId ret_gf))) pc')
                     missing)
              | S.Config ->
                let pc' = add_constraint (SLet (ret_gf, SApp(SId "config", [SId fn_id]))) pc_present in
                also_return (Sym ret_gf) (add_constraint (SAssert (SId ret_gf)) pc')
                  (also_return (Sym ret_gf) (add_constraint (SAssert (SNot (SId ret_gf))) pc')
                     missing)
              | S.Getter ->
                let pc_present = check_type fn_id TAccessor pc_present in
                let pc' = add_constraint (SLet (ret_gf, SApp(SId "getter", [SId fn_id]))) pc_present in
                also_return (Sym ret_gf) pc' missing
              | S.Setter ->
                let pc_present = check_type fn_id TAccessor pc_present in
                let pc' = add_constraint (SLet (ret_gf, SApp(SId "setter", [SId fn_id]))) pc_present in
                also_return (Sym ret_gf) pc' missing)
            | _ -> failwith ("[interp] GetAttr got a non-object or a non-string field name: (get-attr "
                             ^ Ljs_sym_pretty.to_string obj ^ " "
                             ^  Ljs_sym_pretty.to_string field ^ ")")
          with TypeError _ -> none
        in
        bind (eval obj env pc)
          (fun (obj_val, pc_obj) ->
            bind (eval field env pc_obj)
              (fun (f_val, pc_f) -> sym_get_attr attr obj_val f_val pc_f))

      | S.GetField (p, obj, f, args) ->
        let rec sym_get_field p obj1 field getter_params result pc depth = 
          try
            match obj1, field with
            | Null, _ -> return Undefined pc (* nothing found *)
            | Sym id, String f -> begin
              let (fn_id, pc') = fresh_var ("FN_" ^ f) TString pc in
                          (* todo: assert that (SId fn_id) = (Concrete f) *)
              sym_get_field p obj1 (Sym fn_id) getter_params result pc' depth
            end
            | Sym o_id, Sym f_id ->
              let pc_types = check_type o_id TObj (check_type f_id TString pc) in
              let (ret_gf, pc'') = fresh_var "GF_" TAny pc_types in
              let true_pc =
                add_constraints [(SAssert (SNot (SIsMissing (SGetField (o_id, f_id)))));
                                 (SLet (ret_gf, SGetField (o_id, f_id)))] pc'' in
              let false_pc =
                add_constraints [(SAssert (SIsMissing (SGetField (o_id, f_id))));
                                 (SLet (ret_gf, SOp2 ("get_field", SId o_id, SId f_id)))] pc''
              in
              also_return (Sym ret_gf) true_pc
                (return (Sym ret_gf)  false_pc)
            | ObjCell c, Sym f -> begin
              let ({proto = pvalue; }, props) = !c in
              combine
                (IdMap.fold (fun fieldName value results ->
                  let (fn_id, pc') = fresh_var ("FN_" ^ fieldName ^ "_") TString pc in
                  let pc'' = add_constraint
                    (SAssert (SApp(SId "=",
                                   [SId f; SId fn_id]))) pc' in
                  let (ret_gf, pc''') = fresh_var "GF_" TAny pc'' in
                  match value with
                  | Data ({ value = v; }, _, _) ->
                    also_return (Sym ret_gf)
                      (add_constraint (SLet (ret_gf, Concrete (result v))) pc''') results
                  | Accessor ({ getter = g; }, _, _) ->
                    combine (apply p g getter_params pc''' depth) results) props none)
                (let none_of = IdMap.fold
                   (fun fieldName _ pc ->
                     let (fn_id, pc) = fresh_var ("FN_" ^ fieldName ^ "_") TString pc in
                     add_constraint
                       (SAssert (SNot (SApp (SId "=", [SCastJS (TString, SId f); 
                                                       SCastJS (TString, SId fn_id)])))) pc)
                   props pc in
                 sym_get_field p pvalue field getter_params result none_of depth)
            end
            | ObjCell c, String f ->
              get_field p obj1 f getter_params (fun x -> x) pc depth
            | _ -> failwith (interp_error p
                               "get_field on a non-object.  The expression was (get-field "
                             ^ Ljs_sym_pretty.to_string obj1
                             ^ " " ^ Ljs_sym_pretty.to_string (List.nth getter_params 0)
                             ^ " " ^ Ljs_sym_pretty.to_string field ^ ")")
          with TypeError _ -> none
        in
        bind (eval obj env pc)
          (fun (objv, pc_o) -> 
            bind (eval f env pc_o) 
              (fun (fv, pc_f) -> 
                bind (eval args env pc_f)
                  (fun (argsv, pc') ->
                    sym_get_field p objv fv [objv; argsv] (fun x -> x) pc' depth)))
          
      (*
        | S.SetField (p, obj, f, v, args) ->
        let obj_value = eval obj env in
        let f_value = eval f env in
        let v_value = eval v env in
        let args_value = eval args env in begin
        match (obj_value, f_value) with
        | (ObjCell o, String s) ->
        update_field p obj_value
        obj_value 
        s
        v_value
        [obj_value; args_value]
        (fun x -> x)
        | _ -> failwith ("[interp] Update field didn't get an object and a string" 
        ^ string_of_position p ^ " : " ^ (Ljs_sym_pretty.to_string obj_value) ^ 
        ", " ^ (Ljs_sym_pretty.to_string f_value))
        end
      *)
      (*
        | S.DeleteField (p, obj, f) ->
        let obj_val = eval obj env in
        let f_val = eval f env in begin
        match (obj_val, f_val) with
        | (ObjCell c, String s) -> 
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
      (* | S.SetAttr (p, attr, obj, field, newval) ->
        let obj_val = eval obj env in
        let f_val = eval field env in
        let v_val = eval newval env in
        bool (set_attr attr obj_val f_val v_val) *)


          
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
      | S.SetField _ -> failwith "[interp] not yet implemented (SetField)"
      | S.SetAttr _ -> failwith "[interp] not yet implemented (SetAttr)"
      | S.Eval _ -> failwith "[interp] not yet implemented (Eval)"



and arity_mismatch_err p xs args = failwith ("Arity mismatch, supplied " ^ string_of_int (List.length args) ^ " arguments and expected " ^ string_of_int (List.length xs) ^ " at " ^ string_of_position p ^ ". Arg names were: " ^ (List.fold_right (^) (map (fun s -> " " ^ s ^ " ") xs) "") ^ ". Values were: " ^ (List.fold_right (^) (map (fun v -> " " ^ Ljs_sym_pretty.to_string v ^ " ") args) ""))

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
        | ObjCell c ->
          let (attrs, props) = !c in
          begin try
                  match IdMap.find "message" props with
                  | Data ({ value = msg_val; }, _, _) ->
                    (Ljs_sym_pretty.to_string msg_val)
                  | _ -> (Ljs_sym_pretty.to_string v)
            with Not_found -> (Ljs_sym_pretty.to_string v)
          end
        | v -> (Ljs_sym_pretty.to_string v) in
      throw (str ("Uncaught exception: " ^ err_msg)) pc
    | Break (l, v) -> throw (str ("Broke to top of execution, missed label: " ^ l)) pc)
