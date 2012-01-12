open Prelude
module C = Es5_cps
module D = Es5_cps_delta
module A = Es5_cps_absdelta
module E = Es5_syntax
module V = Es5_cps_values
module U = Es5_cps_util
open Graph
open Format
open FormatExt

type vert = C.cps_exp
module Vert_COMPARABLE = struct
  type t = vert
  let compare t1 t2 = Pervasives.compare t1 t2
  let hash t = Hashtbl.hash t
  let equal t1 t2 = (t1 = t2)
end

module Es5_ORDERED_TYPE_DFT = struct
  type t = Jump | IfTrue | IfFalse | Prim (* get/set field?? *)
  let default = Prim
  let compare t1 t2 = Pervasives.compare t1 t2
end

module G = Persistent.Digraph.ConcreteBidirectionalLabeled (Vert_COMPARABLE) (Es5_ORDERED_TYPE_DFT)

type complete = Ans of V.bind_value | Err of V.bind_value
module AddrSet = Set.Make (Es5_cps_values.ADDRESS)



let eval (exp : C.cps_exp) =
  let newLabel = C.Label.newLabel in
  let bool b pos = if b then V.True(pos, newLabel()) else V.False(pos, newLabel()) in
  let unbool v = match v with
    | V.True _ -> true
    | V.False _ -> false
    | _ -> failwith "tried to unbool a non-bool" in

  (* 
   * Garbage collection of the stores, assuming that the provided environments are all the 
   * roots that exist.  Similarly, assume that the closed-over environments in closures and
   * continuations are themselves gc'ed, so that they only contain reachable information and
   * no garbage.
   *)
  let garbage_collect
      bindingEnv (bindingStore : V.bind_value Es5_cps_values.Store.t)
      retContEnv retContStore
      exnContEnv exnContStore =
    (* (U.dump_heap_as_dot "before_" bindingEnv bindingStore retContEnv retContStore exnContEnv exnContStore) Format.str_formatter; *)
    (* print_string (Format.flush_str_formatter ()); *)
    let noIds = AddrSet.empty in
    let just addr = AddrSet.singleton addr in
    let add addr = AddrSet.add addr in
    let (++) l1 l2 = AddrSet.union l1 l2 in
    let join (b1, r1, e1) (b2, r2, e2) = (b1++b2, r1++r2, e1++e2) in
    let lookup addr store = try Some (Es5_cps_values.Store.find addr store) with _ -> None in
    let rec reachable_retContEnv_addrs (retContEnv : V.retContEnv) =
      IdMap.fold (fun _ rAddr (b, r, e) ->
        match (lookup rAddr retContStore) with
        | None
        | Some V.Answer -> (b, add rAddr r, e)
        | Some (V.RetCont (_, _, _, bindingEnv, retContEnv, exnContEnv)) -> join
          (join (reachable_bindingEnv_addrs bindingEnv)
             (join (reachable_retContEnv_addrs retContEnv)
                (reachable_exnContEnv_addrs exnContEnv)))
          (b, add rAddr r, e)) retContEnv (noIds, noIds, noIds)
    and reachable_exnContEnv_addrs (exnContEnv : V.exnContEnv) =
      IdMap.fold (fun _ eAddr (b, r, e) ->
        match (lookup eAddr exnContStore) with
        | None
        | Some V.Error -> (b, r, add eAddr e)
        | Some (V.ExnCont (_, _, _, _, bindingEnv, retContEnv, exnContEnv)) -> join
          (join (reachable_bindingEnv_addrs bindingEnv)
             (join (reachable_retContEnv_addrs retContEnv)
                (reachable_exnContEnv_addrs exnContEnv)))
          (b, r, add eAddr e)) exnContEnv (noIds, noIds, noIds)
    and reachable_bindingEnv_addrs (bindingEnv : V.bindingEnv) =
      let rec reachable_binding v =
        match v with
        | V.VarCell (_, _, ptr) -> 
          begin match (lookup ptr bindingStore) with
          | None -> (just ptr, noIds, noIds)
          | Some v -> join (just ptr, noIds, noIds) (reachable_binding v)
          end
        | V.Object (_, _, attrs, props) ->
          let prim = match attrs.V.primval with 
            | None -> (noIds, noIds, noIds)
            | Some v -> reachable_binding v in
          let code = match attrs.V.code with
            | None -> (noIds, noIds, noIds)
            | Some v -> reachable_binding v in
          let proto = match attrs.V.proto with
            | None -> (noIds, noIds, noIds)
            | Some v -> reachable_binding v in
          let prop a = match a with
            | (_, V.Data ({V.value = v}, _, _)) -> reachable_binding v
            | (_, V.Accessor ({V.getter = g; V.setter = s}, _, _)) -> 
              join (reachable_binding g) (reachable_binding s) in
          List.fold_left (fun acc p -> join (prop p) acc) (join prim (join code proto)) props
        | V.Closure(_, _, _, _, _, _, bindingEnv', retContEnv', exnContEnv') ->
          let newBinds = if (bindingEnv == bindingEnv') then (noIds, noIds, noIds) else (reachable_bindingEnv_addrs bindingEnv') in
          let newRets = if (retContEnv == retContEnv') then (noIds, noIds, noIds) else (reachable_retContEnv_addrs retContEnv') in
          let newExns = if (exnContEnv == exnContEnv') then (noIds, noIds, noIds) else (reachable_exnContEnv_addrs exnContEnv') in
          join newBinds (join newRets newExns)
        | _ -> (noIds, noIds, noIds) in
      IdMap.fold (fun _ bAddr (b, r, e) -> 
        match (lookup bAddr bindingStore) with
        | None -> (add bAddr b, r, e)
        | Some v -> join (add bAddr b, r, e) (reachable_binding v)) bindingEnv (noIds, noIds, noIds) in 
    let (reachable_bind_addrs, reachable_ret_addrs, reachable_exn_addrs) =
      join (reachable_bindingEnv_addrs bindingEnv)
        (join (reachable_retContEnv_addrs retContEnv)
           (reachable_exnContEnv_addrs exnContEnv)) in
    (* monomorphism restriction at module level means I can't encapsulate the call to Store.fold... *)
    let filter_sto stoName pretty addrs = (fun addr value acc -> 
      if (AddrSet.mem addr addrs)
      then acc
      else 
        (
          (* print_string ("discarding " ^ (string_of_int addr) ^ "->" ^ (pretty value) ^ " from store " ^ stoName ^ "\n"); *)
          Es5_cps_values.Store.remove addr acc)
    ) in
    let (newBindings, newRets, newExns) =
      (Es5_cps_values.Store.fold (filter_sto "bindings" V.pretty_bind reachable_bind_addrs) 
         bindingStore bindingStore,
       Es5_cps_values.Store.fold (filter_sto "retconts" V.pretty_retcont reachable_ret_addrs) 
         retContStore retContStore,
       Es5_cps_values.Store.fold (filter_sto "exnconts" V.pretty_exncont reachable_exn_addrs) 
         exnContStore exnContStore) in
    (* (U.dump_heap_as_dot "after_" bindingEnv newBindings retContEnv newRets exnContEnv newExns) Format.str_formatter; *)
    (newBindings, newRets, newExns) in

  let eval_ret ret bindingEnv retContEnv exnContEnv retContStore = match ret with
    | C.RetId(_, id) -> Es5_cps_values.Store.find (IdMap.find id retContEnv) retContStore
    | C.RetLam(label, arg, body) -> V.RetCont(label, arg, body, bindingEnv, retContEnv, exnContEnv) in
  let eval_exn exn bindingEnv retContEnv exnContEnv exnContStore = match exn with
    | C.ExnId(_, id) -> Es5_cps_values.Store.find (IdMap.find id exnContEnv) exnContStore
    | C.ExnLam(label, arg, lbl, body) -> V.ExnCont(label, arg, lbl, body, bindingEnv, retContEnv, exnContEnv) in
  let rec eval_exp exp 
      bindingEnv retContEnv exnContEnv 
      (bindingStore : V.bind_value Es5_cps_values.Store.t) retContStore exnContStore = 
    (* print_string "In eval_exp for "; *)
    (* (match exp with *)
    (* | C.LetValue (_, l, id, _, _) -> printf "%s" ("LetValue " ^ (string_of_int l) ^ "," ^ id ^ "\n") *)
    (* | C.RecValue (_, l, id, _, _) -> printf "%s" ("RecValue " ^ (string_of_int l) ^ "," ^ id ^ "\n") *)
    (* | C.LetPrim (_, l, id, _, _) -> printf "%s" ("LetPrim " ^ (string_of_int l) ^ "," ^ id ^ "\n") *)
    (* | C.LetRetCont (l, id, _, _, _) -> printf "%s" ("LetRetCont " ^ (string_of_int l) ^ "," ^ id ^ "\n") *)
    (* | C.LetExnCont (l, id, _, _, _, _) -> printf "%s" ("LetExnCont " ^ (string_of_int l) ^ "," ^ id ^ "\n") *)
    (* | C.AppRetCont (l, id, _) -> printf "%s" ("AppRetCont " ^ (string_of_int l) ^ "," ^ id ^ "\n") *)
    (* | C.AppExnCont (l, id, _, _) -> printf "%s" ("AppExnCont " ^ (string_of_int l) ^ "," ^ id ^ "\n") *)
    (* | C.AppFun (_, l, f, r, e, a) -> printf "%s %s(Ret %s, Exn %s; %s)\n" ("AppFun " ^ (string_of_int l)) *)
    (*   (Es5_cps_pretty.cps_value_to_string f) r e (String.concat ", " (List.map Es5_cps_pretty.cps_value_to_string a)) *)
    (* | C.If(_, l, _, _, _) -> printf "%s" ("If " ^ (string_of_int l) ^ "\n") *)
    (* | C.Eval(_, l, _) -> printf "%s" ("Eval " ^ (string_of_int l) ^ "\n") *)
    (* ); *)
    (* U.print_bindings bindingEnv bindingStore; *)
    match exp with
    | C.LetValue(pos, label, id, value, body) ->
      let (value, bindingStore, retContStore, exnContStore) = 
        eval_val value bindingEnv bindingStore retContEnv retContStore exnContEnv exnContStore in
      let addr = V.ADDRESS.newAddr() in
      eval_exp body 
        (IdMap.add id addr bindingEnv) retContEnv exnContEnv 
        (Es5_cps_values.Store.add addr value bindingStore) retContStore exnContStore
    | C.RecValue(pos, label, id, value, body) ->
      let addr = V.ADDRESS.newAddr() in
      let bindingEnv' = IdMap.add id addr bindingEnv in
      let (value', bindingStore, retContStore, exnContStore) = 
        eval_val value bindingEnv' (Es5_cps_values.Store.add addr (V.Undefined(dummy_pos, newLabel())) bindingStore)
          retContEnv retContStore exnContEnv exnContStore in
      eval_exp body 
        bindingEnv' retContEnv exnContEnv 
        (Es5_cps_values.Store.add addr value' bindingStore) retContStore exnContStore
    | C.LetPrim(pos, label, id, prim, body) ->
      let (value, bindingStore', retContStore, exnContStore) = eval_prim prim bindingEnv bindingStore retContEnv retContStore exnContEnv exnContStore in
      let addr = V.ADDRESS.newAddr() in
      eval_exp body 
        (IdMap.add id addr bindingEnv) retContEnv exnContEnv 
        (Es5_cps_values.Store.add addr value bindingStore') retContStore exnContStore
    | C.LetRetCont(label, id, r, exp) ->
      (* let (bindingStore, retContStore, exnContStore) = *)
      (*   garbage_collect bindingEnv bindingStore retContEnv retContStore exnContEnv exnContStore in *)
      let ret = eval_ret r bindingEnv retContEnv exnContEnv retContStore in
      let addr = V.ADDRESS.newAddr() in
      let retEnv' = (IdMap.add id addr retContEnv) in
      let retStore' = (Es5_cps_values.Store.add addr ret retContStore) in
      (* print_rets retEnv' retStore'; *)
      eval_exp exp
        bindingEnv retEnv' exnContEnv
        bindingStore retStore' exnContStore
    | C.AppRetCont(label, r, value) ->
      (* print_rets retContEnv retContStore; *)
      let (value', bindingStore, retContStore, exnContStore) = 
        eval_val value bindingEnv bindingStore retContEnv retContStore exnContEnv exnContStore in
      let ret = eval_ret r bindingEnv retContEnv exnContEnv retContStore in
      begin match ret with
      | V.Answer -> 
        (match value' with
        | V.VarCell (_, _, a) -> 
          (Ans (Es5_cps_values.Store.find a bindingStore), bindingStore, retContStore, exnContStore)
        | _ ->
          (Ans value', bindingStore, retContStore, exnContStore))
      | V.RetCont (_, arg, body, bindingEnv, retContEnv, exnContEnv) ->
        let addr = V.ADDRESS.newAddr() in
        eval_exp body
          (IdMap.add arg addr bindingEnv) retContEnv exnContEnv
          (Es5_cps_values.Store.add addr value' bindingStore) retContStore exnContStore
      end
    | C.LetExnCont(label, id, e, exp) ->
      (* let (bindingStore, retContStore, exnContStore) = *)
      (*   garbage_collect bindingEnv bindingStore retContEnv retContStore exnContEnv exnContStore in *)
      let exn = eval_exn e bindingEnv retContEnv exnContEnv exnContStore in
      let addr = V.ADDRESS.newAddr() in
      let exnEnv' = (IdMap.add id addr exnContEnv) in
      let exnStore' = (Es5_cps_values.Store.add addr exn exnContStore) in
      (* print_exns exnEnv' exnStore'; *)
      eval_exp exp
        bindingEnv retContEnv exnEnv'
        bindingStore retContStore exnStore'
    | C.AppExnCont(label, e, arg, lbl) ->
      (* print_exns exnContEnv exnContStore; *)
      let (arg', bindingStore, retContStore, exnContStore) = 
        eval_val arg bindingEnv bindingStore retContEnv retContStore exnContEnv exnContStore in
      let (lbl', bindingStore, retContStore, exnContStore) = 
        eval_val lbl bindingEnv bindingStore retContEnv retContStore exnContEnv exnContStore in
      let exn = eval_exn e bindingEnv retContEnv exnContEnv exnContStore in
      begin match exn with
      | V.Error -> 
        (match arg' with
        | V.VarCell (_, _, a) -> 
          (Err (Es5_cps_values.Store.find a bindingStore), bindingStore, retContStore, exnContStore)
        | _ ->
          (Err arg', bindingStore, retContStore, exnContStore))
      | V.ExnCont(_, arg, lbl, body, bindingEnv, retContEnv, exnContEnv) ->
        let argAddr = V.ADDRESS.newAddr() in
        let lblAddr = V.ADDRESS.newAddr() in
        eval_exp body
          (IdMap.add arg argAddr (IdMap.add lbl lblAddr bindingEnv)) retContEnv exnContEnv
          (Es5_cps_values.Store.add argAddr arg' (Es5_cps_values.Store.add lblAddr lbl' bindingStore)) retContStore exnContStore
      end
    | C.If(pos, label, cond, left, right) ->
      let (cond', bindingStore, retContStore, exnContStore) = 
        eval_val cond bindingEnv bindingStore retContEnv retContStore exnContEnv exnContStore in
      if unbool cond' 
      then eval_exp left bindingEnv retContEnv exnContEnv bindingStore retContStore exnContStore
      else eval_exp right bindingEnv retContEnv exnContEnv bindingStore retContStore exnContStore
    | C.AppFun(pos, label, func, ret, exn, args) ->
      (* let (bindingStore, retContStore, exnContStore) = *)
      (*   garbage_collect bindingEnv bindingStore retContEnv retContStore exnContEnv exnContStore in *)
      let (func', bindingStore, retContStore, exnContStore) = 
        eval_val func bindingEnv bindingStore retContEnv retContStore exnContEnv exnContStore in
      let (args', bindingStore, retContStore, exnContStore) = List.fold_left (fun (args, bindingStore, retContStore, exnContStore) arg -> 
        let (arg', bs, rs, es) = 
          eval_val arg bindingEnv bindingStore retContEnv retContStore exnContEnv exnContStore in
        arg'::args, bs, rs, es) ([],bindingStore, retContStore, exnContStore) args in
      let args' = List.rev args' in
      let ret' = eval_ret ret bindingEnv retContEnv exnContEnv retContStore in
      let exn' = eval_exn exn bindingEnv retContEnv exnContEnv exnContStore in
      let getLambda fobj = match fobj with
        | V.Closure (_, _, retArg, exnArg, argNames, body, bindingEnv,retContEnv,exnContEnv)
        | V.Object(_, _, {V.code = Some (V.Closure (_, _, retArg, exnArg, argNames, body, bindingEnv,retContEnv,exnContEnv))}, _) -> 
          (retArg, exnArg, argNames, body, bindingEnv, retContEnv, exnContEnv)
        | _ -> failwith "[cps-interp] applying a non-function" in
      let (retArg, exnArg, argNames, body, cBindingEnv, cRetEnv, cExnEnv) = getLambda func' in
      let retAddr = V.ADDRESS.newAddr() in
      let exnAddr = V.ADDRESS.newAddr() in
      let argAddrs = List.map (fun _ -> V.ADDRESS.newAddr()) argNames in
      let bindingEnv' = List.fold_left (fun env (name, addr) -> IdMap.add name addr env)
        cBindingEnv (List.combine argNames argAddrs) in (* NEED THE CLOSURE ENVIRONMENTS *)
      let bindingStore' = List.fold_left (fun store (addr, value) -> Es5_cps_values.Store.add addr value store)
        bindingStore (List.combine argAddrs args') in
      eval_exp body
        bindingEnv' (IdMap.add retArg retAddr cRetEnv) (IdMap.add exnArg exnAddr cExnEnv)
        bindingStore' (Es5_cps_values.Store.add retAddr ret' retContStore) (Es5_cps_values.Store.add exnAddr exn' exnContStore)
    | C.Eval _ ->
      (Err (V.Undefined(dummy_pos, newLabel())), bindingStore, retContStore, exnContStore)
  and eval_val (value : C.cps_value) env bindingStore retEnv retStore exnEnv exnStore : (V.bind_value * Es5_cps_values.bindingStore * Es5_cps_values.retContStore * Es5_cps_values.exnContStore) = match value with
    | C.Id(_, _, id) -> ((Es5_cps_values.Store.find (IdMap.find id env) bindingStore), bindingStore, retStore, exnStore)
    | C.Null(p,l) -> (V.Null(p,l), bindingStore, retStore, exnStore)
    | C.Undefined(p,l) -> (V.Undefined(p,l), bindingStore, retStore, exnStore)
    | C.String(p,l,s) -> (V.String(p,l,s), bindingStore, retStore, exnStore)
    | C.Num(p,l,n) -> (V.Num(p,l,n), bindingStore, retStore, exnStore)
    | C.True(p,l) -> (V.True(p,l), bindingStore, retStore, exnStore)
    | C.False(p,l) -> (V.False(p,l), bindingStore, retStore, exnStore)
    | C.Object(p,l,a,ps) -> 
      let (bindingStore, retStore, exnStore) =
        garbage_collect env bindingStore retEnv retStore exnEnv exnStore in
      let opt_val v bindingStore = match v with 
        | None -> (None, bindingStore, retStore, exnStore)
        | Some v -> let (ans,bs,rs,es) = 
                      eval_val v env bindingStore retEnv retStore exnEnv exnStore in (Some ans, bs,rs,es) in
      let (primval, bindingStore,retStore,exnStore) = opt_val a.C.primval bindingStore in
      let (code, bindingStore,retStore,exnStore) = opt_val a.C.code bindingStore in
      let (proto, bindingStore,retStore,exnStore) = opt_val a.C.proto bindingStore in
      let a' = { V.primval = primval; V.code = code; V.proto = proto; 
                 V.klass = a.C.klass; V.extensible = a.C.extensible } in
      let prop (props, bindingStore,retStore,exnStore) (str, p) = (match p with
        | C.Data({C.value = v; C.writable = w}, enum, config) ->
          let v = (Es5_cps_values.Store.find (IdMap.find v env) bindingStore) in
          (str, V.Data({V.value = v; V.writable = w}, enum, config))::props, bindingStore,retStore,exnStore
        | C.Accessor({C.getter = g; C.setter = s}, enum, config) -> 
          let g = (Es5_cps_values.Store.find (IdMap.find g env) bindingStore) in
          let s = (Es5_cps_values.Store.find (IdMap.find s env) bindingStore) in
          (str, V.Accessor({V.getter = g; V.setter = s}, enum, config))::props, bindingStore,retStore,exnStore) in
      let (ps', bindingStore,retStore,exnStore) = List.fold_left prop ([], bindingStore,retStore,exnStore) ps in
      let ps' = List.rev ps' in
      let addr = V.ADDRESS.newAddr() in
      (V.VarCell(dummy_pos,newLabel(),addr), 
       Es5_cps_values.Store.add addr (V.Object(p,l,a',ps')) bindingStore, retStore, exnStore)
    | C.Lambda(p,l,r,e,a,b) -> 
      let (bindingStore, retStore, exnStore) =
        garbage_collect env bindingStore retEnv retStore exnEnv exnStore in
      (V.Closure(p,l,r,e,a,b,env, retEnv, exnEnv), bindingStore, retStore, exnStore)
  and eval_prim (prim : C.cps_prim) env bindingStore retEnv retStore exnEnv exnStore = 
    (* U.print_bindings env bindingStore; *)
    (* (let pretty_val v = Es5_cps_pretty.value v Format.str_formatter; Format.flush_str_formatter() in *)
    (*   match prim with *)
    (* | C.GetAttr(_, l, a, o, f) -> printf "%d GetAttr %s[%s<%s>]\n" l (pretty_val o) (E.string_of_attr a) (pretty_val f) *)
    (* | C.SetAttr(_, l, a, o, f, v) -> printf "%d SetAttr %s[%s<%s> = %s]\n" l (pretty_val o) (E.string_of_attr a) (pretty_val f) (pretty_val v) *)
    (* | C.DeleteField(_, l, o, f) -> printf "%d DeleteField %s[%s]\n" l (pretty_val o) (pretty_val f) *)
    (* | C.Op1(_, l, o, a) -> printf "%d Op1(%s, %s)\n" l o (pretty_val a) *)
    (* | C.Op2(_, l, o, a, b) -> printf "%d Op2(%s, %s, %s)\n" l o (pretty_val a) (pretty_val b) *)
    (* | C.MutableOp1(_, l, o, a) -> printf "%d MutableOp1(%s, %s)\n" l o (pretty_val a) *)
    (* | C.SetBang(_, l, i, v) -> printf "%d Set!(%s = %s)\n" l i (pretty_val v) *)
    (* ); *)
    match prim with
    | C.GetAttr(_, _, pattr, obj, field) ->
      let (obj', bindingStore, retStore, exnStore) = 
        eval_val obj env bindingStore retEnv retStore exnEnv exnStore in
      let obj' = match obj' with
        | V.VarCell (_, _, a) -> Es5_cps_values.Store.find a bindingStore
        | _ -> failwith "[cps-interp] set-attr didn't get a VarCell" in
      let (field', bindingStore, retStore, exnStore) = 
        eval_val field env bindingStore retEnv retStore exnEnv exnStore in
      begin match obj', field' with
      | V.Object(pos, label, attrs, props), V.String(_, _, s) -> 
        begin 
          try
            match (List.assoc s props), pattr with
            | V.Data({ V.value = v }, _, _), E.Value -> (v, bindingStore, retStore, exnStore)
            | V.Accessor({ V.getter = g }, _, _), E.Getter -> (g, bindingStore, retStore, exnStore)
            | V.Accessor({ V.setter = s }, _, _), E.Setter -> (s, bindingStore, retStore, exnStore)
            | V.Data(_, _, config), E.Config -> (bool config pos, bindingStore, retStore, exnStore)
            | V.Accessor(_, _, config), E.Config -> (bool config pos, bindingStore, retStore, exnStore)
            | V.Data(_, enum, _), E.Enum -> (bool enum pos, bindingStore, retStore, exnStore)
            | V.Accessor(_, enum, _), E.Enum -> (bool enum pos, bindingStore, retStore, exnStore)
            | V.Data({ V.writable = w }, _, _), E.Writable -> (bool w pos, bindingStore, retStore, exnStore)
            | _ -> failwith "bad access of attribute"
          with Not_found -> failwith "Field not found"
        end
      | _ -> failwith "GetAttr didn't have both an object and a string"
      end
    | C.SetAttr(pos, label, pattr, obj, field, value) ->
      let (obj', bindingStore, retStore, exnStore) = 
        eval_val obj env bindingStore retEnv retStore exnEnv exnStore in
      let (obj', addr) = match obj' with
        | V.VarCell (_, _, a) -> (Es5_cps_values.Store.find a bindingStore, a)
        | _ -> failwith ("[cps-interp] set-attr didn't get a VarCell: " ^ (V.pretty_bind obj')) in
      let (field', bindingStore, retStore, exnStore) = 
        eval_val field env bindingStore retEnv retStore exnEnv exnStore in
      let (value', bindingStore, retStore, exnStore) = 
        eval_val value env bindingStore retEnv retStore exnEnv exnStore  in
      begin match obj', field' with
      | V.Object(pos, label, ({V.extensible = true} as attrs), props), V.String (_, _, s) ->
        let newprop = begin
          try 
            match (List.assoc s props), pattr with
            | V.Data ({ V.writable = true } as d, enum, config), E.Writable -> 
              V.Data ({ d with V.writable = unbool value' }, enum, config)
            | V.Data (d, enum, true), E.Writable ->
              V.Data ({ d with V.writable = unbool value' }, enum, true)
            (* Updating values only checks writable *)
            | V.Data ({ V.writable = true } as d, enum, config), E.Value ->
              V.Data ({ d with V.value = value' }, enum, config)
            (* If we had a data property, update it to an accessor *)
            | V.Data (d, enum, true), E.Setter ->
              V.Accessor ({ V.getter = V.Undefined(dummy_pos, newLabel()); V.setter = value' }, enum, true)
            | V.Data (d, enum, true), E.Getter ->
              V.Accessor ({ V.getter = value'; V.setter = V.Undefined(dummy_pos, newLabel()) }, enum, true)
            (* Accessors can update their getter and setter properties *)
            | V.Accessor (a, enum, true), E.Getter ->
              V.Accessor ({ a with V.getter = value' }, enum, true)
            | V.Accessor (a, enum, true), E.Setter ->
              V.Accessor ({ a with V.setter = value' }, enum, true)
            (* An accessor can be changed into a data property *)
            | V.Accessor (a, enum, true), E.Value ->
              V.Data ({ V.value = value'; V.writable = false; }, enum, true)
            | V.Accessor (a, enum, true), E.Writable ->
              V.Data ({ V.value = V.Undefined(dummy_pos, newLabel()); V.writable = unbool value'; }, enum, true)
            (* enumerable and configurable need configurable=true *)
            | V.Data (d, _, true), E.Enum ->
              V.Data (d, unbool value', true)
            | V.Data (d, enum, true), E.Config ->
              V.Data (d, enum, unbool value')
            | V.Data (d, enum, false), E.Config ->
              (match value' with
              | V.False _ -> V.Data (d, enum, false)
              | _ -> failwith ("[cps-interp] can't set Config property to true once it's false: " ^ s))
            | V.Accessor (a, enum, true), E.Config ->
              V.Accessor (a, enum, unbool value')
            | V.Accessor (a, enum, true), E.Enum ->
              V.Accessor (a, unbool value', true)
            | V.Accessor (a, enum, false), E.Config ->
              (match value' with 
              | V.False _ -> V.Accessor(a, enum, false)
              | _ -> failwith ("[cps-interp] can't set Config property to true once it's false: " ^ s))
            | _ -> failwith ("[cps-interp] bad property set: " ^ s)
          with Not_found ->
            let undef () = V.Undefined(pos, newLabel()) in
            match pattr with
            | E.Getter -> V.Accessor({V.getter = value'; V.setter = undef ()}, false, false)
            | E.Setter -> V.Accessor({V.getter = undef (); V.setter = value'}, false, false)
            | E.Value -> V.Data({V.value = value'; V.writable = false}, false, false)
            | E.Writable -> V.Data({V.value = undef(); V.writable = unbool value'}, false, false)
            | E.Enum -> V.Data({V.value = undef(); V.writable = false}, unbool value', true)
            | E.Config -> V.Data({V.value = undef(); V.writable = false}, true, unbool value')
        end in
        let replaceProp ((s, prop) as newProp) props =
          let rec help props acc =
            match props with
            | [] -> List.rev_append acc [newProp]
            | ((n, p) as oldProp)::props' -> if (s = n) 
              then List.rev_append acc (newProp::props')
              else help props' (oldProp::acc) in
          help props [] in
        let newobj = V.Object(pos, label, attrs, replaceProp (s, newprop) props) in
        (bool true pos, (Es5_cps_values.Store.add addr newobj bindingStore), retStore, exnStore)
      | V.Object(pos, label, {V.extensible = false}, props), V.String (_, _, s) -> 
        failwith "[cps-interp] extending inextensible object"
      | _ -> failwith "[cps-interp] set-attr didn't get an object and a string"
      end
    | C.Op1(_, _, op, arg) -> 
      let (arg', bindingStore, retStore, exnStore) = eval_val arg env bindingStore retEnv retStore exnEnv exnStore in
      (D.op1 op arg' bindingStore, bindingStore, retStore, exnStore)
    | C.Op2(_, _, op, left, right) -> 
      let (left', bindingStore, retStore, exnStore) = eval_val left env bindingStore retEnv retStore exnEnv exnStore in
      let (right', bindingStore, retStore, exnStore) = eval_val right env bindingStore retEnv retStore exnEnv exnStore in
      (D.op2 op left' right' bindingStore, bindingStore, retStore, exnStore)
    | C.MutableOp1(_, _, op, arg) -> 
      let (arg', bindingStore, retStore, exnStore) = eval_val arg env bindingStore retEnv retStore exnEnv exnStore in
      let (value, newStore) = D.mutableOp1 op arg' bindingStore in
      (value, newStore, retStore, exnStore)
    | C.DeleteField(pos, _, obj, field) -> 
      let (obj', bindingStore, retStore, exnStore) = eval_val obj env bindingStore retEnv retStore exnEnv exnStore in
      let (obj', addr, retStore, exnStore) = match obj' with
        | V.VarCell (_, _, a) -> ((Es5_cps_values.Store.find a bindingStore), a, retStore, exnStore)
        | _ -> failwith "[cps-interp] set-attr didn't get a VarCell" in
      let (field', bindingStore, retStore, exnStore) = eval_val field env bindingStore retEnv retStore exnEnv exnStore in
      begin match obj', field' with
      | V.Object(pos, label, attrs, props), V.String (_, _, s) ->
        begin 
          try
            match (List.assoc s props) with
            | V.Data (_, _, true)
            | V.Accessor (_, _, true) ->
              let newObj = V.Object(pos, label, attrs, List.remove_assoc s props) in
              (bool true pos, Es5_cps_values.Store.add addr newObj bindingStore, retStore, exnStore)
            | _ -> (bool false pos, bindingStore, retStore, exnStore)
          with Not_found -> (bool false pos, bindingStore, retStore, exnStore)
        end
      | _ -> failwith "DeleteField didn't have both an object and a string"
      end
    | C.SetBang(_, _, id, value) -> 
      let (value', bindingStore, retStore, exnStore) = eval_val value env bindingStore retEnv retStore exnEnv exnStore in
      let addr = IdMap.find id env in
      (* this is for binding sets
         let bindings = IdMap.find addr bindingStore in
         if (BindingSet.cardinal bindings == 1) 
         then (value', IdMap.add addr (BindingSet.singleton value') bindingStore)
         else (value', IdMap.add addr (BindingSet.add value' bindings) bindingStore) *)
      (value', Es5_cps_values.Store.add addr value' bindingStore, retStore, exnStore) in
  let bindingEnv = IdMap.empty in
  let bindingStore = Es5_cps_values.Store.empty in
  let answerAddr = V.ADDRESS.newAddr() in
  let retContEnv = IdMap.add "%answer" answerAddr IdMap.empty in
  let retContStore = Es5_cps_values.Store.add answerAddr V.Answer Es5_cps_values.Store.empty in
  let errorAddr = V.ADDRESS.newAddr() in
  let exnContEnv = IdMap.add "%error" errorAddr IdMap.empty in
  let exnContStore = Es5_cps_values.Store.add errorAddr V.Error Es5_cps_values.Store.empty in
  let (ans, _, _, _) = (eval_exp exp bindingEnv retContEnv exnContEnv bindingStore retContStore exnContStore) in
  ans





















(* module type STORABLE = sig *)
(*   type t *)
(*   val compare : t -> t -> int *)
(*   val equal : t -> t -> bool *)
(* end *)
(* module Storable = struct *)
(*   type t =  *)
(*     | RetCont of label * id * cps_exp *)
(*     | ExnCont of label * id * id * cps_exp *)
(*     | Value of Es5_cps.cps_value *)
(*   let compare = Pervasives.compare *)
(*   let equal t1 t2 = match (t1, t2) with *)
(*     | RetCont(l1, _, _), RetCont(l2, _, _) -> l1 = l2 *)
(*     | ExnCont(l1, _, _, _), ExnCont(l2, _, _, _) -> l1 = l2 *)
(*     | Value v1, Value v2 -> v1 = v2 *)
(*     | _ -> false *)
(* end *)
  
(* module Labeled_Exp = struct *)
(*   type t = cps_exp *)
(*   let initial_env : Storable.t IdMap.t = *)
(*     let id id = Id(dummy_pos, newLabel(), id) in *)
(*     List.fold_left (fun map (key,value) -> IdMap.add key value map) *)
(*       IdMap.empty *)
(*       [("%answer",  *)
(*         let arg = newVar "arg" in *)
(*         Storable.RetCont(newLabel(), arg, *)
(*                          LetPrim(dummy_pos, newLabel(), newVar "",  *)
(*                                  Op1(dummy_pos, newLabel(), "print", id arg), *)
(*                                  AppFun(dummy_pos, newLabel(), id "%answer", arg, "", [])))); *)
(*        ("%error", *)
(*         let arg = newVar "arg" in *)
(*         let lab = newVar "lab" in  *)
(*         Storable.ExnCont(newLabel(), arg, lab, *)
(*                          LetPrim(dummy_pos, newLabel(), newVar "", *)
(*                                  Op1(dummy_pos, newLabel(), "print", id arg), *)
(*                                  AppFun(dummy_pos, newLabel(), id "%error", arg, lab, []))))] *)
(*   let compare = Pervasives.compare *)
(* end *)
(* module type LABELED_EXP = sig *)
(*   type t *)
(*   val initial_env : Storable.t IdMap.t *)
(*   val compare : t -> t -> int *)
(* end *)
(* module type ENV = sig *)
(*   type t *)
(*   val empty : t *)
(* end *)
(* module type ADDR = sig *)
(*   type t *)
(*   type state *)
(*   type kont *)
(*   val compare : t -> t -> int *)
(*   val alloc : state -> kont -> kont -> t *)
(*   val newAddr : unit -> t *)
(* end *)
(* module type TIME = sig *)
(*   type t *)
(*   type state *)
(*   type kont *)
(*   val start_time : t *)
(*   val tick : state -> kont -> kont -> t *)
(* end *)

(* module K_CFA_TIME : TIME = struct *)
(*   type kont = Mt | Prim | App | Ret | Exn | Label of label *)
(*   type t = kont * label list *)
(*   type state = (cps_exp * t) *)
(*   let start_time = (Mt, []) *)
(*   let truncate list n = *)
(*     let rec helper list n acc = *)
(*       match n, list with *)
(*       | 0, _ -> List.rev acc *)
(*       | _, [] -> List.rev acc *)
(*       | _, hd::tl -> helper tl (n-1) (hd::acc) *)
(*     in helper list n [] *)
(*   let tick (e, (l, delta)) k h = (l, delta) *)
(* (\*    match e with *)
(*     | LetValue *)
(*     | RecValue *)
(*     | LetPrim *)
(*     | LetRetCont *)
(*     | LetExnCont *)
(*     | If *)
(*     | AppFun *)
(*     | AppRetCont *)
(*     | AppExnCont *)
(*     | Eval *\) *)
(* end *)



(* module ABS_STORE = struct *)
(*   module type S = sig *)
(*     type t *)
(*     type addr *)
(*     type storable *)
(*     val equal : t -> t -> bool *)
(*     val empty : t *)
(*     val join  : t -> t -> t *)
(*     val add : addr -> storable -> t -> t *)
(*   end *)
(*   module Make (Addr : ADDR) (Storable : STORABLE) = struct *)
(*     type addr = Addr.t *)
(*     type storable = Storable.t *)
(*     module StorableSet = Set.Make (Storable) *)
(*     module AddrMap = Map.Make (StorableSet) *)
(*     type t = StorableSet.t AddrMap.t *)
(*     let equal store1 store2 = AddrMap.equal Storable.equal store1 store2 *)
(*     let empty = AddrMap.empty *)
(*     let add a v t = *)
(*       try *)
(*         let curBindings = AddrMap.find a t in *)
(*         let newBindings = StorableSet.add v curBindings in *)
(*         AddrMap.add a newBindings t *)
(*       with Not_found -> *)
(*         AddrMap.add a (StorableSet.singleton v) t *)
(*     let join store1 store2 = AddrMap.fold add store1 store2 *)

(*   end *)
(* end *)

(* module System *)
(*   (Exp : LABELED_EXP) *)
(*   (Env : ENV)  *)
(*   (Addr : ADDR)  *)
(*   (Time : TIME) *)
(*   (Store : ABS_STORE.S with type addr = Addr.t with type storable = Storable.t) = struct *)
(*   module State = struct *)
(*     type t = Exp.t * Env.t * Addr.t * Addr.t * Time.t *)
(*     let compare = Pervasives.compare *)
(*   end *)
(*   module StateSet = Set.Make (State) *)

(*   module S = struct *)
(*     type t = State.t * Store.t *)
(*     let compare = Pervasives.compare *)
(*   end *)
(*   module SystemSet = Set.Make (S) *)

(*   let step ((state : State.t), (store : Store.t)) = (state, store) (\* for now *\) *)

(*   type t = StateSet.t * Store.t *)

(*   let inject (e : Exp.t) : State.t * Store.t = *)
(*     let answer = Addr.newAddr()  in *)
(*     let error = Addr.newAddr() in *)
(*     let initialStore = *)
(*       Store.add answer (IdMap.find "%answer" Exp.initial_env) *)
(*         (Store.add error (IdMap.find "%error" Exp.initial_env) *)
(*            Store.empty) in     *)
(*     ((e, Env.empty, answer, error, Time.start_time), initialStore) *)

(*   let aval e = *)
(*     let rec lfp (f : 'help -> t -> ('help * t)) (help : 'help) (state, store) : t = *)
(*       let (help', (state', store')) = f help (state, store) in *)
(*       if (StateSet.equal state state' && Store.equal store store') *)
(*       then (state', store') *)
(*       else lfp f help' (state', store') in *)
(*     let (c_0, sigma_0) = inject e in *)
(*     let _C_0 = StateSet.singleton c_0 in *)
(*     let nextStep (worklist : StateSet.t) ((_C : StateSet.t), (sigma : Store.t)) = *)
(*       let _Q' = StateSet.fold (fun (state : State.t) (curSys : SystemSet.t) ->  *)
(*         SystemSet.add (step (state, sigma)) curSys) worklist SystemSet.empty in *)
(*       let (_C'', sigma'') = SystemSet.fold (fun (state', sigma') (curState, curStore) -> *)
(*         (StateSet.add state' curState, Store.join sigma' curStore)) _Q' (StateSet.empty, sigma) in *)
(*       let _C' = StateSet.union _C _C'' in *)
(*       (_C'', (_C', sigma'')) in *)
(*     lfp nextStep _C_0 (_C_0, sigma_0) *)
(* end *)

type env = C.cps_exp IdMap.t

let build expr =
  let v = expr in
  let cfg = G.add_vertex G.empty v in
  let rec build_exp (g : G.t) (env : env) (entry : vert) (exp : Es5_cps.cps_exp) : (G.t * vert) =
    match exp with
  | C.LetValue(pos,l, id, value, exp) -> (g, entry)
  | C.RecValue(pos,l, id, value, exp) -> (g, entry)
  | C.LetPrim(pos,l, id, prim, exp) -> (g, entry)
  | C.LetRetCont(l,ret, r, exp) -> (g, entry)
  | C.LetExnCont(l,exn, e, exp) -> (g, entry)
  | C.If(pos,l, cond, trueBranch, falseBranch) -> (g, entry)
  | C.AppFun(pos,l, func, ret, exn, args) -> (g, entry)
  | C.AppRetCont(l,ret, arg) -> (g, entry)
  | C.AppExnCont(l,exn, arg, label) -> (g, entry)
  | C.Eval(pos,l, eval) -> (g, entry) in
  fst (build_exp cfg IdMap.empty v expr)

let cpsv_to_string cps_value =
  Es5_cps_pretty.value false cps_value Format.str_formatter;
  Format.flush_str_formatter()
module Display = struct
  include G
  let vertex_name v = match v with
  | C.LetValue(pos,l, id, value, exp) -> "LetValue(" ^ id ^ ")"
  | C.RecValue(pos,l, id, value, exp) -> "RecValue(" ^ id ^ ")"
  | C.LetPrim(pos,l, id, prim, exp) -> "LetPrim(" ^ id ^ ")"
  | C.LetRetCont(l,ret, r, exp) -> "LetRet(" ^ ret ^ ")"
  | C.LetExnCont(l,exn, e, exp) -> "LetExn(" ^ exn ^ ")"
  | C.If(pos,l, cond, trueBranch, falseBranch) -> "If(" ^ (cpsv_to_string cond) ^ ")"
  | C.AppFun(pos,l, func, ret, exn, args) -> "App(" ^ (cpsv_to_string func) ^ ")"
  | C.AppRetCont(l,ret, arg) -> "Ret()"
  | C.AppExnCont(l,exn, arg, label) -> "Exn(" ^ (cpsv_to_string label) ^ ")"
  | C.Eval(pos,l, eval) -> "Eval"
  let graph_attributes _ = []
  let default_vertex_attributes _ = []
  let vertex_attributes _ = []
  let default_edge_attributes _ = []
  let edge_attributes _ = []
  let get_subgraph _ = None
end

module Dot = Graphviz.Dot(Display)

let print_cfg g =
  Dot.fprint_graph Format.str_formatter g;
  Format.flush_str_formatter()
