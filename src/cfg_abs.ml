open Prelude
module C = Es5_cps
module D = Es5_cps_absdelta
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

type complete = Ans of D.ValueLattice.t | Err of D.ValueLattice.t
module AddrSet = Set.Make (Es5_cps_values.ADDRESS)


type abstractEnv = (V.ADDRESS.t IdMap.t * V.retContEnv * V.exnContEnv) C.LabelMap.t
type abstractStore = (D.ValueLattice.t Es5_cps_values.Store.t * V.retContStore * V.exnContStore) C.LabelMap.t


(* **************************************** *)
let print_abs_bindings label env store =
  let (bE, rE, eE) = C.LabelMap.find label env in
  let (bH, rH, eH) = C.LabelMap.find label store in
  printf "Condensed abs bindings at %d:\n" label;
  let reachableAddrs : V.ADDRESS.t list ref = ref [] in
  let rootAddrs : V.ADDRESS.t list ref = ref [] in
  let rec addReachable obj = match (D.ValueLattice.addrsOf obj) with
    | D.AddressSetLattice.Set addrs ->
      D.AddressSet.iter (fun a -> 
        reachableAddrs := a::!reachableAddrs;
        addReachable (Es5_cps_values.Store.find a bH)) addrs
    | _ -> () in
  IdMap.iter (fun id addr ->
    rootAddrs := addr::!rootAddrs;
    try 
      let lookup = Es5_cps_values.Store.find addr bH in
      addReachable lookup;
      vert[horz[text "  "; text id; text "->"; (V.ADDRESS.pretty addr); text "->"; (D.ValueLattice.pretty lookup)]]
        Format.str_formatter;
      printf "%s\n" (Format.flush_str_formatter ())
    with _ -> printf "  %s -> %s -> XXX dangling pointer XXX\n" id (V.ADDRESS.toString addr)) bE;
  List.iter (fun addr ->
    if List.mem addr !rootAddrs then ()
    else begin
      let lookup = Es5_cps_values.Store.find addr bH in
      vert[horz[text "  ** ->"; (V.ADDRESS.pretty addr); text "->"; (D.ValueLattice.pretty lookup)]]
        Format.str_formatter;
      printf "%s\n" (Format.flush_str_formatter ());
      rootAddrs := addr::!rootAddrs
    end)
    !reachableAddrs

(* let print_rets env store =  *)
(*   printf "Condensed returns:\n"; *)
(*   IdMap.iter (fun id addr -> printf "  %s -> %s" id (V.ADDRESS.toString addr); *)
(*     match (Es5_cps_values.Store.find addr store) with *)
(*     | V.Answer -> printf " -> ANS\n" *)
(*     | V.RetCont(l, arg, _, _,_,_) -> printf " -> RET(%s->...)[...]\n" arg) env *)

(* let print_exns env store =  *)
(*   printf "Error Env:\n"; *)
(*   IdMap.iter (fun id addr -> printf "  %s -> %s\n" id (V.ADDRESS.toString addr)) env; *)
(*   printf "Error Store:\n"; *)
(*   Es5_cps_values.Store.iter (fun addr ret -> *)
(*     match ret with *)
(*     | V.Error -> printf "  %s -> ERR\n" (V.ADDRESS.toString addr) *)
(*     | V.ExnCont(l, arg, lbl, body, _,_,_) -> printf "  %s -> RET(%s, %s->...)\n" (V.ADDRESS.toString addr) arg lbl *)
(*   ) store *)
(* **************************************** *)





let addBinding label id addr env =
  try
    let (b, r, e) = C.LabelMap.find label env in
    C.LabelMap.add label ((IdMap.add id addr b), r, e) env
  with _ -> C.LabelMap.add label (IdMap.singleton id addr, IdMap.empty, IdMap.empty) env
let addRet label id addr env =
  try
    let (b, r, e) = C.LabelMap.find label env in
    C.LabelMap.add label (b, (IdMap.add id addr r), e) env
  with _ -> C.LabelMap.add label (IdMap.empty, IdMap.singleton id addr, IdMap.empty) env
let addExn label id addr env =
  try
    let (b, r, e) = C.LabelMap.find label env in
    C.LabelMap.add label (b, r, (IdMap.add id addr e)) env
  with _ -> C.LabelMap.add label (IdMap.empty, IdMap.empty, IdMap.singleton id addr) env
let updateValue label addr v store =
  try
    let (b, r, e) = C.LabelMap.find label store in
    let b' =
      try
        let oldV = Es5_cps_values.Store.find addr b in
        Es5_cps_values.Store.add addr (D.ValueLattice.join [v; oldV]) b
      with _ -> Es5_cps_values.Store.singleton addr v in
    C.LabelMap.add label (b', r, e) store
  with _ -> C.LabelMap.singleton label (Es5_cps_values.Store.singleton addr v,
                                        V.Store.empty,
                                        V.Store.empty)
let getEnv label env =
  try C.LabelMap.find label env
  with _ -> (IdMap.empty, IdMap.empty, IdMap.empty)
let getStore label store =
  try C.LabelMap.find label store
  with _ -> (Es5_cps_values.Store.empty, V.Store.empty, V.Store.empty)
let getBinding label id env store = 
  let (b, r, e) = getEnv label env in
  try 
    let addr = IdMap.find id b in
    let (b, r, e) = getStore label store in
    try
      Es5_cps_values.Store.find addr b
    with Not_found -> D.ValueLattice._Bot ()
  with Not_found -> D.ValueLattice._Bot ()

let refineStore whichBranch branchLabel cond store = store (* TODO *)

let updateRet label addr v store =
  try
    let (b, r, e) = C.LabelMap.find label store in
    let r' = V.Store.add addr v r in
    C.LabelMap.add label (b, r', e) store
  with _ -> C.LabelMap.singleton label (Es5_cps_values.Store.empty,
                                        V.Store.singleton addr v,
                                        V.Store.empty)
let updateExn label addr v store =
  try
    let (b, r, e) = C.LabelMap.find label store in
    let e' = V.Store.add addr v e in
    C.LabelMap.add label (b, r, e') store
  with _ -> C.LabelMap.singleton label (Es5_cps_values.Store.empty,
                                        V.Store.empty,
                                        V.Store.singleton addr v)
let mergeAbstractStores (b1, r1, e1) (b2, r2, e2) =
  let b = Es5_cps_values.Store.merge (fun _ v1 v2 ->
    match (v1, v2) with
    | None, _ -> v2
    | _, None -> v1
    | Some v1, Some v2 -> Some (D.ValueLattice.join [v1;v2])) b1 b2 in
  let r = V.Store.merge (fun _ v1 v2 ->
    match (v1, v2) with
    | None, _ -> v2
    | _ -> v1) r1 r2 in
  let e = V.Store.merge (fun _ v1 v2 ->
    match (v1, v2) with
    | None, _ -> v2
    | _ -> v1) e1 e2 in
  (b, r, e)
let updateValues label values store =
  let (b1, r1, e1) =
    try C.LabelMap.find label store
    with _ -> (Es5_cps_values.Store.empty, V.Store.empty, V.Store.empty) in
  C.LabelMap.add label (mergeAbstractStores (b1, r1, e1) (values, r1, e1)) store
let joinStores store1 store2 = C.LabelMap.merge (fun _ s1 s2 ->
  match (s1, s2) with
  | None, _ -> s2
  | _, None -> s1
  | Some s1, Some s2 -> Some (mergeAbstractStores s1 s2)) store1 store2
let joinEnvs env1 env2 = C.LabelMap.merge (fun _ e1 e2 ->
  match (e1, e2) with
  | None, _ -> e2
  | _ -> e1) env1 env2
let pushStore label1 label2 store =
  let s1 = getStore label1 store in
  let s2 = getStore label2 store in
  C.LabelMap.add label2 (mergeAbstractStores s1 s2) store
let copyEnv label1 label2 env =
  let e1 = getEnv label1 env in
  C.LabelMap.add label2 e1 env
let replaceBindings label bindings env =
  let (_, r, e) = getEnv label env in
  C.LabelMap.add label (bindings, r, e) env

let eval (exp : C.cps_exp) : abstractEnv * abstractStore * C.Label.t =
  (* let newLabel = C.newLabel in *)

  (* (\*  *)
  (*  * Garbage collection of the stores, assuming that the provided environments are all the  *)
  (*  * roots that exist.  Similarly, assume that the closed-over environments in closures and *)
  (*  * continuations are themselves gc'ed, so that they only contain reachable information and *)
  (*  * no garbage. *)
  (*  *\) *)
  (* let garbage_collect *)
  (*     bindingEnv (bindingStore : V.bind_value Es5_cps_values.Store.t) *)
  (*     retContEnv retContStore *)
  (*     exnContEnv exnContStore = *)
  (*   (U.dump_heap_as_dot "before_" bindingEnv bindingStore retContEnv retContStore exnContEnv exnContStore) Format.str_formatter; *)
  (*   print_string (Format.flush_str_formatter ()); *)
  (*   let noIds = AddrSet.empty in *)
  (*   let just addr = AddrSet.singleton addr in *)
  (*   let add addr = AddrSet.add addr in *)
  (*   let (++) l1 l2 = AddrSet.union l1 l2 in *)
  (*   let join (b1, r1, e1) (b2, r2, e2) = (b1++b2, r1++r2, e1++e2) in *)
  (*   let lookup addr store = try Some (Es5_cps_values.Store.find addr store) with _ -> None in *)
  (*   let rec reachable_retContEnv_addrs (retContEnv : V.retContEnv) = *)
  (*     IdMap.fold (fun _ rAddr (b, r, e) -> *)
  (*       match (lookup rAddr retContStore) with *)
  (*       | None *)
  (*       | Some V.Answer -> (b, add rAddr r, e) *)
  (*       | Some (V.RetCont (_, _, _, bindingEnv, retContEnv, exnContEnv)) -> join *)
  (*         (join (reachable_bindingEnv_addrs bindingEnv) *)
  (*            (join (reachable_retContEnv_addrs retContEnv) *)
  (*               (reachable_exnContEnv_addrs exnContEnv))) *)
  (*         (b, add rAddr r, e)) retContEnv (noIds, noIds, noIds) *)
  (*   and reachable_exnContEnv_addrs (exnContEnv : V.exnContEnv) = *)
  (*     IdMap.fold (fun _ eAddr (b, r, e) -> *)
  (*       match (lookup eAddr exnContStore) with *)
  (*       | None *)
  (*       | Some V.Error -> (b, r, add eAddr e) *)
  (*       | Some (V.ExnCont (_, _, _, _, bindingEnv, retContEnv, exnContEnv)) -> join *)
  (*         (join (reachable_bindingEnv_addrs bindingEnv) *)
  (*            (join (reachable_retContEnv_addrs retContEnv) *)
  (*               (reachable_exnContEnv_addrs exnContEnv))) *)
  (*         (b, r, add eAddr e)) exnContEnv (noIds, noIds, noIds) *)
  (*   and reachable_bindingEnv_addrs (bindingEnv : V.bindingEnv) = *)
  (*     let rec reachable_binding v = *)
  (*       match v with *)
  (*       | V.VarCell (_, _, ptr) ->  *)
  (*         begin match (lookup ptr bindingStore) with *)
  (*         | None -> (just ptr, noIds, noIds) *)
  (*         | Some v -> join (just ptr, noIds, noIds) (reachable_binding v) *)
  (*         end *)
  (*       | V.Object (_, _, attrs, props) -> *)
  (*         let prim = match attrs.V.primval with  *)
  (*           | None -> (noIds, noIds, noIds) *)
  (*           | Some v -> reachable_binding v in *)
  (*         let code = match attrs.V.code with *)
  (*           | None -> (noIds, noIds, noIds) *)
  (*           | Some v -> reachable_binding v in *)
  (*         let proto = match attrs.V.proto with *)
  (*           | None -> (noIds, noIds, noIds) *)
  (*           | Some v -> reachable_binding v in *)
  (*         let prop a = match a with *)
  (*           | (_, V.Data ({V.value = v}, _, _)) -> reachable_binding v *)
  (*           | (_, V.Accessor ({V.getter = g; V.setter = s}, _, _)) ->  *)
  (*             join (reachable_binding g) (reachable_binding s) in *)
  (*         List.fold_left (fun acc p -> join (prop p) acc) (join prim (join code proto)) props *)
  (*       | V.Closure(_, _, _, _, _, _, bindingEnv', retContEnv', exnContEnv') -> *)
  (*         let newBinds = if (bindingEnv == bindingEnv') then (noIds, noIds, noIds) else (reachable_bindingEnv_addrs bindingEnv') in *)
  (*         let newRets = if (retContEnv == retContEnv') then (noIds, noIds, noIds) else (reachable_retContEnv_addrs retContEnv') in *)
  (*         let newExns = if (exnContEnv == exnContEnv') then (noIds, noIds, noIds) else (reachable_exnContEnv_addrs exnContEnv') in *)
  (*         join newBinds (join newRets newExns) *)
  (*       | _ -> (noIds, noIds, noIds) in *)
  (*     IdMap.fold (fun _ bAddr (b, r, e) ->  *)
  (*       match (lookup bAddr bindingStore) with *)
  (*       | None -> (add bAddr b, r, e) *)
  (*       | Some v -> join (add bAddr b, r, e) (reachable_binding v)) bindingEnv (noIds, noIds, noIds) in  *)
  (*   let (reachable_bind_addrs, reachable_ret_addrs, reachable_exn_addrs) = *)
  (*     join (reachable_bindingEnv_addrs bindingEnv) *)
  (*       (join (reachable_retContEnv_addrs retContEnv) *)
  (*          (reachable_exnContEnv_addrs exnContEnv)) in *)
  (*   (\* monomorphism restriction at module level means I can't encapsulate the call to Store.fold... *\) *)
  (*   let filter_sto stoName pretty addrs = (fun addr value acc ->  *)
  (*     if (AddrSet.mem addr addrs) *)
  (*     then acc *)
  (*     else  *)
  (*       ( *)
  (*         (\* print_string ("discarding " ^ (string_of_int addr) ^ "->" ^ (pretty value) ^ " from store " ^ stoName ^ "\n"); *\) *)
  (*         Es5_cps_values.Store.remove addr acc) *)
  (*   ) in *)
  (*   let (newBindings, newRets, newExns) = *)
  (*     (Es5_cps_values.Store.fold (filter_sto "bindings" V.pretty_bind reachable_bind_addrs)  *)
  (*        bindingStore bindingStore, *)
  (*      Es5_cps_values.Store.fold (filter_sto "retconts" V.pretty_retcont reachable_ret_addrs)  *)
  (*        retContStore retContStore, *)
  (*      Es5_cps_values.Store.fold (filter_sto "exnconts" V.pretty_exncont reachable_exn_addrs)  *)
  (*        exnContStore exnContStore) in *)
  (*   (U.dump_heap_as_dot "after_" bindingEnv newBindings retContEnv newRets exnContEnv newExns) Format.str_formatter; *)
  (*   (newBindings, newRets, newExns) in *)
  let printModReasons label reasons = 
    let module FX = FormatExt in
    FX.vert ((FX.horz [FX.text "For label"; FX.int label])::
                (List.map (fun (n,b) -> FX.horz [FX.text n; FX.text "="; if b then FX.text "true" else FX.text "false"]) reasons))
      Format.str_formatter;
    printf "%s\n" (Format.flush_str_formatter ()) in
  let rec eval_exp exp (exitLab : C.Label.t) (env : abstractEnv) (store : abstractStore) : abstractEnv * abstractStore * bool = 
    print_string "In eval_exp for ";
    let label = (match exp with
    | C.LetValue (_, l, id, _, _) -> printf "%s" ("LetValue " ^ (string_of_int l) ^ "," ^ id ^ "\n"); l
    | C.RecValue (_, l, id, _, _) -> printf "%s" ("RecValue " ^ (string_of_int l) ^ "," ^ id ^ "\n"); l
    | C.LetPrim (_, l, id, _, _) -> printf "%s" ("LetPrim " ^ (string_of_int l) ^ "," ^ id ^ "\n"); l
    | C.LetRetCont (l, id, _, _, _) -> printf "%s" ("LetRetCont " ^ (string_of_int l) ^ "," ^ id ^ "\n"); l
    | C.LetExnCont (l, id, _, _, _, _) -> printf "%s" ("LetExnCont " ^ (string_of_int l) ^ "," ^ id ^ "\n"); l
    | C.AppRetCont (l, id, _) -> printf "%s" ("AppRetCont " ^ (string_of_int l) ^ "," ^ id ^ "\n"); l
    | C.AppExnCont (l, id, _, _) -> printf "%s" ("AppExnCont " ^ (string_of_int l) ^ "," ^ id ^ "\n"); l
    | C.AppFun (_, l, f, r, e, a) -> printf "%s %s(Ret %s, Exn %s; %s)\n" ("AppFun " ^ (string_of_int l))
      (Es5_cps_pretty.cps_value_to_string f) r e (String.concat ", " (List.map Es5_cps_pretty.cps_value_to_string a)); l
    | C.If(_, l, _, _, _) -> printf "%s" ("If " ^ (string_of_int l) ^ "\n"); l
    | C.Eval(_, l, _) -> printf "%s" ("Eval " ^ (string_of_int l) ^ "\n"); l
    ) in
    print_abs_bindings label env store;

    match exp with
    | C.LetValue(pos, label, id, value, body) ->
      let oldValue = eval_val value env store in
      let store' = pushStore label (C.label_of_val value) store in
      let env' = copyEnv label (C.label_of_val value) env in
      let value' = eval_val value env' store' in
      printf "Pushing env/store from %d to %d\n" label (C.label_of_val value);
      printf "Env/store for value:%d:\n" (C.label_of_val value);
      print_abs_bindings (C.label_of_val value) env' store';
      let blab = C.label_of_exp body in
      V.ADDRESS.resetForContour [label];
      let addr = V.ADDRESS.addrForContour [label] in
      let env'' = (addBinding blab id addr (copyEnv (C.label_of_val value) blab env')) in
      let store'' = (updateValue blab addr value' (pushStore (C.label_of_val value) blab store')) in
      printf "Pushing env/store from %d to %d\n" (C.label_of_val value) blab;
      printf "Env/store for body:%d:\n" blab;
      print_abs_bindings blab env'' store'';
      let (env3, store3, bodyMod) = eval_exp body exitLab env'' store'' in
      printModReasons label ["bodyMod", bodyMod; "oldValue != value'", oldValue != value'];
      ((joinEnvs env'' env3), (joinStores store'' store3), (bodyMod || (oldValue != value')))
    | C.RecValue(pos, label, id, value, body) ->
      let oldValue = eval_val value env store in
      let vlab = C.label_of_val value in
      let blab = C.label_of_exp body in
      let store' = pushStore label vlab store in
      V.ADDRESS.resetForContour [label];
      let addr = V.ADDRESS.addrForContour [label] in
      let env' = addBinding vlab id addr (copyEnv label vlab env) in
      let rec fixpoint (bot, modified) store =
        let value' = eval_val value env' store in
        if (bot = value') 
        then begin
          printf "Finished with inner fixpoint\n";
          (value', store, modified)
        end 
        else begin
          printf "In inner fixpoint, modified: %s\n" (if modified then "true" else "false");
          let widened = (D.ValueLattice.join [bot;value']) in
          fixpoint (widened, true) (updateValue vlab addr widened store) 
        end in
      let (value', store'', modified) = 
        fixpoint (D.ValueLattice._Bot (), false) (updateValue vlab addr (D.ValueLattice._Bot ()) store') in
      let (env3, store3, bodyMod) = eval_exp body exitLab (copyEnv vlab blab env') (pushStore vlab blab store'') in
      printModReasons label ["bodyMod", bodyMod; "modified", modified; "value' != oldValue", value' != oldValue];
      ((joinEnvs env' env3), (joinStores store'' store3), (bodyMod || modified || (value' != oldValue)))
    | C.LetPrim(pos, label, id, prim, body) ->
      let (oldValue, oldStore, oldMod) = eval_prim prim env store in
      let plab = C.label_of_prim prim in
      let blab = C.label_of_exp body in
      let store' = pushStore label plab store in
      let env' = copyEnv label plab env in
      let (value', store'', primMod) = eval_prim prim env' store' in
      V.ADDRESS.resetForContour [label];
      let addr = V.ADDRESS.addrForContour [label] in
      let env'' = (addBinding blab id addr (copyEnv plab blab env')) in
      let store3 = (updateValue blab addr value' (pushStore plab blab store'')) in
      let (env3, store4, bodyMod) = eval_exp body exitLab env'' store3 in
      ((joinEnvs env'' env3), (joinStores store3 store4), (oldMod || primMod || bodyMod || (oldValue != value')))
    | C.LetRetCont(label, id, arg, body, exp) ->
      (* let (bindingStore, retContStore, exnContStore) = *)
      (*   garbage_collect bindingEnv bindingStore retContEnv retContStore exnContEnv exnContStore in *)
      let elab = C.label_of_exp exp in
      let (b, r, e) = getEnv label env in
      let ret = V.RetCont(label, arg, body, b, r, e) in
      let addr = V.ADDRESS.newAddr() in (* Choose not to lose any precision on ret-cont allocation *)
      let env' = (addRet elab id addr (copyEnv label elab env)) in
      let store' = (updateRet elab addr ret (pushStore label elab store)) in
      (* print_rets retEnv' retStore'; *)
      eval_exp exp exitLab env' store'
    | C.AppRetCont(label, id, value) ->
      (* print_rets retContEnv retContStore; *)
      let oldValue = eval_val value env store in
      let store' = pushStore label (C.label_of_val value) store in
      let env' = copyEnv label (C.label_of_val value) env in
      let value' = eval_val value env' store' in
      let (bindingEnv, retContEnv, _) = getEnv label env in
      let (bindingStore, retContStore, _) = getStore label store in
      let ret = V.Store.find (IdMap.find id retContEnv) retContStore in
      begin match ret with
      | V.Answer -> 
        let finalAns = (match (D.ValueLattice.addrsOf value') with
          | D.AddressSetLattice.Set addrs ->
            let deref = D.ValueLattice.join (List.map (fun addr -> Es5_cps_values.Store.find addr bindingStore)
                                               (D.AddressSetLattice.elements addrs)) in
            D.ValueLattice.join [deref; value']
          | a -> value'
        ) in
        let answerVal = IdMap.find "%%ANSWER" bindingEnv in
        (env', updateValue exitLab answerVal finalAns store', value' != oldValue)
      | V.RetCont (_, arg, body, bindingEnv, retContEnv, exnContEnv) ->
        V.ADDRESS.resetForContour [label];
        let addr = V.ADDRESS.addrForContour [label] in
        let blab = C.label_of_exp body in
        let env'' = (addBinding blab arg addr (copyEnv label blab env')) in
        let store'' = (updateValue blab addr value' (pushStore label blab store')) in
        let (env3, store3, modRet) = eval_exp body exitLab env'' store'' in
        ((joinEnvs env'' env3), (joinStores store'' store3), (modRet || value' != oldValue))
      end
    | C.LetExnCont(label, id, arg, lbl, body, exp) ->
      (* let (bindingStore, retContStore, exnContStore) = *)
      (*   garbage_collect bindingEnv bindingStore retContEnv retContStore exnContEnv exnContStore in *)
      let elab = C.label_of_exp exp in
      let (b, r, e) = getEnv label env in
      let exn = V.ExnCont(label, arg, lbl, body, b, r, e) in
      let addr = V.ADDRESS.newAddr() in (* Choose not to lose any precision on exn-cont allocation *)
      let env' = (addExn elab id addr (copyEnv label elab env)) in
      let store' = (updateExn elab addr exn (pushStore label elab store)) in
      (* print_exns retEnv' retStore'; *)
      eval_exp exp exitLab env' store'
    | C.AppExnCont(label, id, arg, lbl) ->
      (* print_exns exnContEnv exnContStore; *)
      let oldArg = eval_val arg env store in
      let oldLbl = eval_val lbl env store in
      let envArg = copyEnv label (C.label_of_val arg) env in
      let storeArg = pushStore label (C.label_of_val arg) store in
      let arg' = eval_val arg envArg storeArg in
      let envLbl = copyEnv label (C.label_of_val lbl) envArg in
      let storeLbl = pushStore label (C.label_of_val lbl) storeArg in
      let lbl' = eval_val lbl envLbl storeLbl in
      let (bindingEnv, _, exnContEnv) = getEnv label env in
      let (bindingStore, _, exnContStore) = getStore label store in
      let exn = V.Store.find (IdMap.find id exnContEnv) exnContStore in
      begin match exn with
      | V.Error -> 
        let oldFinalErr = getBinding exitLab "%%ERROR" env store in
        let finalErr = (match (D.ValueLattice.addrsOf arg') with
          | D.AddressSetLattice.Set addrs ->
            let deref = D.ValueLattice.join (List.map (fun addr -> Es5_cps_values.Store.find addr bindingStore)
                                               (D.AddressSetLattice.elements addrs)) in
            D.ValueLattice.join [deref; arg']
          | a -> arg'
        ) in
        let errorVal = IdMap.find "%%ERROR" bindingEnv in
        (envLbl, updateValue exitLab errorVal finalErr storeLbl, finalErr != oldFinalErr)
      | V.ExnCont(_, arg, lbl, body, bindingEnv, retContEnv, exnContEnv) ->
        V.ADDRESS.resetForContour [label];
        let argAddr = V.ADDRESS.addrForContour [label] in
        let lblAddr = V.ADDRESS.addrForContour [label] in
        let blab = C.label_of_exp body in
        let env'' = (addBinding blab arg argAddr 
                       (addBinding blab lbl lblAddr (copyEnv label blab envLbl))) in
        let store'' = (updateValue blab argAddr arg' 
                         (updateValue blab lblAddr lbl' (pushStore label blab storeLbl))) in
        let (env3, store3, modExn) = eval_exp body exitLab env'' store'' in
        ((joinEnvs env'' env3), (joinStores store'' store3), (modExn || arg' != oldArg || lbl' != oldLbl))
      end
    | C.If(pos, label, cond, left, right) ->
      let oldCond = eval_val cond env store in
      let store' = pushStore label (C.label_of_val cond) store in
      let env' = copyEnv label (C.label_of_val cond) env in
      let cond' = eval_val cond env' store' in
      let leftStore = refineStore true (C.label_of_exp left) cond store' in
      let leftEnv = copyEnv label (C.label_of_exp left) env in
      let rightStore = refineStore false (C.label_of_exp right) cond store' in
      let rightEnv = copyEnv label (C.label_of_exp right) env in
      let (leftEnv', leftStore', leftMod) = (eval_exp left exitLab leftEnv leftStore) in
      let (rightEnv', rightStore', rightMod) = (eval_exp right exitLab rightEnv rightStore) in
      ((joinEnvs leftEnv' rightEnv'), 
       (joinStores leftStore' rightStore'), 
       (leftMod || rightMod || (oldCond != cond')))
    | C.AppFun(pos, label, func, ret, exn, args) ->
      (* let (bindingStore, retContStore, exnContStore) = *)
      (*   garbage_collect bindingEnv bindingStore retContEnv retContStore exnContEnv exnContStore in *)
      let oldFunc = eval_val func env store in
      let funcLab = C.label_of_val func in
      let store1 = pushStore label funcLab store in
      let env1 = copyEnv label funcLab env in
      let func' = eval_val func env1 store1 in

      let (args', argsMod, env2, store2) = List.fold_left (fun (args, argsMod, envArg, storeArg) arg ->
        let oldArg = eval_val arg env store in
        let argLab = C.label_of_val arg in
        let envArg' = copyEnv label argLab envArg in
        let storeArg' = pushStore label argLab storeArg in
        let arg' = eval_val arg envArg' storeArg' in
        (arg'::args, argsMod || oldArg != arg', joinEnvs envArg envArg', joinStores storeArg storeArg')
      ) ([], false, env1, store1) args in
      if (func' = oldFunc && not argsMod) 
      then (env, store, false)
      else begin
        let args' = List.rev args' in
        let (bindingEnv, retContEnv, exnContEnv) = getEnv label env in
        let (bindingStore, retContStore, exnContStore) = getStore label store in
        let ret' = V.Store.find (IdMap.find ret retContEnv) retContStore in
        let exn' = V.Store.find (IdMap.find exn exnContEnv) exnContStore in
        let getLambda fobj = 
          let closures = D.ValueLattice.closureOf fobj in
          let obj = D.ValueLattice.objOf fobj in
          match obj with
          | D.ObjLattice.Bot -> closures
          | D.ObjLattice.Top -> D.ClosureSetLattice._Top ()
          | D.ObjLattice.Obj ({D.ObjLattice.code = Some c}, _) -> D.ClosureSetLattice.join [closures;c]
          | _ -> closures in
        V.ADDRESS.resetForContour [label];
        let closureResults = match getLambda func' with
          | D.ClosureSetLattice.Bot -> [] (* TODO *)
          | D.ClosureSetLattice.Top -> [] (* TODO *)
          | D.ClosureSetLattice.Set closures -> D.ClosureSet.fold (fun closure acc -> 
            let (retArg, exnArg, argNames, body, cBindingEnv, cRetEnv, cExnEnv) = closure in
            let retAddr = V.ADDRESS.addrForContour [label] in
            let exnAddr = V.ADDRESS.addrForContour [label]  in
            let argAddrs = List.map (fun _ -> V.ADDRESS.addrForContour [label]) argNames in
            let blab = C.label_of_exp body in
            let env' = List.fold_left (fun env (name, addr) -> addBinding blab name addr env)
              (replaceBindings blab cBindingEnv (copyEnv label blab env2))  (* NEED THE CLOSURE ENVIRONMENTS *)
              (List.combine argNames argAddrs) in
            let store' = List.fold_left (fun store (addr, value) -> updateValue blab addr value store)
              (pushStore label blab store2) (List.combine argAddrs args') in
            let env'' = addRet blab retArg retAddr (addExn blab exnArg exnAddr env') in
            let store'' = updateRet blab retAddr ret' (updateExn blab exnAddr exn' store') in
            (eval_exp body exitLab env'' store'')::acc
          ) closures [] in
        List.fold_left (fun (e1, s1, m1) (e2, s2, m2) -> (joinEnvs e1 e2, joinStores s1 s2, m1 || m2)) 
          (env2, store2, oldFunc != func' || argsMod) closureResults
      end
    | C.Eval _ ->
      failwith "Not yet implemented"

  and eval_val (value : C.cps_value) (env : abstractEnv) (store : abstractStore)
      : D.ValueLattice.t = 
    let module VL = D.ValueLattice in
    match value with
    | C.Id(_, label, id) -> getBinding label id env store
    | C.Null _ -> VL.injectNull (D.NullLattice._Top ())
    | C.Undefined _ -> VL.injectUndef (D.UndefLattice._Top ())
    | C.String(_, _, s) -> D.str s
    | C.Num(_, _, n) -> D.num n
    | C.True _ -> D.bool true
    | C.False _ -> D.bool false
    | C.Object(p, label, a, ps) -> 
      (* let (bindingStore, retStore, exnStore) = *)
      (*   garbage_collect env bindingStore retEnv retStore exnEnv exnStore in *)
      let opt_val v env store = match v with 
        | None -> None
        | Some v -> 
          let env' = copyEnv label (C.label_of_val v) env in
          let store' = pushStore label (C.label_of_val v) store in
          Some (eval_val v env' store') in
      let primval = opt_val a.C.primval env store in
      let code = match opt_val a.C.code env store with
        | None -> None
        | Some v -> Some (D.ValueLattice.closureOf v) in
      let proto = opt_val a.C.proto env store in
      let a' = { D.ObjLattice.primval = primval; D.ObjLattice.code = code; D.ObjLattice.proto = proto; 
                 D.ObjLattice.klass = D.StringLattice.inject a.C.klass; 
                 D.ObjLattice.extensible = D.BoolLattice.inject a.C.extensible } in
      let prop props (str, p) = (match p with
        | C.Data({C.value = id; C.writable = w}, enum, config) ->
          let v' = getBinding label id env store in
          IdMap.add str (D.ObjLattice.Data({D.ObjLattice.value = v'; 
                                            D.ObjLattice.writable = D.BoolLattice.inject w}, 
                                           D.BoolLattice.inject enum, D.BoolLattice.inject config)) props
        | C.Accessor({C.getter = g; C.setter = s}, enum, config) -> 
          let g' = getBinding label g env store in
          let s' = getBinding label s env store in
          IdMap.add str (D.ObjLattice.Accessor({D.ObjLattice.getter = g'; D.ObjLattice.setter = s'}, 
                                               D.BoolLattice.inject enum, D.BoolLattice.inject config)) props
      ) in
      let ps' = List.fold_left prop IdMap.empty ps in
      VL.injectObj (D.ObjLattice.Obj (a', ps'))
    | C.Lambda(_, label, r, e, args, body) -> 
      (* let (bindingStore, retStore, exnStore) = *)
      (*   garbage_collect env bindingStore retEnv retStore exnEnv exnStore in *)
      let (env, retEnv, exnEnv) = getEnv label env in
      VL.injectClosure (D.ClosureSetLattice.inject (r, e, args, body, env, retEnv, exnEnv))

  and eval_prim (prim : C.cps_prim) (env : abstractEnv) (store : abstractStore) : D.ValueLattice.t * abstractStore  * bool = failwith "TODO" in
    (* match prim with *)
    (* | C.GetAttr(_, _, pattr, obj, field) -> *)
    (*   let (obj', bindingStore, retStore, exnStore) =  *)
    (*     eval_val obj env bindingStore retEnv retStore exnEnv exnStore in *)
    (*   let obj' = match obj' with *)
    (*     | V.VarCell (_, _, a) -> Es5_cps_values.Store.find a bindingStore *)
    (*     | _ -> failwith "[cps-interp] set-attr didn't get a VarCell" in *)
    (*   let (field', bindingStore, retStore, exnStore) =  *)
    (*     eval_val field env bindingStore retEnv retStore exnEnv exnStore in *)
    (*   begin match obj', field' with *)
    (*   | V.Object(pos, label, attrs, props), V.String(_, _, s) ->  *)
    (*     begin  *)
    (*       try *)
    (*         match (List.assoc s props), pattr with *)
    (*         | V.Data({ V.value = v }, _, _), E.Value -> (v, bindingStore, retStore, exnStore) *)
    (*         | V.Accessor({ V.getter = g }, _, _), E.Getter -> (g, bindingStore, retStore, exnStore) *)
    (*         | V.Accessor({ V.setter = s }, _, _), E.Setter -> (s, bindingStore, retStore, exnStore) *)
    (*         | V.Data(_, _, config), E.Config -> (D.bool config, bindingStore, retStore, exnStore) *)
    (*         | V.Accessor(_, _, config), E.Config -> (D.bool config, bindingStore, retStore, exnStore) *)
    (*         | V.Data(_, enum, _), E.Enum -> (D.bool enum, bindingStore, retStore, exnStore) *)
    (*         | V.Accessor(_, enum, _), E.Enum -> (D.bool enum, bindingStore, retStore, exnStore) *)
    (*         | V.Data({ V.writable = w }, _, _), E.Writable -> (D.bool w, bindingStore, retStore, exnStore) *)
    (*         | _ -> failwith "bad access of attribute" *)
    (*       with Not_found -> failwith "Field not found" *)
    (*     end *)
    (*   | _ -> failwith "GetAttr didn't have both an object and a string" *)
    (*   end *)
    (* | C.SetAttr(pos, label, pattr, obj, field, value) -> *)
    (*   let (obj', bindingStore, retStore, exnStore) =  *)
    (*     eval_val obj env bindingStore retEnv retStore exnEnv exnStore in *)
    (*   let (obj', addr) = match obj' with *)
    (*     | V.VarCell (_, _, a) -> (Es5_cps_values.Store.find a bindingStore, a) *)
    (*     | _ -> failwith ("[cps-interp] set-attr didn't get a VarCell: " ^ (V.pretty_bind obj')) in *)
    (*   let (field', bindingStore, retStore, exnStore) =  *)
    (*     eval_val field env bindingStore retEnv retStore exnEnv exnStore in *)
    (*   let (value', bindingStore, retStore, exnStore) =  *)
    (*     eval_val value env bindingStore retEnv retStore exnEnv exnStore  in *)
    (*   begin match obj', field' with *)
    (*   | V.Object(pos, label, ({V.extensible = true} as attrs), props), V.String (_, _, s) -> *)
    (*     let newprop = begin *)
    (*       try  *)
    (*         match (List.assoc s props), pattr with *)
    (*         | V.Data ({ V.writable = true } as d, enum, config), E.Writable ->  *)
    (*           V.Data ({ d with V.writable = D.unbool value' }, enum, config) *)
    (*         | V.Data (d, enum, true), E.Writable -> *)
    (*           V.Data ({ d with V.writable = D.unbool value' }, enum, true) *)
    (*         (\* Updating values only checks writable *\) *)
    (*         | V.Data ({ V.writable = true } as d, enum, config), E.Value -> *)
    (*           V.Data ({ d with V.value = value' }, enum, config) *)
    (*         (\* If we had a data property, update it to an accessor *\) *)
    (*         | V.Data (d, enum, true), E.Setter -> *)
    (*           V.Accessor ({ V.getter = V.Undefined(dummy_pos, newLabel()); V.setter = value' }, enum, true) *)
    (*         | V.Data (d, enum, true), E.Getter -> *)
    (*           V.Accessor ({ V.getter = value'; V.setter = V.Undefined(dummy_pos, newLabel()) }, enum, true) *)
    (*         (\* Accessors can update their getter and setter properties *\) *)
    (*         | V.Accessor (a, enum, true), E.Getter -> *)
    (*           V.Accessor ({ a with V.getter = value' }, enum, true) *)
    (*         | V.Accessor (a, enum, true), E.Setter -> *)
    (*           V.Accessor ({ a with V.setter = value' }, enum, true) *)
    (*         (\* An accessor can be changed into a data property *\) *)
    (*         | V.Accessor (a, enum, true), E.Value -> *)
    (*           V.Data ({ V.value = value'; V.writable = false; }, enum, true) *)
    (*         | V.Accessor (a, enum, true), E.Writable -> *)
    (*           V.Data ({ V.value = V.Undefined(dummy_pos, newLabel()); V.writable = D.unbool value'; }, enum, true) *)
    (*         (\* enumerable and configurable need configurable=true *\) *)
    (*         | V.Data (d, _, true), E.Enum -> *)
    (*           V.Data (d, D.unbool value', true) *)
    (*         | V.Data (d, enum, true), E.Config -> *)
    (*           V.Data (d, enum, D.unbool value') *)
    (*         | V.Data (d, enum, false), E.Config -> *)
    (*           (match value' with *)
    (*           | V.False _ -> V.Data (d, enum, false) *)
    (*           | _ -> failwith ("[cps-interp] can't set Config property to true once it's false: " ^ s)) *)
    (*         | V.Accessor (a, enum, true), E.Config -> *)
    (*           V.Accessor (a, enum, D.unbool value') *)
    (*         | V.Accessor (a, enum, true), E.Enum -> *)
    (*           V.Accessor (a, D.unbool value', true) *)
    (*         | V.Accessor (a, enum, false), E.Config -> *)
    (*           (match value' with  *)
    (*           | V.False _ -> V.Accessor(a, enum, false) *)
    (*           | _ -> failwith ("[cps-interp] can't set Config property to true once it's false: " ^ s)) *)
    (*         | _ -> failwith ("[cps-interp] bad property set: " ^ s) *)
    (*       with Not_found -> *)
    (*         let undef () = V.Undefined(pos, newLabel()) in *)
    (*         match pattr with *)
    (*         | E.Getter -> V.Accessor({V.getter = value'; V.setter = undef ()}, false, false) *)
    (*         | E.Setter -> V.Accessor({V.getter = undef (); V.setter = value'}, false, false) *)
    (*         | E.Value -> V.Data({V.value = value'; V.writable = false}, false, false) *)
    (*         | E.Writable -> V.Data({V.value = undef(); V.writable = D.unbool value'}, false, false) *)
    (*         | E.Enum -> V.Data({V.value = undef(); V.writable = false}, D.unbool value', true) *)
    (*         | E.Config -> V.Data({V.value = undef(); V.writable = false}, true, D.unbool value') *)
    (*     end in *)
    (*     let replaceProp ((s, prop) as newProp) props = *)
    (*       let rec help props acc = *)
    (*         match props with *)
    (*         | [] -> List.rev_append acc [newProp] *)
    (*         | ((n, p) as oldProp)::props' -> if (s = n)  *)
    (*           then List.rev_append acc (newProp::props') *)
    (*           else help props' (oldProp::acc) in *)
    (*       help props [] in *)
    (*     let newobj = V.Object(pos, label, attrs, replaceProp (s, newprop) props) in *)
    (*     (D.bool true, (Es5_cps_values.Store.add addr newobj bindingStore), retStore, exnStore) *)
    (*   | V.Object(pos, label, {V.extensible = false}, props), V.String (_, _, s) ->  *)
    (*     failwith "[cps-interp] extending inextensible object" *)
    (*   | _ -> failwith "[cps-interp] set-attr didn't get an object and a string" *)
    (*   end *)
    (* | C.Op1(_, _, op, arg) ->  *)
    (*   let (arg', bindingStore, retStore, exnStore) = eval_val arg env bindingStore retEnv retStore exnEnv exnStore in *)
    (*   (D.op1 op arg' bindingStore, bindingStore, retStore, exnStore) *)
    (* | C.Op2(_, _, op, left, right) ->  *)
    (*   let (left', bindingStore, retStore, exnStore) = eval_val left env bindingStore retEnv retStore exnEnv exnStore in *)
    (*   let (right', bindingStore, retStore, exnStore) = eval_val right env bindingStore retEnv retStore exnEnv exnStore in *)
    (*   (D.op2 op left' right' bindingStore, bindingStore, retStore, exnStore) *)
    (* | C.DeleteField(pos, _, obj, field) ->  *)
    (*   let (obj', bindingStore, retStore, exnStore) = eval_val obj env bindingStore retEnv retStore exnEnv exnStore in *)
    (*   let (obj', addr, retStore, exnStore) = match obj' with *)
    (*     | V.VarCell (_, _, a) -> ((Es5_cps_values.Store.find a bindingStore), a, retStore, exnStore) *)
    (*     | _ -> failwith "[cps-interp] set-attr didn't get a VarCell" in *)
    (*   let (field', bindingStore, retStore, exnStore) = eval_val field env bindingStore retEnv retStore exnEnv exnStore in *)
    (*   begin match obj', field' with *)
    (*   | V.Object(pos, label, attrs, props), V.String (_, _, s) -> *)
    (*     begin  *)
    (*       try *)
    (*         match (List.assoc s props) with *)
    (*         | V.Data (_, _, true) *)
    (*         | V.Accessor (_, _, true) -> *)
    (*           let newObj = V.Object(pos, label, attrs, List.remove_assoc s props) in *)
    (*           (D.bool true, Es5_cps_values.Store.add addr newObj bindingStore, retStore, exnStore) *)
    (*         | _ -> (D.bool false, bindingStore, retStore, exnStore) *)
    (*       with Not_found -> (D.bool false, bindingStore, retStore, exnStore) *)
    (*     end *)
    (*   | _ -> failwith "DeleteField didn't have both an object and a string" *)
    (*   end *)
    (* | C.SetBang(_, _, id, value) ->  *)
    (*   let (value', bindingStore, retStore, exnStore) = eval_val value env bindingStore retEnv retStore exnEnv exnStore in *)
    (*   let addr = IdMap.find id env in *)
    (*   (\* this is for binding sets *)
    (*      let bindings = IdMap.find addr bindingStore in *)
    (*      if (BindingSet.cardinal bindings == 1)  *)
    (*      then (value', IdMap.add addr (BindingSet.singleton value') bindingStore) *)
    (*      else (value', IdMap.add addr (BindingSet.add value' bindings) bindingStore) *\) *)
    (*   (value', Es5_cps_values.Store.add addr value' bindingStore, retStore, exnStore) in *)
  let answerVal = V.ADDRESS.newAddr() in
  let errorVal = V.ADDRESS.newAddr() in
  let bot = D.ValueLattice._Bot () in
  let bindingEnv = IdMap.add "%%ERROR" errorVal (IdMap.add "%%ANSWER" answerVal IdMap.empty) in
  let bindingStore = Es5_cps_values.Store.add errorVal bot (Es5_cps_values.Store.add answerVal bot Es5_cps_values.Store.empty) in
  let answerAddr = V.ADDRESS.newAddr() in
  let retContEnv = IdMap.add "%answer" answerAddr IdMap.empty in
  let retContStore = V.Store.add answerAddr V.Answer V.Store.empty in
  let errorAddr = V.ADDRESS.newAddr() in
  let exnContEnv = IdMap.add "%error" errorAddr IdMap.empty in
  let exnContStore = V.Store.add errorAddr V.Error V.Store.empty in
  let expLab = C.label_of_exp exp in
  let finalLab = C.Label.newLabel() in
  let initEnv = C.LabelMap.singleton expLab (bindingEnv, retContEnv, exnContEnv) in
  let initStore = C.LabelMap.singleton expLab (bindingStore, retContStore, exnContStore) in
  let rec fixpoint eval exp env store =
    let finalAns = getBinding finalLab "%%ANSWER" env store in
    let finalErr = getBinding finalLab "%%ERROR" env store in
    let module FX = FormatExt in
    FX.vert [FX.text "In outer fixpoint,";
             FX.horz [FX.text "ANSWER <="; Es5_cps_absdelta.ValueLattice.pretty finalAns];
             FX.horz [FX.text "ERROR  <="; Es5_cps_absdelta.ValueLattice.pretty finalErr]] Format.str_formatter;
    printf "%s\n" (Format.flush_str_formatter());
    let (env', store', modified) = eval exp finalLab env store in
    if not modified then (printf "Reached outer fixpoint, modified is false\n"; (env', store', finalLab))
    else fixpoint eval exp (joinEnvs env env') (joinStores store store') in
  fixpoint eval_exp exp initEnv initStore






















type env = C.cps_exp IdMap.t

let build expr =
  let v = expr in
  let cfg = G.add_vertex G.empty v in
  let rec build_exp (g : G.t) (env : env) (entry : vert) (exp : Es5_cps.cps_exp) : (G.t * vert) =
    match exp with
  | C.LetValue(pos,l, id, value, exp) -> (g, entry)
  | C.RecValue(pos,l, id, value, exp) -> (g, entry)
  | C.LetPrim(pos,l, id, prim, exp) -> (g, entry)
  | C.LetRetCont(l,ret, arg, retBody, exp) -> (g, entry)
  | C.LetExnCont(l,exn, arg, label, exnBody, exp) -> (g, entry)
  | C.If(pos,l, cond, trueBranch, falseBranch) -> (g, entry)
  | C.AppFun(pos,l, func, ret, exn, args) -> (g, entry)
  | C.AppRetCont(l,ret, arg) -> (g, entry)
  | C.AppExnCont(l,exn, arg, label) -> (g, entry)
  | C.Eval(pos,l, eval) -> (g, entry) in
  fst (build_exp cfg IdMap.empty v expr)

let cpsv_to_string cps_value =
  Es5_cps_pretty.value cps_value Format.str_formatter;
  Format.flush_str_formatter()
module Display = struct
  include G
  let vertex_name v = match v with
  | C.LetValue(pos,l, id, value, exp) -> "LetValue(" ^ id ^ ")"
  | C.RecValue(pos,l, id, value, exp) -> "RecValue(" ^ id ^ ")"
  | C.LetPrim(pos,l, id, prim, exp) -> "LetPrim(" ^ id ^ ")"
  | C.LetRetCont(l,ret, arg, retBody, exp) -> "LetRet(" ^ ret ^ ")"
  | C.LetExnCont(l,exn, arg, label, exnBody, exp) -> "LetExn(" ^ exn ^ ")"
  | C.If(pos,l, cond, trueBranch, falseBranch) -> "If(" ^ (cpsv_to_string cond) ^ ")"
  | C.AppFun(pos,l, func, ret, exn, args) -> "App(" ^ (cpsv_to_string func) ^ ")"
  | C.AppRetCont(l,ret, arg) -> "Ret(" ^ ret ^ ")"
  | C.AppExnCont(l,exn, arg, label) -> "Exn(" ^ exn ^ ", " ^ (cpsv_to_string label) ^ ")"
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
