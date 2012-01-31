open Prelude
module C = Ljs_cps
module D = Ljs_cps_absdelta
module E = Ljs_syntax
module V = Ljs_cps_values
module U = Ljs_cps_util
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

module Ljs_ORDERED_TYPE_DFT = struct
  type t = Jump | IfTrue | IfFalse | Prim (* get/set field?? *)
  let default = Prim
  let compare t1 t2 = Pervasives.compare t1 t2
end

module G = Persistent.Digraph.ConcreteBidirectionalLabeled (Vert_COMPARABLE) (Ljs_ORDERED_TYPE_DFT)

type complete = Ans of D.ValueLattice.t | Err of D.ValueLattice.t
module AddrSet = Set.Make (Ljs_cps_values.ADDRESS)


type abstractEnv = (V.ADDRESS.t IdMap.t * V.retContEnv * V.exnContEnv) C.LabelMap.t
type abstractStore = (D.ValueLattice.t Ljs_cps_values.Store.t * V.retContStore * V.exnContStore) C.LabelMap.t


module ImperativeUnionFind = struct
  module type OrderedType = sig
    type t
    val compare : t -> t -> int
    val toString : t -> string
  end
  module type S = 
    functor (Ord : OrderedType) -> 
      functor (EltMap : Map.S with type key = Ord.t) -> functor (EltSet : Set.S with type elt = Ord.t) -> sig
    type elt = Ord.t
    type t
    val empty : unit -> t
    val find : t -> elt -> elt
    val union : t -> elt -> elt -> unit
    val toEquivClasses : t -> EltSet.t EltMap.t
  end
  module Make (Ord : OrderedType)
    (EltMap : Map.S with type key = Ord.t) (EltSet : Set.S with type elt = Ord.t) = struct
    type elt = Ord.t
    type t = elt EltMap.t ref
    let empty () = ref EltMap.empty
    let find (m : t) (i : elt) =
      let rec find_aux i = 
        try begin
          let link = EltMap.find i !m in
          if link <> i then 
            let rep = find_aux link in
            m := EltMap.add i rep !m;
            rep
          else
            i
        end with Not_found ->
          m := EltMap.add i i !m;
          i in
      find_aux i
    let union m i j =
      let ri = find m i in
      let rj = find m j in
      if ri <> rj then m := EltMap.add ri rj !m;
      ()
    let toEquivClasses m =
      EltMap.fold (fun i _ acc ->
        let ri = find m i in
        let curClass = 
          try EltMap.find ri acc
          with Not_found -> EltSet.empty in
        EltMap.add ri (EltSet.add i curClass) acc) !m EltMap.empty
  end
end



module LabelSet = Set.Make(C.Label) 
module LabelUF = ImperativeUnionFind.Make(C.Label) (C.LabelMap) (LabelSet)
let print_labelmap map = C.LabelMap.iter (fun l set ->
  printf "%s -> \n\t" (C.Label.toString l);
  IdSet.iter (printf "%s ") set;
  printf "\n") map;;
let print_labelmap2 map = C.LabelMap.iter (fun l set ->
  printf "%s -> \n\t" (C.Label.toString l);
  LabelSet.iter (fun x -> printf "%s " (C.Label.toString x)) set;
  printf "\n") map;;
let print_labelmap3 map = C.LabelMap.iter (fun l m ->
  printf "%s -> %s\n" (C.Label.toString l) (C.Label.toString m)) !map;;


let partition_vars e =
  let labelSets = LabelUF.empty () in
  let rec part_exp curL e = match e with
    | C.LetValue (_, l, i, v, b) 
    | C.RecValue (_, l, i, v, b) ->
      part_val curL v;      part_exp curL b;
      LabelUF.union labelSets curL l
    | C.LetPrim (_, l, i, p, b) ->
      part_prim curL p;     part_exp curL b;
      LabelUF.union labelSets curL l
    | C.LetRetCont (l, i, r, b) ->
      part_ret curL r;      part_exp curL b;
      LabelUF.union labelSets curL l
    | C.LetExnCont (l, i, e, b) -> (* only care about user lambda, not continuations *)
      part_exn curL e;      part_exp curL b;
      LabelUF.union labelSets curL l;
    | C.If (_, l, c, t, f) ->
      part_val curL c;      part_exp curL t;      part_exp curL f;
      LabelUF.union labelSets curL l
    | C.AppFun (_, l, f, r, e, args) ->
      part_val curL f; part_ret curL r; part_exn curL e;
      List.iter (part_val curL) args;
      begin match f with
      | C.Lambda _ -> ()
      | _ -> LabelUF.union labelSets curL l
      end
    | C.AppRetCont(l, r, a) ->
      part_val curL a;      part_ret curL r;
      LabelUF.union labelSets curL l
    | C.AppExnCont(l, e, a, lbl) ->
      part_exn curL e;      part_val curL a;      part_val curL lbl;
      LabelUF.union labelSets curL l
    | C.Eval _ -> ()
  and part_ret curL r = match r with
    | C.RetId(l, _) -> LabelUF.union labelSets curL l
    | C.RetLam(l, arg, b) -> part_exp curL b; LabelUF.union labelSets curL l
  and part_exn curL r = match r with
    | C.ExnId(l, _) -> LabelUF.union labelSets curL l
    | C.ExnLam(l, arg, lbl, b) -> part_exp curL b; LabelUF.union labelSets curL l
  and part_val curL v = match v with
    | C.Lambda(_, l, _, _, _, b) ->
      part_exp l b (* ignoring curL, because labels inside lambdas are separate *)
    | C.Object(_, l, attrs, _) ->
      let optval o = match o with
        | None -> ()
        | Some v -> part_val curL v in
      optval attrs.C.primval;      optval attrs.C.code;      optval attrs.C.proto;
      LabelUF.union labelSets curL l
    | C.Null(_, l)
    | C.Undefined(_, l)
    | C.String(_, l, _)
    | C.Num(_, l, _)
    | C.True(_, l)
    | C.False(_, l)
    | C.Id(_, l, _) ->
      LabelUF.union labelSets curL l
  and part_prim curL p = match p with
    | C.GetAttr(_, l, _, o, f) ->
      part_val curL o;      part_val curL f;
      LabelUF.union labelSets curL l
    | C.SetAttr (_, l, _, o, f, v) ->
      part_val curL o;      part_val curL f;      part_val curL v;
      LabelUF.union labelSets curL l
    | C.Op1 (_, l, _, v) ->
      part_val curL v;
      LabelUF.union labelSets curL l
    | C.Op2 (_, l, _, u, v) ->
      part_val curL u;      part_val curL v;
      LabelUF.union labelSets curL l
    | C.MutableOp1 (_, l, _, v) ->
      part_val curL v;
      LabelUF.union labelSets curL l
    | C.DeleteField(_, l, o, f) ->
      part_val curL o;      part_val curL f;
      LabelUF.union labelSets curL l
    | C.SetBang (_, l, _, v) ->
      part_val curL v;
      LabelUF.union labelSets curL l
    | C.OwnFieldNames (_, l, obj) ->
      part_val curL obj;
      LabelUF.union labelSets curL l
  in 

  let rec vars_at_exp e acc = match e with
    | C.LetValue (_, l, i, v, b)
    | C.RecValue (_, l, i, v, b) ->
      vars_at_exp b (vars_at_val v (C.LabelMap.add l (IdSet.singleton i) acc))
    | C.LetPrim (_, l, i, p, b) ->
      vars_at_exp b (vars_at_prim p (C.LabelMap.add l (IdSet.singleton i) acc))
    | C.LetRetCont (l, ret, r, b) -> 
      vars_at_exp b (vars_at_ret r (C.LabelMap.add l (IdSet.singleton ret) acc))
    | C.LetExnCont (l, exn, e, b) ->
      vars_at_exp b (vars_at_exn e (C.LabelMap.add l (IdSet.singleton exn) acc))
    | C.If (_, _, c, t, f) ->
      vars_at_exp f (vars_at_exp t (vars_at_val c acc))
    | C.AppFun (_, _, f, r, e, args) ->
      let flip f x y = f y x in 
      List.fold_left (flip vars_at_val) (vars_at_val f (vars_at_ret r (vars_at_exn e acc))) args
    | C.AppRetCont (_, r, v) -> vars_at_val v (vars_at_ret r acc)
    | C.AppExnCont (_, e, a, l) -> vars_at_val l (vars_at_val a (vars_at_exn e acc))
    | C.Eval _ -> acc
  and vars_at_ret r acc = match r with
    | C.RetId _ -> acc
    | C.RetLam(l, arg, b) -> vars_at_exp b (C.LabelMap.add l (IdSet.singleton arg) acc)
  and vars_at_exn e acc = match e with
    | C.ExnId _ -> acc
    | C.ExnLam(l, arg, lbl, b) -> vars_at_exp b (C.LabelMap.add l (IdSet.add lbl (IdSet.singleton arg)) acc)
  and vars_at_prim p acc = match p with
    | C.GetAttr (_, _, _, o, f) -> vars_at_val f (vars_at_val o acc)
    | C.SetAttr (_, _, _, o, f, v) -> vars_at_val v (vars_at_val f (vars_at_val o acc))
    | C.Op1 (_, _, _, v) -> vars_at_val v acc
    | C.Op2 (_, _, _, l, r) -> vars_at_val r (vars_at_val l acc)
    | C.MutableOp1 (_, _, _, v) -> vars_at_val v acc
    | C.DeleteField (_, _, o, f) -> vars_at_val f (vars_at_val o acc)
    | C.SetBang (_, _, _, v) -> vars_at_val v acc
    | C.OwnFieldNames (_, _, o) -> vars_at_val o acc
  and vars_at_val v acc = match v with
    | C.Lambda (_, l, ret, exn, args, b) -> 
      let flip f x y = f y x in 
      vars_at_exp b (C.LabelMap.add l
                       (List.fold_left (flip IdSet.add) (IdSet.add exn (IdSet.singleton ret)) args) acc)
    | C.Object (_, _, attrs, _) ->
      let optval o acc = match o with
        | None -> acc
        | Some v -> vars_at_val v acc in
      optval attrs.C.primval (optval attrs.C.code (optval attrs.C.proto acc))
    | _ -> acc in

  let equivClasses_to_idSets e =
    (* map from labels that define ids to the set of ids they define*)
    let (labels_to_idSets : IdSet.t C.LabelMap.t) = vars_at_exp e C.LabelMap.empty in
    (* map from each label to the set of ids defined in the equivalence class *)
    C.LabelMap.fold (fun (label : C.Label.t) (set : LabelSet.t) (acc : IdSet.t C.LabelMap.t) ->
      let ids_in_class = (LabelSet.fold (fun label acc ->
        try
          IdSet.union acc (C.LabelMap.find label labels_to_idSets)
        with Not_found -> acc) set IdSet.empty) in
      LabelSet.fold (fun label acc -> C.LabelMap.add label ids_in_class acc) set acc)
      (LabelUF.toEquivClasses labelSets) C.LabelMap.empty in
  part_exp (C.label_of_exp e) e; 
  equivClasses_to_idSets e

let stack_ref var label labelVarMap =
  try
    IdSet.mem var (C.LabelMap.find label labelVarMap)
  with Not_found -> failwith ("Label " ^ (C.Label.toString label) ^ " not found in map!")
let heap_ref var label labelVarMap = not (stack_ref var label labelVarMap)



type userValueMap = D.ValueLattice.t IdMap.t
type localFrame = userValueMap
type localStack = localFrame
type localHeap = userValueMap

type localState =
  | UEval of C.Label.t * C.cps_value * C.cps_ret * C.cps_exn * C.cps_value list * localStack * localHeap
  | UApply of C.Label.t * D.CLOSURE.t * D.ValueLattice.t * D.ValueLattice.t * D.ValueLattice.t list * localStack * localHeap
  | CEval of C.Label.t * C.cps_ret * C.cps_value * localStack * localHeap
  | CApply of C.Label.t * C.cps_ret * D.ValueLattice.t * localStack * localHeap
  (* | ... more to come *)

(* let analyze exp = *)
(*   let labelVarMap = partition_vars exp in *)

(*   let localNextState state = match state with *)
(*     | UEval (l, f, r, e, args, tf, h) -> *)
(*       begin match f with *)
(*       | C.Lambda (_, _, r, e, args, body) -> D.ClosureSet.singleton (r, e, args, body, IdMap.empty, IdMap.empty, IdMap.empty) *)
(*       |  *)
(*       if stack_ref *)



(* **************************************** *)
let print_abs_bindings label env store =
  let (bE, rE, eE) = C.LabelMap.find label env in
  let (bH, rH, eH) = C.LabelMap.find label store in
  printf "Condensed abs bindings at %s:\n" (C.Label.toString label);
  let reachableAddrs : V.ADDRESS.t list ref = ref [] in
  let rootAddrs : V.ADDRESS.t list ref = ref [] in
  let rec addReachable obj = match (D.ValueLattice.addrsOf obj) with
    | D.AddressSetLattice.Set addrs ->
      D.AddressSet.iter (fun a -> 
        reachableAddrs := a::!reachableAddrs;
        addReachable (Ljs_cps_values.Store.find a bH)) addrs
    | _ -> () in
  IdMap.iter (fun id addr ->
    rootAddrs := addr::!rootAddrs;
    try 
      let lookup = Ljs_cps_values.Store.find addr bH in
      addReachable lookup;
      vert[horz[text " "; text id; text "->"; (V.ADDRESS.pretty addr); text "->"; (D.ValueLattice.pretty lookup)]]
        Format.str_formatter;
      printf "%s\n" (Format.flush_str_formatter ())
    with _ -> printf "  %s -> %s -> XXX dangling pointer XXX\n" id (V.ADDRESS.toString addr)) bE;
  List.iter (fun addr ->
    if List.mem addr !rootAddrs then ()
    else begin
      let lookup = Ljs_cps_values.Store.find addr bH in
      vert[horz[text "  ** ->"; (V.ADDRESS.pretty addr); text "->"; (D.ValueLattice.pretty lookup)]]
        Format.str_formatter;
      printf "%s\n" (Format.flush_str_formatter ());
      rootAddrs := addr::!rootAddrs
    end)
    !reachableAddrs

let print_all_abs_bindings store =
  printf "All abs bindings:\n";
  vert (C.LabelMap.fold (fun label (store, _, _) acc ->
    (horz [C.Label.pretty label; text "->";
           braces (vert (Ljs_cps_values.Store.fold (fun addr value acc ->
             (horz [V.ADDRESS.pretty addr; text "->"; D.ValueLattice.pretty value])::acc) store []))])::acc)
          store [])
    Format.str_formatter;
  printf "%s\n" (Format.flush_str_formatter ())
let print_all_abs_env env =
  printf "All abs environments:\n";
  vert (C.LabelMap.fold (fun label (env, _, _) acc ->
    (horz [C.Label.pretty label; text "->";
           braces (vert (IdMap.fold (fun id addr acc ->
             (horz [text id; text "->"; V.ADDRESS.pretty addr])::acc) env []))])::acc) env [])
    Format.str_formatter;
  printf "%s\n" (Format.flush_str_formatter ())

let printAnsErr msg ans err =
  let module FX = FormatExt in
  FX.vert [FX.text (msg ^ ",");
           FX.horz [FX.text "ANSWER <="; Ljs_cps_absdelta.ValueLattice.pretty ans];
           FX.horz [FX.text "ERROR  <="; Ljs_cps_absdelta.ValueLattice.pretty err]] Format.str_formatter;
  printf "%s\n" (Format.flush_str_formatter())
  

(* let print_rets env store =  *)
(*   printf "Condensed returns:\n"; *)
(*   IdMap.iter (fun id addr -> printf "  %s -> %s" id (V.ADDRESS.toString addr); *)
(*     match (Ljs_cps_values.Store.find addr store) with *)
(*     | V.Answer -> printf " -> ANS\n" *)
(*     | V.RetCont(l, arg, _, _,_,_) -> printf " -> RET(%s->...)[...]\n" arg) env *)

(* let print_exns env store =  *)
(*   printf "Error Env:\n"; *)
(*   IdMap.iter (fun id addr -> printf "  %s -> %s\n" id (V.ADDRESS.toString addr)) env; *)
(*   printf "Error Store:\n"; *)
(*   Ljs_cps_values.Store.iter (fun addr ret -> *)
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
let updateValue strong label addr v store =
  try
    let (b, r, e) = C.LabelMap.find label store in
    let b' =
      try
        if strong then
          Ljs_cps_values.Store.add addr v b
        else 
          let oldV = Ljs_cps_values.Store.find addr b in
          Ljs_cps_values.Store.add addr (D.ValueLattice.join [v; oldV]) b
      with _ -> Ljs_cps_values.Store.add addr v b in
    C.LabelMap.add label (b', r, e) store
  with _ -> C.LabelMap.singleton label (Ljs_cps_values.Store.singleton addr v,
                                        V.Store.empty,
                                        V.Store.empty)
let getEnv label env =
  try C.LabelMap.find label env
  with _ -> (IdMap.empty, IdMap.empty, IdMap.empty)
let getStore label store =
  try C.LabelMap.find label store
  with _ -> (Ljs_cps_values.Store.empty, V.Store.empty, V.Store.empty)
let getBinding label id env store = 
  let (b, r, e) = getEnv label env in
  try 
    let addr = IdMap.find id b in
    let (b, r, e) = getStore label store in
    try
      Ljs_cps_values.Store.find addr b
    with Not_found -> D.ValueLattice._Bot ()
  with Not_found -> D.ValueLattice._Bot ()
let getRet label id env store = 
  let (b, r, e) = getEnv label env in
  let addr = IdMap.find id r in
  let (b, r, e) = getStore label store in
  V.Store.find addr r
let getExn label id env store = 
  let (b, r, e) = getEnv label env in
  let addr = IdMap.find id e in
  let (b, r, e) = getStore label store in
  V.Store.find addr e

let updateRet label addr v store =
  try
    let (b, r, e) = C.LabelMap.find label store in
    let r' = V.Store.add addr v r in
    C.LabelMap.add label (b, r', e) store
  with _ -> C.LabelMap.singleton label (Ljs_cps_values.Store.empty,
                                        V.Store.singleton addr v,
                                        V.Store.empty)
let updateExn label addr v store =
  try
    let (b, r, e) = C.LabelMap.find label store in
    let e' = V.Store.add addr v e in
    C.LabelMap.add label (b, r, e') store
  with _ -> C.LabelMap.singleton label (Ljs_cps_values.Store.empty,
                                        V.Store.empty,
                                        V.Store.singleton addr v)
let mergeAbstractStores (b1, r1, e1) (b2, r2, e2) =
  let b = Ljs_cps_values.Store.merge (fun _ v1 v2 ->
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
    with _ -> (Ljs_cps_values.Store.empty, V.Store.empty, V.Store.empty) in
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

let refineStore whichBranch branchLabel cond cond' env store = 
  let condLab = C.label_of_val cond in
  let store' = pushStore condLab branchLabel store in
  match cond with
  | C.Id(_, _, id) -> 
    let (b, _, _) = C.LabelMap.find branchLabel env in
    let addr = IdMap.find id b in
    let store2 = 
      updateValue true branchLabel addr (D.ValueLattice.meet [cond'; D.bool whichBranch]) store' in
    (* (match (D.ValueLattice.boolOf cond') with *)
    (* | D.BoolLattice.TrueTypeof (t, v) -> *)
    (* | D.BoolLattice.FalseTypeof (t, v) -> *)
    (* ) *) (* TODO *)
    store2
  | _ -> store'


let eval (exp : C.cps_exp) : abstractEnv * abstractStore * C.Label.t =
  (* let newLabel = C.newLabel in *)

  (* (\*  *)
  (*  * Garbage collection of the stores, assuming that the provided environments are all the  *)
  (*  * roots that exist.  Similarly, assume that the closed-over environments in closures and *)
  (*  * continuations are themselves gc'ed, so that they only contain reachable information and *)
  (*  * no garbage. *)
  (*  *\) *)
  (* let garbage_collect *)
  (*     bindingEnv (bindingStore : V.bind_value Ljs_cps_values.Store.t) *)
  (*     retContEnv retContStore *)
  (*     exnContEnv exnContStore = *)
  (*   (U.dump_heap_as_dot "before_" bindingEnv bindingStore retContEnv retContStore exnContEnv exnContStore) Format.str_formatter; *)
  (*   print_string (Format.flush_str_formatter ()); *)
  (*   let noIds = AddrSet.empty in *)
  (*   let just addr = AddrSet.singleton addr in *)
  (*   let add addr = AddrSet.add addr in *)
  (*   let (++) l1 l2 = AddrSet.union l1 l2 in *)
  (*   let join (b1, r1, e1) (b2, r2, e2) = (b1++b2, r1++r2, e1++e2) in *)
  (*   let lookup addr store = try Some (Ljs_cps_values.Store.find addr store) with _ -> None in *)
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
  (*         Ljs_cps_values.Store.remove addr acc) *)
  (*   ) in *)
  (*   let (newBindings, newRets, newExns) = *)
  (*     (Ljs_cps_values.Store.fold (filter_sto "bindings" V.pretty_bind reachable_bind_addrs)  *)
  (*        bindingStore bindingStore, *)
  (*      Ljs_cps_values.Store.fold (filter_sto "retconts" V.pretty_retcont reachable_ret_addrs)  *)
  (*        retContStore retContStore, *)
  (*      Ljs_cps_values.Store.fold (filter_sto "exnconts" V.pretty_exncont reachable_exn_addrs)  *)
  (*        exnContStore exnContStore) in *)
  (*   (U.dump_heap_as_dot "after_" bindingEnv newBindings retContEnv newRets exnContEnv newExns) Format.str_formatter; *)
  (*   (newBindings, newRets, newExns) in *)
  let printModReasons label reasons = 
    let module FX = FormatExt in
    FX.vert ((FX.horz [FX.text "For label"; C.Label.pretty label])::
                (List.map (fun (n,b) -> FX.horz [FX.text n; FX.text "="; if b then FX.text "true" else FX.text "false"]) reasons))
      Format.str_formatter;
    printf "%s\n" (Format.flush_str_formatter ()) in
  let rec eval_exp exp (exitLab : C.Label.t) (env : abstractEnv) (store : abstractStore) : abstractEnv * abstractStore * bool = 
    print_string "In eval_exp for ";
    let label = (match exp with
    | C.LetValue (_, l, id, _, _) -> printf "%s" ("LetValue " ^ (C.Label.toString l) ^ "," ^ id ^ "\n"); l
    | C.RecValue (_, l, id, _, _) -> printf "%s" ("RecValue " ^ (C.Label.toString l) ^ "," ^ id ^ "\n"); l
    | C.LetPrim (_, l, id, _, _) -> printf "%s" ("LetPrim " ^ (C.Label.toString l) ^ "," ^ id ^ "\n"); l
    | C.LetRetCont (l, id, _, _) -> printf "%s" ("LetRetCont " ^ (C.Label.toString l) ^ "," ^ id ^ "\n"); l
    | C.LetExnCont (l, id, _, _) -> printf "%s" ("LetExnCont " ^ (C.Label.toString l) ^ "," ^ id ^ "\n"); l
    | C.AppRetCont (l, _, _) -> printf "%s" ("AppRetCont " ^ (C.Label.toString l) ^ "\n"); l
    | C.AppExnCont (l, _, _, _) -> printf "%s" ("AppExnCont " ^ (C.Label.toString l) ^ "\n"); l
    | C.AppFun (_, l, f, r, e, a) -> printf "%s %s(Ret XXX, Exn XXX; %s)\n" ("AppFun " ^ (C.Label.toString l))
      (Ljs_cps_pretty.cps_value_to_string f) (String.concat ", " (List.map Ljs_cps_pretty.cps_value_to_string a)); l
    | C.If(_, l, _, _, _) -> printf "%s" ("If " ^ (C.Label.toString l) ^ "\n"); l
    | C.Eval(_, l, _) -> printf "%s" ("Eval " ^ (C.Label.toString l) ^ "\n"); l
    ) in
    print_abs_bindings label env store;
    match exp with
    | C.LetValue(pos, label, id, value, body) ->
      let blab = C.label_of_exp body in
      let oldValue = getBinding blab id env store in
      let store' = pushStore label (C.label_of_val value) store in
      let env' = copyEnv label (C.label_of_val value) env in
      let value' = eval_val value env' store' in
      printf "Pushing env/store from %s to %s\n" (C.Label.toString label) (C.Label.toString(C.label_of_val value));
      printf "Env/store for value:%s:\n" (C.Label.toString (C.label_of_val value));
      print_abs_bindings (C.label_of_val value) env' store';
      V.ADDRESS.resetForContour [label];
      let addr = V.ADDRESS.addrForContour [label] in
      let env'' = (addBinding blab id addr (copyEnv (C.label_of_val value) blab env')) in
      let store'' = (updateValue false blab addr value' (pushStore (C.label_of_val value) blab store')) in
      printf "Pushing env/store from %s to %s\n" (C.Label.toString (C.label_of_val value)) (C.Label.toString blab);
      printf "Env/store for body:%s:\n" (C.Label.toString blab);
      print_abs_bindings blab env'' store'';
      let (env3, store3, bodyMod) = eval_exp body exitLab env'' store'' in
      printModReasons label ["bodyMod", bodyMod; "oldValue <> value'", oldValue <> value'];
      printAnsErr "After LetValue" (getBinding exitLab "%%ANSWER" env3 store3) (getBinding exitLab "%%ERROR" env3 store3);
      ((joinEnvs env'' env3), (joinStores store'' store3), (bodyMod || (oldValue <> value')))
    | C.RecValue(pos, label, id, value, body) ->
      let oldValue = eval_val value env store in
      let vlab = C.label_of_val value in
      let blab = C.label_of_exp body in
      let store' = pushStore label vlab store in
      V.ADDRESS.resetForContour [label];
      let addr = V.ADDRESS.addrForContour [label] in
      let env' = addBinding vlab id addr (copyEnv label vlab env) in
      let rec fixpoint bot store =
        let value' = eval_val value env' store in
        if (bot = value') 
        then begin
          printf "Finished with inner fixpoint\n";
          (value', store)
        end 
        else begin
          (* let module FX = FormatExt in *)
          (* FX.vert [FX.text "In inner fixpoint,"; *)
          (*          FX.horz [FX.text "oldValue <="; Ljs_cps_absdelta.ValueLattice.pretty oldValue]; *)
          (*          FX.horz [FX.text "value' <="; Ljs_cps_absdelta.ValueLattice.pretty value']] Format.str_formatter; *)
          (* printf "%s\n" (Format.flush_str_formatter()); *)
          let widened = (D.ValueLattice.join [bot;value']) in
          fixpoint widened (updateValue false vlab addr widened store) 
        end in
      let (value', store'') = 
        fixpoint (D.ValueLattice._Bot ()) (updateValue false vlab addr (D.ValueLattice._Bot ()) store') in
      let (env3, store3, bodyMod) = eval_exp body exitLab (copyEnv vlab blab env') (pushStore vlab blab store'') in
      printModReasons label ["bodyMod", bodyMod; "value' <> oldValue", value' <> oldValue];
      printAnsErr "After RecValue" (getBinding exitLab "%%ANSWER" env3 store3) (getBinding exitLab "%%ERROR" env3 store3);
      ((joinEnvs env' env3), (joinStores store'' store3), (bodyMod || (value' <> oldValue)))
    | C.LetPrim(pos, label, id, prim, body) ->
      let oldValue = getBinding label id env store in
      let plab = C.label_of_prim prim in
      let blab = C.label_of_exp body in
      let store' = pushStore label plab store in
      V.ADDRESS.resetForContour [label];
      let addr = V.ADDRESS.addrForContour [label] in
      let env' = addBinding plab id addr (copyEnv label plab env) in
      let (value', store'', primMod) = eval_prim prim env' store' in
      V.ADDRESS.resetForContour [label];
      let addr = V.ADDRESS.addrForContour [label] in
      let env'' = (addBinding blab id addr (copyEnv plab blab env')) in
      let store3 = (updateValue false blab addr value' (pushStore plab blab store'')) in
      let (env3, store4, bodyMod) = eval_exp body exitLab env'' store3 in
      printModReasons label ["bodyMod", bodyMod; "primMod", primMod; "value' <> oldValue", value' <> oldValue];
      ((joinEnvs env'' env3), (joinStores store3 store4), (primMod || bodyMod || (oldValue <> value')))
    | C.LetRetCont(label, id, ret, exp) ->
      (* let (bindingStore, retContStore, exnContStore) = *)
      (*   garbage_collect bindingEnv bindingStore retContEnv retContStore exnContEnv exnContStore in *)
      let elab = C.label_of_exp exp in
      let ret = match ret with
        | C.RetId(_, r) -> getRet label r env store
        | C.RetLam(_, arg, body) -> 
          let (b, r, e) = getEnv label env in
          V.RetCont(label, arg, body, b, r, e) in
      let addr = V.ADDRESS.newAddr() in (* Choose not to lose any precision on ret-cont allocation *)
      let env' = (addRet elab id addr (copyEnv label elab env)) in
      let store' = (updateRet elab addr ret (pushStore label elab store)) in
      (* print_rets retEnv' retStore'; *)
      eval_exp exp exitLab env' store'
    | C.AppRetCont(label, r, value) ->
      (* print_rets retContEnv retContStore; *)
      let oldValue = eval_val value env store in
      let store' = pushStore label (C.label_of_val value) store in
      let env' = copyEnv label (C.label_of_val value) env in
      let value' = eval_val value env' store' in
      let (bindingEnv, retContEnv, _) = getEnv label env in
      let (bindingStore, retContStore, _) = getStore label store in
      let ret = match r with
        | C.RetId(_, id) -> V.Store.find (IdMap.find id retContEnv) retContStore 
        | C.RetLam(_, arg, body) -> let (b, r, e) = getEnv label env in V.RetCont(label, arg, body, b, r, e) in
      begin match ret with
      | V.Answer -> 
        let finalAns = (match (D.ValueLattice.addrsOf value') with
          | D.AddressSetLattice.Set addrs ->
            let deref = D.ValueLattice.join (List.map (fun addr -> Ljs_cps_values.Store.find addr bindingStore)
                                               (D.AddressSetLattice.elements addrs)) in
            D.ValueLattice.join [deref; value']
          | a -> value'
        ) in
        let finalErr = getBinding exitLab "%%ERROR" env' store' in
        printAnsErr "At V.Answer" finalAns finalErr;
        let answerVal = IdMap.find "%%ANSWER" bindingEnv in
        (env', updateValue false exitLab answerVal finalAns store', value' <> oldValue)
      | V.RetCont (_, arg, body, bindingEnv, retContEnv, exnContEnv) ->
        V.ADDRESS.resetForContour [label];
        let addr = V.ADDRESS.addrForContour [label] in
        let blab = C.label_of_exp body in
        let env'' = (addBinding blab arg addr (copyEnv label blab env')) in
        let store'' = (updateValue false blab addr value' (pushStore label blab store')) in
        let finalErr = getBinding exitLab "%%ERROR" env'' store'' in
        printAnsErr "At V.RetCont" value' finalErr;
        let (env3, store3, modRet) = eval_exp body exitLab env'' store'' in
        ((joinEnvs env'' env3), (joinStores store'' store3), (modRet || value' <> oldValue))
      end
    | C.LetExnCont(label, id, exn, exp) ->
      (* let (bindingStore, retContStore, exnContStore) = *)
      (*   garbage_collect bindingEnv bindingStore retContEnv retContStore exnContEnv exnContStore in *)
      let elab = C.label_of_exp exp in
      let exn = match exn with
        | C.ExnId(_, id) -> getExn label id env store
        | C.ExnLam(_, arg, lbl, body) ->
          let (b, r, e) = getEnv label env in
          V.ExnCont(label, arg, lbl, body, b, r, e) in
      let addr = V.ADDRESS.newAddr() in (* Choose not to lose any precision on exn-cont allocation *)
      let env' = (addExn elab id addr (copyEnv label elab env)) in
      let store' = (updateExn elab addr exn (pushStore label elab store)) in
      (* print_exns retEnv' retStore'; *)
      eval_exp exp exitLab env' store'
    | C.AppExnCont(label, e, arg, lbl) ->
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
      let exn = match e with
        | C.ExnId(_, id) -> V.Store.find (IdMap.find id exnContEnv) exnContStore 
        | C.ExnLam(_, arg, lbl, body) -> let (b, r, e) = getEnv label env in 
                                         V.ExnCont(label, arg, lbl, body, b, r, e) in
      begin match exn with
      | V.Error -> 
        let oldFinalErr = getBinding exitLab "%%ERROR" env store in
        let finalErr = (match (D.ValueLattice.addrsOf arg') with
          | D.AddressSetLattice.Set addrs ->
            let deref = D.ValueLattice.join (List.map (fun addr -> Ljs_cps_values.Store.find addr bindingStore)
                                               (D.AddressSetLattice.elements addrs)) in
            D.ValueLattice.join [deref; arg']
          | a -> arg'
        ) in
        printf "%s Throwing %s to %s\n" (C.Label.toString label) (D.ValueLattice.pretty finalErr Format.str_formatter; Format.flush_str_formatter()) (C.Label.toString exitLab);
        let errorVal = IdMap.find "%%ERROR" bindingEnv in
        (envLbl, updateValue false exitLab errorVal finalErr storeLbl, finalErr <> oldFinalErr)
      | V.ExnCont(_, arg, lbl, body, bindingEnv, retContEnv, exnContEnv) ->
        V.ADDRESS.resetForContour [label];
        let argAddr = V.ADDRESS.addrForContour [label] in
        let lblAddr = V.ADDRESS.addrForContour [label] in
        let blab = C.label_of_exp body in
        let env'' = (addBinding blab arg argAddr 
                       (addBinding blab lbl lblAddr (copyEnv label blab envLbl))) in
        let store'' = (updateValue false blab argAddr arg' 
                         (updateValue false blab lblAddr lbl' (pushStore label blab storeLbl))) in
        let (env3, store3, modExn) = eval_exp body exitLab env'' store'' in
        ((joinEnvs env'' env3), (joinStores store'' store3), (modExn || arg' <> oldArg || lbl' <> oldLbl))
      end
    | C.If(pos, label, cond, left, right) ->
      let oldCond = eval_val cond env store in
      let store' = pushStore label (C.label_of_val cond) store in
      let env' = copyEnv label (C.label_of_val cond) env in
      let cond' = eval_val cond env' store' in
      let condAsBool = D.ValueLattice.boolOf cond' in
      let (leftEnv', leftStore', leftMod) = match condAsBool with
        | D.BoolLattice.Bool
        | D.BoolLattice.True
        | D.BoolLattice.TrueTypeof _ ->
          let leftEnv = copyEnv label (C.label_of_exp left) env in
          let leftStore = refineStore true (C.label_of_exp left) cond cond' leftEnv store' in
          (eval_exp left exitLab leftEnv leftStore)
        | _ -> (env', store', false) in
      let (rightEnv', rightStore', rightMod) = match condAsBool with
        | D.BoolLattice.True
        | D.BoolLattice.TrueTypeof _ -> (env', store', false)
        | _ ->
          let rightEnv = copyEnv label (C.label_of_exp right) env in
          let rightStore = refineStore false (C.label_of_exp right) cond cond' rightEnv store' in
          (eval_exp right exitLab rightEnv rightStore) in
      ((joinEnvs leftEnv' rightEnv'), 
       (joinStores leftStore' rightStore'), 
       (leftMod || rightMod || (oldCond <> cond')))
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
        (arg'::args, argsMod || oldArg <> arg', joinEnvs envArg envArg', joinStores storeArg storeArg')
      ) ([], false, env1, store1) args in
      begin
        let args' = List.rev args' in
        let (bindingEnv, retContEnv, exnContEnv) = getEnv label env in
        let (bindingStore, retContStore, exnContStore) = getStore label store in
        let ret' = match ret with
          | C.RetId(_, r) -> getRet label r env store
          | C.RetLam(_, arg, body) -> 
            let (b, r, e) = getEnv label env in
            V.RetCont(label, arg, body, b, r, e) in
        let exn' = match exn with
          | C.ExnId(_, id) -> V.Store.find (IdMap.find id exnContEnv) exnContStore 
          | C.ExnLam(_, arg, lbl, body) -> let (b, r, e) = getEnv label env in 
                                           V.ExnCont(label, arg, lbl, body, b, r, e) in
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
            let store' = List.fold_left (fun store (addr, value) -> updateValue false blab addr value store)
              (pushStore label blab store2) (List.combine argAddrs args') in
            let env'' = addRet blab retArg retAddr (addExn blab exnArg exnAddr env') in
            let store'' = updateRet blab retAddr ret' (updateExn blab exnAddr exn' store') in
            (eval_exp body exitLab env'' store'')::acc
          ) closures [] in
        let (e, s, m) = 
          List.fold_left (fun (e1, s1, m1) (e2, s2, m2) -> (joinEnvs e1 e2, joinStores s1 s2, m1 || m2)) 
            (env2, store2, oldFunc <> func' || argsMod) closureResults in
        printAnsErr "After AppFun" (getBinding exitLab "%%ANSWER" e s) (getBinding exitLab "%%ERROR" e s);
        (e, s, m)
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
      VL.injectObj (D.ObjLattice.Obj (a', ps'))  (* XXXXXXXXXX WRONG: Need to return a reference cell to this object! *)
    | C.Lambda(_, label, r, e, args, body) -> 
      (* let (bindingStore, retStore, exnStore) = *)
      (*   garbage_collect env bindingStore retEnv retStore exnEnv exnStore in *)
      let (env, retEnv, exnEnv) = getEnv label env in
      VL.injectClosure (D.ClosureSetLattice.inject (r, e, args, body, env, retEnv, exnEnv))

  and eval_prim (prim : C.cps_prim) (env : abstractEnv) (store : abstractStore) : D.ValueLattice.t * abstractStore  * bool = 
    (let pretty_val v = Ljs_cps_pretty.value false v Format.str_formatter; Format.flush_str_formatter() in
      match prim with
      | C.GetAttr(_, l, a, o, f) -> printf "%s GetAttr %s[%s<%s>]\n" (C.Label.toString l) (pretty_val o) (E.string_of_attr a) (pretty_val f)
      | C.SetAttr(_, l, a, o, f, v) -> printf "%s SetAttr %s[%s<%s> = %s]\n" (C.Label.toString l) (pretty_val o) (E.string_of_attr a) (pretty_val f) (pretty_val v)
      | C.DeleteField(_, l, o, f) -> printf "%s DeleteField %s[%s]\n" (C.Label.toString l) (pretty_val o) (pretty_val f)
      | C.Op1(_, l, o, a) -> printf "%s Op1(%s, %s)\n" (C.Label.toString l) o (pretty_val a)
      | C.Op2(_, l, o, a, b) -> printf "%s Op2(%s, %s, %s)\n" (C.Label.toString l) o (pretty_val a) (pretty_val b)
      | C.MutableOp1(_, l, o, a) -> printf "%s MutableOp1(%s, %s)\n" (C.Label.toString l) o (pretty_val a)
      | C.SetBang(_, l, i, v) -> printf "%s Set!(%s = %s)\n" (C.Label.toString l) i (pretty_val v)
      | C.OwnFieldNames(_, l, o) -> printf "%s GetOwnFieldNames(%s)\n" (C.Label.toString l) (pretty_val o)
    );
    match prim with
    | C.GetAttr(_, label, pattr, obj, field) ->
      let module VL = D.ValueLattice in
      let module ASL = D.AddressSetLattice in
      let module SL = D.StringLattice in
      let module OL = D.ObjLattice in
      let oldObj = eval_val obj env store in
      let envObj = copyEnv label (C.label_of_val obj) env in
      let storeObj = pushStore label (C.label_of_val obj) store in
      let obj' = eval_val obj envObj storeObj in begin
        match (VL.addrsOf obj') with
        | ASL.Top -> (VL._Top (), storeObj, oldObj <> obj')
        | ASL.Bot -> (VL._Bot (), storeObj, oldObj <> obj')
        | ASL.Set addrs -> 
          let oldField = eval_val field env store in
          let envField = copyEnv label (C.label_of_val field) envObj in
          let storeField = pushStore label (C.label_of_val field) storeObj in
          let field' = eval_val field envField storeField in
          match (VL.strOf field') with
          | SL.Bot -> (VL._Bot(), storeField, oldObj <> obj' || oldField <> field')
          | fieldStr ->
            let (bindingStore, _, _) = getStore label storeField in
            let addrResults = D.AddressSet.fold (fun addr acc -> 
              let obj' = Ljs_cps_values.Store.find addr bindingStore in
              match (VL.objOf obj') with
              | OL.Bot -> VL._Bot ()
              | OL.Top -> VL._Top ()
              | OL.Obj (_, props) ->
                let possibleFieldValue = 
                  IdMap.fold (fun s prop acc ->
                    let sStr = SL.inject s in
                    let candidate = SL.meet [sStr; fieldStr] in
                    if (sStr = candidate) 
                    then begin (* fieldStr could be s *)
                      let valueToJoin = match prop, pattr with
                        | OL.Data({ OL.value = v}, _, _), E.Value -> v
                        | OL.Data({ OL.writable = w }, _, _), E.Writable -> VL.injectBool w
                        | OL.Accessor({ OL.getter = g }, _, _), E.Getter -> g
                        | OL.Accessor({ OL.setter = s }, _, _), E.Setter -> s
                        | OL.Data(_, _, config), E.Config -> VL.injectBool config
                        | OL.Accessor(_, _, config), E.Config -> VL.injectBool config
                        | OL.Data(_, enum, _), E.Enum -> VL.injectBool enum
                        | OL.Accessor(_, enum, _), E.Enum -> VL.injectBool enum
                        | _ -> VL._Bot() in
                      VL.join [valueToJoin; acc]
                    end
                    else begin (* whatever fieldStr is, it isn't compatible with s *)
                      acc
                    end) props (VL._Bot ())
                in VL.join [possibleFieldValue; acc]
            ) addrs (VL._Bot ()) in
            (addrResults, storeField, oldObj <> obj' || oldField <> field')
      end
    | C.SetAttr(pos, label, pattr, obj, field, value) ->
      let module VL = D.ValueLattice in
      let module ASL = D.AddressSetLattice in
      let module SL = D.StringLattice in
      let module OL = D.ObjLattice in
      let oldObj = eval_val obj env store in
      let envObj = copyEnv label (C.label_of_val obj) env in
      let storeObj = pushStore label (C.label_of_val obj) store in
      let obj' = eval_val obj envObj storeObj in begin
        match (VL.addrsOf obj') with
        | ASL.Top -> (VL._Top (), storeObj, oldObj <> obj')
        | ASL.Bot -> (VL._Bot (), storeObj, oldObj <> obj')
        | ASL.Set addrs -> 
          let strongUpdate = D.AddressSet.cardinal addrs = 1 in
          let oldField = eval_val field env store in
          let envField = copyEnv label (C.label_of_val field) envObj in
          let storeField = pushStore label (C.label_of_val field) storeObj in
          let field' = eval_val field envField storeField in
          begin match (VL.strOf field') with
          | SL.Bot -> (VL._Bot(), storeField, oldObj <> obj' || oldField <> field')
          | SL.String
          | SL.UintString
          | SL.NonUintString ->
            let (store3, modified) = D.AddressSet.fold (fun addr (storeAcc, modAcc) ->
              let (bindingStore, _, _) = getStore label storeAcc in
              let obj' = Ljs_cps_values.Store.find addr bindingStore in
              match (VL.objOf obj') with
              | OL.Bot -> (storeAcc, modAcc)
              | OL.Top -> (storeAcc, modAcc)
              | OL.Obj _ -> (updateValue strongUpdate label addr (VL.injectObj (OL._Top ())) storeAcc, true)
            ) addrs (storeField, false) in
            (D.bool true, store3, modified)
          | fieldStr ->
            let s = (match fieldStr with
              | SL.ConcreteUint s
              | SL.ConcreteNonUint s -> s
              | SL.TypeofString (t, _) -> SL.stringofTypeof t
              | _ -> failwith "Impossible case -- we've already matched these away") in
            let oldValue = eval_val value env store in
            let envValue = copyEnv label (C.label_of_val value) envField in
            let storeValue = pushStore label (C.label_of_val value) storeField in
            let value' = eval_val value envValue storeValue in
            let trueEnough b = match b with
              | D.BoolLattice.Bool
              | D.BoolLattice.True
              | D.BoolLattice.TrueTypeof _ -> true
              | _ -> false in
            let (store3, modified) = D.AddressSet.fold (fun addr (store, modified) -> 
              let (bindingStore, _, _) = getStore label store in
              let obj' = Ljs_cps_values.Store.find addr bindingStore in
              match (VL.objOf obj') with
              | OL.Bot
              | OL.Top -> (store, modified)
              | OL.Obj ({OL.extensible = b} as attrs, props) when trueEnough b ->
                let undef = VL.injectUndef (D.UndefLattice._Top ()) in
                let bool = D.BoolLattice.inject in
                let (newprop, modified') = begin
                  try
                    let oldprop = IdMap.find s props in
                    let newprop = match oldprop, pattr with
                      | OL.Data ({ OL.writable = b } as d, enum, config), E.Writable when trueEnough b ->
                        OL.Data ({ d with OL.writable = VL.boolOf value' }, enum, config)
                      | OL.Data (d, enum, b), E.Writable when trueEnough b ->
                        OL.Data ({ d with OL.writable = VL.boolOf value' }, enum, bool true)
                      (* Updating values only checks writable *)
                      | OL.Data ({ OL.writable = b } as d, enum, config), E.Value when trueEnough b ->
                        OL.Data ({ d with OL.value = value' }, enum, config)
                      (* If we had a data property, update it to an accessor *)
                      | OL.Data (d, enum, c), E.Setter when trueEnough c ->
                        OL.Accessor ({ OL.getter = undef; OL.setter = value' }, 
                                     enum, bool true)
                      | OL.Data (d, enum, c), E.Getter when trueEnough c ->
                        OL.Accessor ({ OL.getter = value'; OL.setter = undef }, 
                                     enum, bool true)
                      (* Accessors can update their getter and setter properties *)
                      | OL.Accessor (a, enum, c), E.Getter when trueEnough c ->
                        OL.Accessor ({ a with OL.getter = value' }, enum, bool true)
                      | OL.Accessor (a, enum, c), E.Setter when trueEnough c ->
                        OL.Accessor ({ a with OL.setter = value' }, enum, bool true)
                      (* An accessor can be changed into a data property *)
                      | OL.Accessor (a, enum, c), E.Value when trueEnough c ->
                        OL.Data ({ OL.value = value'; OL.writable = bool false; }, enum, bool true)
                      | OL.Accessor (a, enum, c), E.Writable when trueEnough c->
                        OL.Data ({ OL.value = undef; OL.writable = VL.boolOf value' }, enum, bool true)
                      (* enumerable and configurable need configurable=true *)
                      | OL.Data (d, _, c), E.Enum when trueEnough c ->
                        OL.Data (d, VL.boolOf value', bool true)
                      | OL.Data (d, enum, c), E.Config when trueEnough c ->
                        OL.Data (d, enum, VL.boolOf value')
                      | OL.Data (d, enum, _), E.Config ->
                        (match (VL.boolOf value') with
                        | D.BoolLattice.False
                        | D.BoolLattice.FalseTypeof _ -> OL.Data (d, enum, bool false)
                        | D.BoolLattice.Bot -> OL.Unknown
                        | _ -> OL.PropTop)
                      | OL.Accessor (a, enum, c), E.Config when trueEnough c ->
                        OL.Accessor (a, enum, VL.boolOf value')
                      | OL.Accessor (a, enum, c), E.Enum when trueEnough c ->
                        OL.Accessor (a, VL.boolOf value', bool true)
                      | OL.Accessor (a, enum, _), E.Config ->
                        (match (VL.boolOf value') with
                        | D.BoolLattice.False
                        | D.BoolLattice.FalseTypeof _ -> OL.Accessor(a, enum, bool false)
                        | D.BoolLattice.Bot -> OL.Unknown
                        | _ -> OL.PropTop)
                      | _ -> OL.PropTop in
                    (newprop, newprop <> oldprop)
                  with Not_found ->
                    let newprop = match pattr with
                      | E.Getter -> OL.Accessor({OL.getter = value'; OL.setter = undef}, 
                                                bool false, bool false)
                      | E.Setter -> OL.Accessor({OL.getter = undef; OL.setter = value'}, 
                                                bool false, bool false)
                      | E.Value -> OL.Data({OL.value = value'; OL.writable = bool false}, 
                                           bool false, bool false)
                      | E.Writable -> OL.Data({OL.value = undef; OL.writable = VL.boolOf value'}, 
                                              bool false, bool false)
                      | E.Enum -> OL.Data({OL.value = undef; OL.writable = bool false}, 
                                          VL.boolOf value', bool true)
                      | E.Config -> OL.Data({OL.value = undef; OL.writable = bool false}, 
                                            bool true, VL.boolOf value')
                    in (newprop, true)
                end in
                let newProps = IdMap.add s newprop props in
                let newObj = OL.Obj(attrs, newProps) in
                let newStore = updateValue strongUpdate label addr (VL.injectObj newObj) store in
                (newStore, modified || modified')
              | _ -> (store, modified)
            ) addrs (storeValue, false) in
            (D.bool true, store3, modified || oldValue <> value' || oldField <> field')
          end
      end
    | C.Op1(_, label, op, arg) ->
      let oldArg = eval_val arg env store in
      let envArg = copyEnv label (C.label_of_val arg) env in
      let storeArg = pushStore label (C.label_of_val arg) store in
      let arg' = eval_val arg envArg storeArg in
      let (bindingStore, _, _) = getStore label storeArg in
      printModReasons label ["oldArg <> arg'", arg' <> oldArg];
      (D.op1 op arg' bindingStore, storeArg, oldArg <> arg')
    | C.OwnFieldNames _ -> failwith "[cfg_abs] OwnFieldNames NYI"
    | C.MutableOp1(_, label, op, arg) ->
      let oldArg = eval_val arg env store in
      let envArg = copyEnv label (C.label_of_val arg) env in
      let storeArg = pushStore label (C.label_of_val arg) store in
      let arg' = eval_val arg envArg storeArg in
      let (value', store', modified) = D.mutableOp1 label getStore updateValue op arg' storeArg in
      (arg', store', modified || oldArg <> arg')
    | C.Op2(_, label, op, left, right) ->
      print_all_abs_bindings store;
      let oldLeft = eval_val left env store in
      let envLeft = copyEnv label (C.label_of_val left) env in
      let storeLeft = pushStore label (C.label_of_val left) store in
      let left' = eval_val left envLeft storeLeft in
      let oldRight = eval_val right env store in
      let envRight = copyEnv label (C.label_of_val right) envLeft in
      let storeRight = pushStore label (C.label_of_val right) storeLeft in
      let right' = eval_val right envRight storeRight in
      let (bindingStore, _, _) = getStore label storeRight in
      let module FX = FormatExt in
      FX.vert [FX.text "In prim_op2,";
               FX.horz [FX.text "oldLeft <="; Ljs_cps_absdelta.ValueLattice.pretty oldLeft];
               FX.horz [FX.text "left' <="; Ljs_cps_absdelta.ValueLattice.pretty left'];
               FX.horz [FX.text "oldRight <="; Ljs_cps_absdelta.ValueLattice.pretty oldRight];
               FX.horz [FX.text "right' <="; Ljs_cps_absdelta.ValueLattice.pretty right']] Format.str_formatter;
      printf "%s\n" (Format.flush_str_formatter());
      printModReasons label ["oldLeft<>left'", oldLeft <> left'; "oldRight<>right'", oldRight <> right'];
      (D.op2 op left' right' bindingStore, storeRight, oldLeft <> left' || oldRight <> right')
    | C.DeleteField(_, label, obj, field) ->
      let module VL = D.ValueLattice in
      let module ASL = D.AddressSetLattice in
      let module SL = D.StringLattice in
      let module OL = D.ObjLattice in
      let oldObj = eval_val obj env store in
      let envObj = copyEnv label (C.label_of_val obj) env in
      let storeObj = pushStore label (C.label_of_val obj) store in
      let obj' = eval_val obj envObj storeObj in begin
        match (VL.addrsOf obj') with
        | ASL.Top -> (VL._Top (), storeObj, oldObj <> obj')
        | ASL.Bot -> (VL._Bot (), storeObj, oldObj <> obj')
        | ASL.Set addrs -> 
          let strongUpdate = D.AddressSet.cardinal addrs = 1 in
          let oldField = eval_val field env store in
          let envField = copyEnv label (C.label_of_val field) envObj in
          let storeField = pushStore label (C.label_of_val field) storeObj in
          let field' = eval_val field envField storeField in
          begin match (VL.strOf field') with
          | SL.Bot -> (VL._Bot(), storeField, oldObj <> obj' || oldField <> field')
          | SL.String
          | SL.UintString
          | SL.NonUintString ->
            let (store3, modified) = D.AddressSet.fold (fun addr (storeAcc, modAcc) ->
              let (bindingStore, _, _) = getStore label storeAcc in
              let obj' = Ljs_cps_values.Store.find addr bindingStore in
              match (VL.objOf obj') with
              | OL.Bot -> (storeAcc, modAcc)
              | OL.Top -> (storeAcc, modAcc)
              | OL.Obj _ -> (updateValue strongUpdate label addr (VL.injectObj (OL._Top ())) storeAcc, true)
            ) addrs (storeField, false) in
            (obj', store3, modified)
          | fieldStr ->
            let s = (match fieldStr with
              | SL.ConcreteUint s
              | SL.ConcreteNonUint s -> s
              | SL.TypeofString (t, _) -> SL.stringofTypeof t
              | _ -> failwith "Impossible case -- we've already matched these away") in
            let trueEnough b = match b with
              | D.BoolLattice.Bool
              | D.BoolLattice.True
              | D.BoolLattice.TrueTypeof _ -> true
              | _ -> false in
            let (store3, modified) = D.AddressSet.fold (fun addr (store, modified) ->
              let (bindingStore, _, _) = getStore label store in
              let obj' = Ljs_cps_values.Store.find addr bindingStore in
              match (VL.objOf obj') with
              | OL.Bot
              | OL.Top -> (storeField, oldObj <> obj' || oldField <> oldField)
              | OL.Obj (attrs, props) ->
                try
                  match (IdMap.find s props) with
                  | OL.Data (_, _, b) 
                  | OL.Accessor (_, _, b) when trueEnough b ->
                    let newObj = if strongUpdate
                      then OL.Obj (attrs, IdMap.remove s props) 
                      else OL.Obj (attrs, IdMap.add s OL.PropTop props) in
                    (updateValue strongUpdate label addr (VL.injectObj newObj) store, true)
                  | _ -> (store, modified)
                with Not_found -> (store, modified)
            ) addrs (storeField, false) in
            (obj', store3, modified)
          end
      end
    | C.SetBang(_, label, id, value) ->
      let (bE, _, _) = getEnv label env in
      let (bH, _, _) = getStore label store in
      let idAddr = IdMap.find id bE in
      let oldIdValue = Ljs_cps_values.Store.find idAddr bH in
      let envValue = copyEnv label (C.label_of_val value) env in
      let storeValue = pushStore label (C.label_of_val value) store in
      let value' = eval_val value envValue storeValue in
      if (oldIdValue = value')
      then (value', store, false)
      else (value', updateValue true label idAddr value' storeValue, true) in

  let answerVal = V.ADDRESS.newAddr() in
  let errorVal = V.ADDRESS.newAddr() in
  let bot = D.ValueLattice._Bot () in
  let bindingEnv = IdMap.add "%%ERROR" errorVal (IdMap.add "%%ANSWER" answerVal IdMap.empty) in
  let bindingStore = Ljs_cps_values.Store.add errorVal bot (Ljs_cps_values.Store.add answerVal bot Ljs_cps_values.Store.empty) in
  let answerAddr = V.ADDRESS.newAddr() in
  let retContEnv = IdMap.add "%answer" answerAddr IdMap.empty in
  let retContStore = V.Store.add answerAddr V.Answer V.Store.empty in
  let errorAddr = V.ADDRESS.newAddr() in
  let exnContEnv = IdMap.add "%error" errorAddr IdMap.empty in
  let exnContStore = V.Store.add errorAddr V.Error V.Store.empty in
  let expLab = C.label_of_exp exp in
  let finalLab = C.Label.newLabel() in
  printf "FinalLab is %s\n" (C.Label.toString finalLab);
  let initEnv = C.LabelMap.singleton expLab (bindingEnv, retContEnv, exnContEnv) in
  let initEnv = copyEnv expLab finalLab initEnv in
  let initStore = C.LabelMap.singleton expLab (bindingStore, retContStore, exnContStore) in
  let initStore = pushStore expLab finalLab initStore in
  let rec fixpoint eval exp env store =
    printf "At beginning of outer fixpoint:\n";
    print_all_abs_env env;
    print_all_abs_bindings store;
    let finalAns = getBinding finalLab "%%ANSWER" env store in
    let finalErr = getBinding finalLab "%%ERROR" env store in
    printAnsErr "In outer fixpoint" finalAns finalErr;
    let (env', store', modified) = eval exp finalLab env store in
    let finalAns = getBinding finalLab "%%ANSWER" env' store' in
    let finalErr = getBinding finalLab "%%ERROR" env' store' in
    printf "At end of outer fixpoint:\n";
    print_all_abs_env env';
    print_all_abs_bindings store';
    printAnsErr "After loop of outer fixpoint" finalAns finalErr;
    let envUnchanged = C.LabelMap.equal (fun (b1, r1, e1) (b2, r2, e2) -> 
      IdMap.equal (=) b1 b2 && IdMap.equal (=) r1 r2 && IdMap.equal (=) e1 e2) env env' in
    let storeUnchanged = C.LabelMap.equal (fun (b1, r1, e1) (b2, r2, e2) -> 
      Ljs_cps_values.Store.equal D.ValueLattice.eq b1 b2 (* &&  *)
        (* V.Store.equal (=) r1 r2 &&  *)
        (* V.Store.equal (=) e1 e2 *)) store store' in
    printf "Env unchanged: %s, Store unchanged: %s\n" 
      (string_of_bool envUnchanged) (string_of_bool storeUnchanged);
    if envUnchanged && storeUnchanged
    then (printf "Reached outer fixpoint, env/store is unchanged\n"; (env', store', finalLab))
    else fixpoint eval exp (joinEnvs env env') (joinStores store store') in
  let (env, store, finalLab) = fixpoint eval_exp exp initEnv initStore in
  (env, store, finalLab)






















type env = C.cps_exp IdMap.t

let build expr =
  let v = expr in
  let cfg = G.add_vertex G.empty v in
  let rec build_exp (g : G.t) (env : env) (entry : vert) (exp : Ljs_cps.cps_exp) : (G.t * vert) =
    match exp with
  | C.LetValue(pos,l, id, value, exp) -> (g, entry)
  | C.RecValue(pos,l, id, value, exp) -> (g, entry)
  | C.LetPrim(pos,l, id, prim, exp) -> (g, entry)
  | C.LetRetCont(l,ret, _, exp) -> (g, entry)
  | C.LetExnCont(l,exn, _, exp) -> (g, entry)
  | C.If(pos,l, cond, trueBranch, falseBranch) -> (g, entry)
  | C.AppFun(pos,l, func, ret, exn, args) -> (g, entry)
  | C.AppRetCont(l,ret, arg) -> (g, entry)
  | C.AppExnCont(l,exn, arg, label) -> (g, entry)
  | C.Eval(pos,l, eval) -> (g, entry) in
  fst (build_exp cfg IdMap.empty v expr)

let cpsv_to_string cps_value =
  Ljs_cps_pretty.value false cps_value Format.str_formatter;
  Format.flush_str_formatter()
module Display = struct
  include G
  let vertex_name v = match v with
  | C.LetValue(pos,l, id, value, exp) -> "LetValue(" ^ id ^ ")"
  | C.RecValue(pos,l, id, value, exp) -> "RecValue(" ^ id ^ ")"
  | C.LetPrim(pos,l, id, prim, exp) -> "LetPrim(" ^ id ^ ")"
  | C.LetRetCont(l,ret, _, exp) -> "LetRet(" ^ ret ^ ")"
  | C.LetExnCont(l,exn, _, exp) -> "LetExn(" ^ exn ^ ")"
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
