open Format
open Prelude
module S = Ljs_syntax
open Ljs_sym_values
open Ljs_sym_delta

let compare_keyword = "COMPARE_RESULTS"
let args_id = compare_keyword ^ "_ARGS"

let max_equiv_depth = 1

(* To be compatible with the way functions are desugared in LJS,
 * we need to wrap the OCaml function we want to execute in an
 * LJS function object, put it in the store, and then return a
 * ptr to it. *)
let wrap_with_func_obj env pc f = 
  let proto_loc, pc = sto_alloc_val Null pc in
  let closure_loc, pc = sto_alloc_val (Closure f) pc in
  let func_obj = ConObj {
    attrs = { primval = None; proto = proto_loc;
              code = Some closure_loc; (* func (%this, %args) { do our thing } *)
              klass = SString "Function"; extensible = BTrue };
    conps = IdMap.empty; symps = IdMap.empty;
  } in
  let func_obj_loc, pc = sto_alloc_obj func_obj pc in
  return (ObjPtr func_obj_loc) pc

(* Allocs a val in the store, binding it to id in the env *)
let bind_val id v env pc =
  let vloc, pc = sto_alloc_val v pc in
  (IdMap.add id vloc env, pc)

(* Given two result values and the list of contexts from which
 * they were produced, returns true if there is a pair (v1,pc1) from
 * the first set that is equivalent to a pair (v2,pc2) from the second.
 * For now, equivalence will just be value equality *)
let rec equivalent (v1, pcs1) (v2, pcs2) =
  equiv_value max_equiv_depth (v1, pcs1) (v2, pcs2)

and equiv_value d (v1, pcs1) (v2, pcs2) =
  match v1, v2 with
  (* punt on symbolic values for now *)
  | SymScalar _, SymScalar _
  | SymScalar _, NewSym _
  | NewSym _, SymScalar _
  | NewSym _, NewSym _ -> true
  | ObjPtr oloc1, ObjPtr oloc2 ->
    if d = 0 then true else
    (* Because we don't group ObjPtrs when collecting,
     * we know there should only be one pc in each class *)
    begin
      assert (List.length pcs1 = 1 && List.length pcs2 = 1);
      equiv_obj (d - 1) (oloc1, List.hd pcs1) (oloc2, List.hd pcs2)
    end
    (*List.exists*)
    (*  (fun pc1 ->*)
    (*    List.exists*)
    (*      (fun pc2 ->*)
      (*  pcs2)*)
      (*pcs1*)
  (* otherwise just check equality *)
  (* TODO this will always be false for sym vs. concrete *)
  | _, _ -> begin
    (*printf "%s = %s : %b \n" (Ljs_sym_pretty.val_to_string v1) (Ljs_sym_pretty.val_to_string v2) (v1 = v2);*)
    (* Use compare because nan = nan yields false, but we want true.
     * Luckily, compare nan nan = 0! *)
    (compare v1 v2 = 0)
    end

and equiv_lookup d (vloc1, pc1) (vloc2, pc2) =
  equiv_value d (sto_lookup_val vloc1 pc1, [pc1])
               (sto_lookup_val vloc2 pc2, [pc2])

and equiv_obj d (loc1, pc1) (loc2, pc2) =
  let obj1 = sto_lookup_obj loc1 pc1 in
  let obj2 = sto_lookup_obj loc2 pc2 in
  match obj1, obj2 with
  | ConObj o1, ConObj o2
  | SymObj o1, SymObj o2 ->
       equiv_attrs d (o1.attrs, pc1) (o2.attrs, pc2) 
    && equiv_props d (o1.conps, pc1) (o2.conps, pc2)
    && equiv_props d (o1.symps, pc1) (o2.symps, pc2)
  (* TODO Preliminary idea: NewSymObjs aren't equal,
   * because we'd have to check the obj at every loc in
   * their lists for equality as well. *)
  | NewSymObj _, NewSymObj _ ->
    (*printf "%s\n" "NewSymObj false";*)
      false
  (* TODO Preliminary idea: diff obj types aren't equal.
   * This is probably wrong. More likely is that a sym obj
   * is equal to any con obj as long as all the fields present
   * in the sym obj are present and have equal values in
   * the con obj. *)
  | _, _ -> false

and equiv_attrs d (as1, pc1) (as2, pc2) = true
  (*let equiv_attr_opt a1 a2 = match a1, a2 with*)
  (*  | None, None -> true*)
  (*  | Some aloc1, Some aloc2 -> equiv_lookup (aloc1, pc1) (aloc2, pc2)*)
  (*  | _, _ -> false*)
  (*in*)
  (*   equiv_attr_opt as1.code as2.code*)
  (*&& equiv_lookup (as1.proto, pc1) (as2.proto, pc2)*)
  (*&& equiv_symbool (as1.extensible, pc1) (as2.extensible, pc2)*)
  (*&& equiv_symstring (as1.klass, pc1) (as2.klass, pc2)*)
  (*&& equiv_attr_opt as1.primval as2.primval*)

and equiv_props d (props1, pc1) (props2, pc2) =
  try 
    List.for_all2
      (fun (f1, p1) (f2, p2) ->
        (* TODO this is wrong if f1, f2 sym - could be equal with different names *)
        (*printf "field %s = %s : %b\n" f1 f2 (f1 = f2);*)
        if f1 <> f2 then false
        else match p1, p2 with
        | Data (data1, enum1, config1),
          Data (data2, enum2, config2) ->
          enum1 = enum2 && config1 = config2
          && equiv_symbool d (data1.writable, pc1) (data2.writable, pc2)
          && equiv_lookup d (data1.value, pc1) (data2.value, pc2)
        | Accessor (acc1, enum1, config1),
          Accessor (acc2, enum2, config2) ->
          enum1 = enum2 && config1 = config2
          (* TODO figure out a good way to compare closures *)
          (*&& equiv_lookup d (acc1.getter, pc1) (acc2.getter, pc2)*)
          (*&& equiv_lookup d (acc1.setter, pc1) (acc2.setter, pc2)*)
        | _, _ -> false)
    (IdMap.bindings props1)
    (IdMap.bindings props2)
  with Invalid_argument _ -> false (* length mismatch *)

and equiv_symbool d (b1, pc1) (b2, pc2) =
  match b1, b2 with
  | BTrue, BTrue
  | BFalse, BFalse -> true
  | BSym id1, BSym id2 ->
    (* TODO probably want to go straight to z3 instead of wrapping
     * with SymScalar *)
    equiv_value d (SymScalar id1, [pc1]) (SymScalar id2, [pc2])
  | _, _ -> false (* TODO sym vs. concrete *)

and equiv_symstring d (s1, pc1) (s2, pc2) =
  match s1, s2 with
  | SString str1, SString str2 -> str1 = str2
  | SSym id1, SSym id2 ->
    (* TODO probably want to go straight to z3 instead of wrapping
     * with SymScalar *)
   equiv_value d (SymScalar id1, [pc1]) (SymScalar id2, [pc2])
  | _, _ -> false (* TODO sym vs. concrete *)

(* Comparator to use for grouping pcs by like values. *)
let our_cmp v1 v2 =
  match v1, v2 with
  (* ObjPtrs with the same loc might point to diff objs in
   * diff contexts, so they aren't equal. *)
  | ObjPtr _, ObjPtr _
  (* Similarly, sym values might be diff depending on context *)
  | SymScalar _, SymScalar _
  | SymScalar _, NewSym _
  | NewSym _, SymScalar _
  | NewSym _, NewSym _ -> 1
  | _, _ -> compare v1 v2

(* Returns an ObjPtr to a function object that can be eval'd
 * to compare the results stored in args. *)
let compare_results p args env pc eval =
  (wrap_with_func_obj env pc (fun args pc _ ->
    (* Extract the functions to compare from the args obj.
     * We construct exps to give to the eval that will run the
     * desired functions. *)
    let args_obj = List.nth args 1 in
    let env, pc = bind_val args_id args_obj env pc in
    let get_exp n = S.GetField (p, S.Id (p, args_id), S.String (p, n), S.Null p) in
    let fexp1, fexp2, target_fexp = get_exp "0", get_exp "1", get_exp "2" in

    (* Helper to eval an exp in a context *)
    let eval_fexp fexp pc = eval (S.App (p, fexp, [S.Null p; S.Null p])) env pc in
    (* Helper to eval the target in the context produced by fexp *)
    let eval_target_after fexp =
      bind (eval_fexp fexp pc)
        (fun (_, pc) -> eval_fexp target_fexp pc)
    in

    let (trets1, _) = eval_target_after fexp1 in
    let (trets2, _) = eval_target_after fexp2 in
    (* Group returned pcs into equivalence classes by value *)
    let targets1 = collect our_cmp trets1 in
    let targets2 = collect our_cmp trets2 in

    printf "%s\n" (">>>>>> found " ^ compare_keyword ^ " <<<<<<");
    printf "%s\n" "####### Results to compare:";
    List.iter
      (fun (v,pcs) -> printf "%s, " (Ljs_sym_pretty.val_to_string v))
      targets1;
    (*Ljs_sym_z3.print_results (targets1, []);*)
    printf "\n%s\n" "============";
    List.iter
      (fun (v,pcs) -> printf "%s, " (Ljs_sym_pretty.val_to_string v))
      targets2;
    printf "\n%s\n" "####### End compare";
    (*Ljs_sym_z3.print_results (targets2, []);*)

    (* Check for result set equivalence.
     * Our metric will be, for each return value in targets1,
     * does there exist an equivalent return value in targets2 *)
    let equiv_results =
      List.for_all
        (fun res_class ->
          let res = List.exists (equivalent res_class) targets2 in
          if not res then
            (*Ljs_sym_z3.print_results ([res_class], []);*)
            printf "%s\n"
            ("No matching result for " ^ Ljs_sym_pretty.val_to_string (fst res_class)); 
          res)
        targets1
    in
    printf "Comparison result: %b\n" equiv_results;
    return (bool equiv_results) pc))

    (*let (rets2, exns2) = eval (S.App (p, func2e, [S.Null p; S.Null p])) env pc in*)
    (*| _ ->*)
    (*  failwith*)
    (*    (compare_keyword ^ " given wrong args.\n"*)
    (*    ^ "usage: " ^ compare_keyword ^ "(func1, func2, targetFunc)\n"*)
    (*    ^ "where target func returns the value to compare.")))*)
  (*let wrapper_obj = ConObj {*)
  (*  attrs = { primval = None; proto = fst (sto_alloc_val Null pc);*)
  (*            code = None; klass = SString "Object"; extensible = BTrue; };*)
  (*  conps = IdMap.add "0"*)
  (*            (Data ({ value = func_obj_loc; writable = BTrue; }, BTrue, BTrue))*)
  (*            IdMap.empty;*)
  (*  symps = IdMap.empty;*)
  (*} in*)
  (*let wrapper_obj_loc, pc = sto_alloc_obj wrapper_obj pc in*)
