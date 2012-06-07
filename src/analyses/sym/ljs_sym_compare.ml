open Format
open Prelude
module S = Ljs_syntax
open Ljs_sym_values
open Ljs_sym_delta

let compare_keyword = "COMPARE_RESULTS"
let args_id = compare_keyword ^ "_ARGS"
(*let id1 = compare_keyword ^ "_FUNC1"*)
(*let id2 = compare_keyword ^ "_FUNC2"*)

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

let bind_val id v env pc =
  let vloc, pc = sto_alloc_val v pc in
  (*let loc, pc = sto_alloc_val (ObjPtr funcv_loc) pc in*)
  (IdMap.add id vloc env, pc)

(* For now, equivalence will just be value equality *)
let equivalent (v1, pcs1) (v2, pcs2) =
  match v1, v2 with
  (* punt on symbolic values for now *)
  | SymScalar _, SymScalar _
  | SymScalar _, NewSym _
  | NewSym _, SymScalar _ -> true
  (* punt on objects for now *)
  | ObjPtr _, ObjPtr _ -> true
  (* otherwise just check equality *)
  (* TODO this will always be false for sym vs. concrete *)
  | _, _ -> v1 = v2

let compare_results p args env pc eval =
  (wrap_with_func_obj env pc (fun args pc _ ->
    (*printf "%d\n" (List.length args);*)
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
    let targets1 = collect trets1 in
    let targets2 = collect trets2 in

    printf "%s\n" "Results to compare:";
    List.iter
      (fun (v,pcs) -> printf "%s, " (Ljs_sym_pretty.val_to_string v))
      targets1;
    (*printf "--------- %s: %d, %d\n" "Got to compare!" (List.length targets1) (List.length targets2);*)
    printf "%s\n" "\n-------------";
    List.iter
      (fun (v,pcs) -> printf "%s, " (Ljs_sym_pretty.val_to_string v))
      targets2;
    printf "%s\n" "";
    (* Check for result set equivalence.
     * Our metric will be, for each return value in targets1,
     * does there exist an equivalent return value in targets2 *)
    let equiv_results =
      List.for_all
        (fun res_class ->
          List.exists (equivalent res_class) targets2)
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
