open Prelude
open Ljs_sym_values
module S = Ljs_syntax

(* summarized results, (sym_arg_val, arg_id) list *)
type summary = results * (value * id) list

let map_store f g s = { vals = f s.vals; objs = g s.objs }
let map2_store f g s1 s2 =
  { vals = f s1.vals s2.vals; objs = g s1.objs s2.objs }

(* pc_new should be an augmented pc_orig *)
let pc_diff pc_new pc_orig =
  (* TODO: handle the store if we need to *)
  (* Optimized set difference that takes advantage of the fact that
   * the new constraint list ends with the original constraint list. *)
  let only_new news origs =
    take ((List.length news) - (List.length origs)) news
  in
  { pc_new with
    constraints = only_new pc_new.constraints pc_orig.constraints;
    vars = IdMap.diff pc_new.vars pc_orig.vars; (* this might discount updated vars *)
    store = map2_store Store.diff Store.diff pc_new.store pc_orig.store (* this might discout updated vals *)
  }

let pc_sum pc_new pc_orig =
  (* TODO: handle the store if we need to *)
  { pc_orig with
    constraints = List.rev_append pc_new.constraints pc_orig.constraints;
    vars = IdMap.join
             (fun id _ _ -> failwith ("var maps should be disjoint " ^ id))
             pc_new.vars pc_orig.vars;
    store = map2_store
             (Store.join (fun loc newv oldv -> newv))
             (Store.join (fun loc newo oldo -> newo))
             pc_new.store pc_orig.store
  }

let map_sym_val (f : id -> id) v : value = match v with
  | NewSym (symid, locs) -> NewSym (f symid, locs) (* TODO: should probably init these *)
  | SymScalar symid -> SymScalar (f symid)
  | _ -> v

let map_sym_val' (f : id -> value) v : value = match v with
  | NewSym (symid, _)  (* TODO: should probably init these *)
  | SymScalar symid -> f symid
  | _ -> v

let map_sym_bool (f : id -> id) b : symbool = match b with
  | BSym id -> BSym (f id) | _ -> b
let map_sym_string (f : id -> id) s : symstring = match s with
  | SSym id -> SSym (f id) | _ -> s

let map_sym_obj (f : id -> id) obj : objlit =
  let attrs_helper attrs =
    { attrs with
      extensible = map_sym_bool f attrs.extensible;
      klass = map_sym_string f attrs.klass }
  in
  let props_helper props =
    IdMap.map
      (fun prop -> match prop with
        | Data (data, enum, config) ->
            Data ({ data with writable = map_sym_bool f data.writable },
                  map_sym_bool f enum, map_sym_bool f config)
        | Accessor (acc, enum, config) ->
            Accessor (acc, map_sym_bool f enum, map_sym_bool f config))
      props
  in
  let fields_helper fields = {
    attrs = attrs_helper fields.attrs;
    conps = props_helper fields.conps;
    symps = props_helper fields.symps
  } in
  match obj with
  | ConObj fields -> ConObj (fields_helper fields)
  | SymObj (fields, locs) -> SymObj (fields_helper fields, locs)
  | _ -> obj

(* Applies f to all nested vals inside an exval *)
let map_exn_val (f : value -> value) (exv : exval) : exval =
   match exv with
   | Break (lbl, v) -> Break (lbl, f v)
   | Throw v -> Throw (f v)

(* Applies f to every sym id in the pc *)
let map_sym_pc (f : id -> id) pc =
  { pc with
    constraints =
      map 
        (exp_map
          (fun exp -> match exp with
            | SId id -> SId (f id)
            | SLet (id, e) -> SLet (f id, e)
            | _ -> exp))
        pc.constraints;
    vars =
      IdMap.fold
        (fun id t newvars -> IdMap.add (f id) t newvars)
        pc.vars IdMap.empty;
    store = map_store
      (Store.map (map_sym_val f))
      (Store.map (fun (o, hide) -> (map_sym_obj f o, hide)))
      pc.store
  }

(* TODO: consolidate branches with same result values by creating a
 * disjunction of their constraints. Esp. for unsats. *)
(* TODO: To compute input conds on objects, have to look at objects after evaling and
 * compare to objects before. However, this will conflate these conds with
 * side-effects of the summarized code. One solution would be to modify the evaluator
 * to add GetField expressions to the pc. *)
let summarize fname eval apply envs pc : summary option =
  printf "Summarizing %s\n" fname;
  let fval =
    try
      sto_lookup_val (env_lookup fname envs) pc
    with Not_found -> failwith "Couldn't find %s to summarize\n"
  in
  match fval with
  | Closure (arg_ids, body, env) ->
    (* Allocate a sym val for each argument. *)
    let (sym_args, pc) =
      fold_right
        (fun arg_id (sym_args, pc) ->
          let sym, pc = new_sym_fresh ("summary arg " ^ arg_id) pc in
          ((sym, arg_id) :: sym_args, pc))
        arg_ids
        ([], pc)
    in
    let helper ret (v, pc') =
      (* TODO: add in support for objects *)
      (* TODO: compute side effects *) 
      let summary_pc = pc_diff pc' pc in

      printf "SUMMARY\n";
      printf "vars: %s\n" (String.concat ", " (IdMap.keys summary_pc.vars));
      (*printf "%s\n\n" (Ljs_sym_z3.simple_to_string v summary_pc);*)
      List.iter 
        (fun c -> printf "%s\n" (Ljs_sym_z3.to_string c summary_pc))
        summary_pc.constraints;

      ret v summary_pc
    in
    Some
      (prune_unsats (reset_traces
        (bind_both (apply fval (map fst sym_args) envs pc eval)
              (helper return)
              (helper throw))),
      sym_args)
  (* TODO: support function objects *)
  | _ -> None

let next_prefix =
  let counter = ref 0 in
  (fun () -> incr counter; "sum" ^ (string_of_int !counter))

let rename_summary map_val (v, pc) sym_args =
  let prefix = next_prefix () in
  let rename id = prefix ^ id in
  let pc = map_sym_pc rename pc in
  let sym_args =
    map
      (fun (symid, arg_id) -> (rename symid, arg_id))
      sym_args
  in
  let v = map_val (map_sym_val rename) v in
  (v, pc), sym_args

let apply_summary fexp (branches, sym_args) envs pc =
  (* Replace each sym arg val with just its sym id *)
  let sym_args =
    map (fun (symv, arg_id) ->
          (*printf "SYMARG: %s\n" (Ljs_sym_pretty.val_to_string symv);*)
          match symv with
          | NewSym (id, _)  (* TODO: should probably init these *)
          | SymScalar id -> (id, arg_id)
          | _ -> failwith "should only have syms")
        sym_args
  in 
  let helper ret map_val branch =
    (* TODO: add in support for objects *)
    (* Rename all sym values used in the summary to avoid conflicts.
     * We do this when applying instead of when summarizing since a 
     * summary may be applied multiple times in one execution. *)
    let (v, pc'), sym_args = rename_summary map_val branch sym_args in

    (*printf "Applying summary, return val: %s\n" (Ljs_sym_pretty.val_to_string v);*)
    (*printf "PRESUB\n";*)
    (*printf "vars: %s\n" (String.concat ", " (IdMap.keys pc'.vars));*)
    (*printf "val: %s\n" (Ljs_sym_z3.simple_to_string v pc');*)

    (* Substitute each arg's sym id from the summary with the value bound
     * to that arg in the current environment. This takes advantage of
     * the fact that we are applying the summary after binding the args.
     * We only care about the constraints and not the vars since we are
     * just eliminating sym vars (we could remove these sym vars from the
     * vars map, but we don't need to). *)
    (* TODO: this approach is nice because it should extend well to objects *)
    let pc' = { pc' with constraints =
      map
        (exp_map (fun exp ->
          (*printf "CON: %s\n" (Ljs_sym_z3.to_string exp pc');*)
          match exp with
          | SId symid
          | SLet (symid, _) -> begin
            try
              let arg_id = List.assoc symid sym_args in
              let argv = sto_lookup_val (env_lookup arg_id envs) pc in
              printf "bound arg %s to %s\n" (Ljs_sym_pretty.val_to_string argv) arg_id;
              Concrete argv
            with Not_found -> exp
          end
          | _ -> exp))
        pc'.constraints }
    in
    (* Don't forget to replace the return value too, if sym. *)
    let v =
      map_val (fun v ->
        map_sym_val' (fun symid ->
          try
            let arg_id = List.assoc symid sym_args in
            sto_lookup_val (env_lookup arg_id envs) pc
          with Not_found -> v)
        v)
      v
    in

    (*printf "APPLYING\n";*)
    (*printf "cur vars: %s\n" (String.concat ", " (IdMap.keys pc.vars));*)
    (*printf "new vars: %s\n" (String.concat ", " (IdMap.keys pc'.vars));*)
    (*printf "val: %s\n" (Ljs_sym_pretty.val_to_string v);*)
    (*printf "val: %s\n" (Ljs_sym_z3.simple_to_string v pc');*)

    (* Combine the summary with the current pc *)
    let new_pc = pc_sum pc' pc in
    (* TODO: could check sat here - have to see if it's practical. *)
    if Ljs_sym_z3.is_sat new_pc "applying summary" 
    then ret v new_pc
    else none
  in
  (* Just for the trace *)
  let arg_string = String.concat ", "
    (map
      (fun (_, arg_id) ->
         Ljs_sym_pretty.val_to_string
           (sto_lookup_val (env_lookup arg_id envs) pc))
      sym_args)
  in
  add_trace_pt (fexp, "apply summary, args: " ^ arg_string)
    (combine (unsat pc)
      (bind_both branches
        (helper
          (fun v pc -> match v with (* TODO: support objects *)
            | ObjPtr _ -> none
            | _ -> return v pc)
          (fun f v -> f v))
        (helper throw map_exn_val)))

(* Save summaries for the whole execution of the program. *)
(* TODO: persist summaries across multiple executions by writing to
 * an external cache. *)
let summaries = ref IdMap.empty

(* To trigger the making of a summary, write a hint sometime
 * after the function is defined like so:
 * /*:SUMMARIZE myFunc*/
 * (if that doesn't work, check the syntax at the top of ljs_sym_eval *)
let make_summary fname eval apply envs pc : unit =
  match summarize fname eval apply envs pc with
  | Some summary ->
    summaries := IdMap.add fname summary !summaries
  | None -> ()

(* Returns a function with the same signature as nested_eval,
 * so that it can be passed through to apply *)
let get_summary fexp : (S.exp -> env_stack -> ctx -> results) option =
  match fexp with
  | S.Id (p, fname) -> begin
    try
      let summary = IdMap.find fname !summaries in
      Some (fun body envs pc -> apply_summary fexp summary envs pc)
    with Not_found -> None
  end
  | _ -> None
