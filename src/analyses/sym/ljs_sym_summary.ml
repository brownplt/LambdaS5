open Prelude
open Ljs_sym_values
open Ljs_sym_env
open Ljs_sym_pretty
module S = Ljs_syntax

(* summarized results, (sym_arg_val, arg_id) list *)
type summary = results * (value * id) list

let map_store f g s = { vals = f s.vals; objs = g s.objs }
let map2_store f g s1 s2 =
  { vals = f s1.vals s2.vals; objs = g s1.objs s2.objs }

let unwrap_assert con = match con with SAssert e -> e | _ -> failwith "Should be assert"
let f_just_asserts f cons =
  let asserts, others =
    List.partition
      (fun con -> match con with SAssert _ -> true | _ -> false)
      cons
  in
  match asserts with [] -> others | _ ->
  f asserts @ others

let conjoin cons =
  f_just_asserts
    (fun asserts -> [SAssert (SAnd (map unwrap_assert asserts))])
    cons

let disjoin cons =
  f_just_asserts
    (fun asserts -> [SAssert (SOr (map unwrap_assert asserts))])
    cons

(* pc_new should be an augmented pc_orig *)
let pc_diff pc_new pc_orig =
  (* Optimized set difference that takes advantage of the fact that
   * the new constraint list ends with the original constraint list. *)
  let only_new news origs =
    take ((List.length news) - (List.length origs)) news
  in
  { pc_new with
    constraints = only_new pc_new.constraints pc_orig.constraints;
    vars = IdMap.diff pc_new.vars pc_orig.vars; (* this might discount updated vars *)
    (*store = map2_store Store.diff Store.diff pc_new.store pc_orig.store [> this might discout updated vals <]*)
  }

let pc_sum pc_new pc_orig =
  { pc_orig with
    constraints = List.rev_append pc_new.constraints pc_orig.constraints;
    vars = IdMap.join
             (* Should be disjoint because of the diff we did in pc_diff *)
             (fun id _ _ -> failwith ("var maps should be disjoint " ^ id))
             pc_new.vars pc_orig.vars;
    (*store = map2_store*)
    (*         (Store.join (fun loc _ _ -> failwith ("stores should be disjoint " ^ Store.print_loc loc)))*)
    (*         (Store.join (fun loc _ _ -> failwith ("stores should be disjoint " ^ Store.print_loc loc)))*)
    (*         (Store.join (fun loc newo oldo -> newo))*)
    (*         pc_new.store pc_orig.store*)
  }

let pc_union pc_new pc_orig =
  { pc_orig with
    constraints = disjoin (conjoin pc_new.constraints @ conjoin pc_orig.constraints);
    vars = IdMap.join
             (fun id tnew torig -> tnew) (* TODO: hopefully this doesn't break anything... *)
             pc_new.vars pc_orig.vars;
    (* TODO: Might need to transfer store values *)
  }

(* Add all the values reachable from the return value to the original
 * pc store, updating the locs in the return value accordingly. These are
 * the only values needed from the summary pc; we can drop the rest of
 * the store when we merge pcs. *)
(* Note that here the use of the ' refers to which pc a value comes from *)
let rec transfer_val vloc' pc' pc =
  match sto_lookup_val vloc' pc' with
  (* TODO: What about NewSyms, Closures? *)
  | ObjPtr oloc' ->
      let oloc, pc = transfer_obj oloc' pc' pc in
      sto_alloc_val (ObjPtr oloc) pc
  | v -> sto_alloc_val v pc
and transfer_obj oloc' pc' pc =
  match sto_lookup_obj oloc' pc' with
  | ConObj fields' ->
      let fields, pc = transfer_fields fields' pc' pc in
      sto_alloc_obj (ConObj fields) pc
  | SymObj (fields', locs') ->
      let fields, pc = transfer_fields fields' pc' pc in
      (* TODO: process locs *)
      sto_alloc_obj (SymObj (fields, [])) pc
  | NewSymObj locs' ->
      failwith "please don't let there be newsymobjs"
and transfer_fields fields' pc' pc =
  let attrs, pc = transfer_attrs fields'.attrs pc' pc in
  let conps, pc = transfer_props fields'.conps pc' pc in
  let symps, pc = transfer_props fields'.symps pc' pc in
  { attrs = attrs; conps = conps; symps = symps }, pc
and transfer_attrs attrs' pc' pc =
  let opt_helper attr_opt' pc = match attr_opt' with
    | Some attr_loc' -> 
        let attr_loc, pc = transfer_val attr_loc' pc' pc in
        Some attr_loc, pc
    | None -> None, pc
  in
  let proto, pc = transfer_val attrs'.proto pc' pc in
  let code, pc = opt_helper attrs'.code pc in
  let primval, pc = opt_helper attrs'.primval pc in
  { attrs' with proto = proto; code = code; primval = primval }, pc
and transfer_props props' pc' pc =
  IdMap.fold
    (fun f prop' (props, pc) ->
      let newprop, pc = match prop' with
      | Data (data', enum', config') ->
        let value, pc = transfer_val data'.value pc' pc in
        Data ({ data' with value = value }, enum', config'), pc
      | Accessor (acc', enum', config') ->
        let getter, pc = transfer_val acc'.getter pc' pc in
        let setter, pc = transfer_val acc'.setter pc' pc in
        Accessor ({ getter = getter; setter = setter }, enum', config'), pc
      in (IdMap.add f newprop props, pc))
    props' (IdMap.empty, pc)

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

(* TODO: To compute input conds on objects, have to look at objects after evaling and
 * compare to objects before. However, this will conflate these conds with
 * side-effects of the summarized code. One solution would be to modify the evaluator
 * to add GetField expressions to the pc. *)
let summarize fname eval apply envs pc : summary option =
  printf "Summarizing %s\n" fname;
  let fval =
    try
      sto_lookup_val (Env.lookup fname envs) pc
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
      (* TODO: Figure out what changed in the store and somehow include that
       * in the summary. For instance, if a NewSym gets replaced by an obj,
       * we need that in the summary. Or maybe we just init all NewSyms beforehand?
       * We can't do that though, because init'ing NewSyms makes more NewSyms.
       *) 

      printf "SUMMARY\n";
      printf "vars: %s\n" (String.concat ", " (IdMap.keys summary_pc.vars));
      printf "%s\n\n" (Ljs_sym_z3.simple_to_string Undefined summary_pc);
      (*List.iter *)
      (*  (fun c -> printf "%s\n" (Ljs_sym_z3.to_string c summary_pc))*)
      (*  summary_pc.constraints;*)

      ret v summary_pc
    in
    let branches =
      (bind_both (apply fval (map fst sym_args) envs pc eval)
        (helper return)
        (helper throw))
    in
    (* This is such a terrible breaking of the monad abstraction.
     * We take the monadic result of just vals/exns, and, knowing it's
     * actually a list of pairs of results with traces, extract a list of
     * the results that we want to collect. This only works because we
     * want to get rid of the traces here anyway. I should be shot for this...
     * - Jonah *)
    let values = map fst (just_values branches) in
    let exns = map fst (just_exns branches) in
    (* Collect like return values and merge their pcs *)
    (* TODO: Probably shouldn't collect like ObjPtrs *)
    let merge_pcs (v, pcs) = (v, fold_left pc_union mt_ctx pcs) in
    let merged_values = map merge_pcs (collect compare values) in
    let compare_exns (exn1,pc1) (exn2,pc2) = match exn1, exn2 with
      | Throw v1, Throw v2 ->
          (*printf "COMPARE %s : %s = %d\n" (val_to_string v1)*)
        compare (message_of_throw v1 pc1) (message_of_throw v2 pc2)
      | _, _ -> 1 in
    (* For exns, instead of merging, just pick a representative result from
     * each group of matching results. TODO better than this *)
    let merged_exns = map List.hd (group compare_exns exns) in
    (* Now wrap them up again and beg for forgiveness. *)
    let branches =
      (* combine's efficiency is linear in the length of its first argument,
      * which probably shouldn't be the accumulator, so we flip it. *) 
      fold_left (flip combine)
        (fold_left (flip combine) none
           (map (uncurry return) merged_values))
        (map (uncurry throw) merged_exns)
    in
    Some (branches, sym_args)
  (* TODO: support function objects *)
  | _ -> None

let next_prefix =
  let counter = ref 0 in
  (fun () -> incr counter; "sum" ^ (string_of_int !counter))

let rename_summary (v, pc) sym_args =
  let prefix = next_prefix () in
  let rename id = prefix ^ id in
  let pc = map_sym_pc rename pc in
  let sym_args =
    map
      (fun (symid, arg_id) -> (rename symid, arg_id))
      sym_args
  in
  let v = map_sym_val rename v in
  (v, pc), sym_args

let apply_summary fexp (branches, sym_args) envs pc =
  (* Replace each sym arg val with just its sym id *)
  let sym_args =
    map (fun (symv, arg_id) ->
          (*printf "SYMARG: %s\n" (val_to_string symv);*)
          match symv with
          | NewSym (id, _)  (* TODO: should probably init these *)
          | SymScalar id -> (id, arg_id)
          | _ -> failwith "should only have syms")
        sym_args
  in 
  let helper branch =
    (* TODO: add in support for objects *)
    (* Rename all sym values used in the summary to avoid conflicts.
     * We do this when applying instead of when summarizing since a 
     * summary may be applied multiple times in one execution. *)
    let (v, pc'), sym_args = rename_summary branch sym_args in

    (*printf "Applying summary, return val: %s\n" (val_to_string v);*)
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
              let argv = sto_lookup_val (Env.lookup arg_id envs) pc in
              printf "bound arg %s to %s\n" (val_to_string argv) arg_id;
              Concrete argv
            with Not_found -> exp
          end
          | _ -> exp))
        pc'.constraints }
    in
    (* Don't forget to replace the return value too, if sym. *)
    let v =
      map_sym_val' (fun symid ->
        try
          let arg_id = List.assoc symid sym_args in
          sto_lookup_val (Env.lookup arg_id envs) pc
        with Not_found -> v)
      v
    in

    (*printf "APPLYING\n";*)
    (*printf "cur vars: %s\n" (String.concat ", " (IdMap.keys pc.vars));*)
    (*printf "new vars: %s\n" (String.concat ", " (IdMap.keys pc'.vars));*)
    (*printf "val: %s\n" (val_to_string v);*)
    (*printf "val: %s\n" (Ljs_sym_z3.simple_to_string v pc');*)

    (* Move everything we need from the summary store into the current store *)
    let v, pc = 
      let vloc', pc' = sto_alloc_val v pc' in
      let vloc, pc = transfer_val vloc' pc' pc in
      sto_lookup_val vloc pc, pc
    in

    (* Combine the summary with the current pc *)
    let new_pc = pc_sum pc' pc in
    (* TODO: could check sat here - have to see if it's practical. *)
    if Ljs_sym_z3.is_sat new_pc "applying summary" 
    then Some (v, new_pc)
    else None
  in
  (* Just for the trace *)
  let arg_string = String.concat ", "
    (map
      (fun (_, arg_id) ->
         val_to_string
           (sto_lookup_val (Env.lookup arg_id envs) pc))
      sym_args)
  in
  (* Need unique labels for each branch for the trace to work correctly *)
  let add_trace_pt_count =
    let counter = ref 0 in
    let next_count () = incr counter; string_of_int !counter in
    (fun branch ->
      add_trace_pt
        (fexp, next_count () ^ " apply summary, args: " ^ arg_string)
        branch)
  in
  (*combine (unsat pc)*)
    (bind_both branches
      (fun branch ->
        match helper branch with
        | Some branch -> add_trace_pt_count (uncurry return branch)
        | None -> none)
      (fun (exv, pc) ->
        match exv with
        | Break (lbl, v) -> begin
          match helper (v, pc) with
          | Some (v, pc) -> add_trace_pt_count (throw (Break (lbl, v)) pc)
          | None -> none
        end
        | Throw v -> begin
          (*printf "THROW %s\n" (val_to_string v);*)
          (*printf "%s\n" (store_to_string pc.store);*)
          match helper (v, pc) with
          | Some (v, pc) -> add_trace_pt_count (throw (Throw v) pc)
          | None -> none
        end))

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
let get_summary fexp : (S.exp -> Env.stack -> ctx -> results) option =
  match fexp with
  | S.Id (p, fname) -> begin
    try
      let summary = IdMap.find fname !summaries in
      Some (fun body envs pc -> apply_summary fexp summary envs pc)
    with Not_found -> None
  end
  | _ -> None
