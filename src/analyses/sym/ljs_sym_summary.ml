open Prelude
open Ljs_sym_values
module S = Ljs_syntax

(* result_val, (sym_arg_val, arg_id) list *)
type branch = (value * (value * id) list) result
type summary = branch res_mo

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
    store = { objs = Store.empty; vals = Store.empty } (* empty til we care *)
  }

let pc_sum pc_new pc_orig =
  (* TODO: handle the store if we need to *)
  { pc_orig with
    constraints = List.rev_append pc_new.constraints pc_orig.constraints;
    vars = IdMap.join
             (fun id _ _ -> failwith ("var maps should be disjoint " ^ id))
             pc_new.vars pc_orig.vars;
  }

(* Applies f to every sym id in the pc *)
let map_sym_pc (f : id -> id) pc =
  (* TODO: handle the store if we need to *)
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
  }

(* If given a sym val, applies f to its id *)
let map_sym_val (f : id -> value) v : value = match v with
  | NewSym (symid, _)  (* TODO: should probably init these *)
  | SymScalar symid -> f symid
  | _ -> v

(* TODO: To compute input conds on objects, have to look at objects after evaling and
 * compare to objects before. However, this will conflate these conds with
 * side-effects of the summarized code. One solution would be to modify the evaluator
 * to add GetField expressions to the pc. *)
let summarize fname eval apply envs pc : summary option =
  printf "Summarizing %s" fname;
  let fval = sto_lookup_val (env_lookup fname envs) pc in
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
    Some (bind (apply fval (map fst sym_args) envs pc eval) (* TODO: exceptions? *)
      (fun (v, pc') ->
        (* TODO: add in support for objects *)
        (* TODO: compute side effects *) 
        let summary_pc = pc_diff pc' pc in

        (*printf "SUMMARY\n";*)
        (*printf "%s\n" (String.concat ", " (IdMap.keys summary_pc.vars));*)
        (*printf "%s\n\n" (Ljs_sym_z3.simple_to_string v summary_pc);*)
        (*List.iter *)
        (*  (fun c -> printf "%s\n" (Ljs_sym_z3.to_string c pc))*)
        (*  input_conds;*)

        return (v, sym_args) summary_pc))
  (* TODO: support function objects *)
  | _ -> None

let rename_summary =
  let counter = ref 0 in
  let next_prefix () = incr counter; "sum" ^ (string_of_int !counter) in
  (fun ((v, sym_args), pc) ->
    let prefix = next_prefix () in
    let rename id = prefix ^ id in
    let pc = map_sym_pc rename pc in
    let sym_args =
      map
        (fun (symv, arg_id) ->
           (map_sym_val (fun id -> SymScalar (rename id)) symv, arg_id))
        sym_args
    in
    let v = map_sym_val (fun id -> SymScalar (rename id)) v in
    ((v, sym_args), pc))

let apply_summary =
  (fun summary envs pc ->
    bind summary (* TODO: exceptions? *)
      (fun branch ->
        (* TODO: add in support for objects *)
        (* Rename all sym values used in the summary to avoid conflicts. *)
        let ((v, sym_args), pc') = rename_summary branch in

        printf "Applying summary, return val: %s\n" (Ljs_sym_pretty.val_to_string v);
        (*printf "PRESUB\n";*)
        (*printf "vars: %s\n" (String.concat ", " (IdMap.keys pc'.vars));*)
        (*printf "val: %s\n" (Ljs_sym_z3.simple_to_string v pc');*)

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
                  Concrete (sto_lookup_val (env_lookup arg_id envs) pc)
                with Not_found -> exp
              end
              | _ -> exp))
            pc'.constraints }
        in
        (* Don't forget to replace the return value too, if sym. *)
        let v =
          map_sym_val
            (fun symid ->
              try
                let arg_id = List.assoc symid sym_args in
                sto_lookup_val (env_lookup arg_id envs) pc
              with Not_found -> v)
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
        match v with (* TODO: support objects *)
        | ObjPtr _ -> none
        | _ -> return v new_pc))

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
      Some (fun body envs pc -> apply_summary summary envs pc)
    with Not_found -> None
  end
  | _ -> None
