open Format
open Prelude
open Ljs_sym_values
open Ljs_sym_pretty
open Ljs_sym_z3

(** CONSTANTS                            *)
(*****************************************)

let max_equiv_depth = 3

(* TODO make this automatic somehow *)
let proj_root = "/Users/Jonah/Documents/spring2012/research/LambdaS5/"

let rename_prefix = "a"

(** TYPES                                *)
(*****************************************)

type res_class = value * ctx list

type compare_result =
  | Equiv of res_class * res_class
  | Diff of res_class * res_class list

(** UTILITIES                            *)
(*****************************************)

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

let classes_of_results = collect our_cmp
let results_of_class (v, pcs) = map (fun pc -> (v, pc)) pcs
let results_of_classes classes = 
  List.concat (map results_of_class classes)

let rec read_until chan test : unit =
  let line = input_line chan in
  if test line then ()
  else read_until chan test

(* Produces the list of f applies to each pair of xs and ys,
 * in the reverse order of what you might expect.
 * I.e. combinations pair [1;2] [3;4] =
 * [(2, 4); (2, 3); (1, 4); (1, 3)] *)
let combinations (f : ('x -> 'y -> 'z)) xs ys : 'z list =
  List.fold_left (fun acc1 x ->
    List.fold_left (fun acc2 y ->
                 (f x y) :: acc2)
      acc1 ys)
    [] xs

(* Renames every sym id in the program context to start with prefix. *)
(* Note that we only rename the parts that will be used in Ljs_sym_z3.is_sat. *)
let alpha_rename prefix pc =
  let rename id =
    (* We won't rename concrete string constants, because
     * there's no problem with those overlapping (they're constants!) *)
    if String.length id >= 2 && String.sub id 0 2 = "S_"
    then id
    else (prefix ^ id)
  in
  { pc with
    constraints =
      map
        (exp_map
           (fun exp -> match exp with
              | SId id -> SId (rename id)
              | SLet (id, e) -> SLet (rename id, e)
              | _ -> exp))
        pc.constraints;
    vars =
      IdMap.fold
        (fun id t res -> IdMap.add (rename id) t res)
        pc.vars IdMap.empty;
  }

(** PRINTING                             *)
(*****************************************)

let print_comp_results results =
  List.iter
    (fun result -> match result with
      | Equiv (c1, c2) ->
          printf "Match: %s\t~ %s\n"
            (val_to_string (fst c1))
            (val_to_string (fst c2))
      | Diff (c1, cs2) -> begin
          printf "No match for: %s\n" (val_to_string (fst c1));
          print_results (results_of_class c1, []);
          printf "\nwhen compared against:\n";
          print_results (results_of_classes cs2, [])
        end) 
    results

(** INTERFACE WITH SYM EVAL              *)
(*****************************************)

let sym_eval js_path =
  let res_file = js_path ^ ".raw" in
  if (Sys.file_exists res_file) then
    printf "Using cached results: %s" res_file
  else begin
    let ast_path = js_path ^ ".ast" in
    if (Sys.file_exists ast_path) then
      printf "Using cached AST: %s" res_file
    else begin
      let js2ast = proj_root ^ "bin/js " ^
        proj_root ^ "tests/json_print.js " ^
        js_path ^ " > " ^ ast_path
      in
      if Sys.command js2ast <> 0
      then failwith ("Could not convert JS to AST: " ^ js_path)
      else ()
    end;
    (* Run the symbolic evaluator on the AST,*)
    (* outputting the raw OCaml results. *)
    let symeval = proj_root ^ "obj/s5.d.byte" ^
      " -desugar " ^ ast_path ^
      " -env " ^ proj_root ^ "envs/es5.env" ^
      " -sym-eval-raw > " ^ res_file
    in
    let _ = Sys.command symeval in ()
  end;

  (* Read the raw results back into OCaml values *)
  let chan = open_in res_file in
  begin
    try read_until chan (fun line -> line = "RAW RESULTS");
    with End_of_file -> failwith ("Couldn't find RAW RESULTS in " ^ res_file)
  end;
  let results = ((input_value chan) : result list * exresult list) in
  close_in chan;
  results
 
(** CHECKING EQUIVALENCE                 *)
(*****************************************)

let rec equiv_value d (v1, pcs1) (v2, pcs2) =
  match v1, v2 with
  (* punt on symbolic values for now *)
  (*| SymScalar _, SymScalar _*)
  (*| SymScalar _, NewSym _*)
  (*| NewSym _, SymScalar _*)
  (*| NewSym _, NewSym _ -> true*)
  | SymScalar id, _ -> equiv_sym (id, pcs1) (v2, pcs2)
  | _, SymScalar id -> equiv_sym (id, pcs2) (v1, pcs1)
  | ObjPtr oloc1, ObjPtr oloc2 ->
    if d = 0 then true else
    (* Because we don't group ObjPtrs when collecting,
     * we know there should only be one pc in each class *)
    begin
      assert (List.length pcs1 = 1 && List.length pcs2 = 1);
      equiv_obj (d - 1) (oloc1, List.hd pcs1) (oloc2, List.hd pcs2)
    end
  (* otherwise just check equality *)
  (* TODO this will always be false for sym vs. concrete *)
  | _, _ -> begin
    (*printf "%s = %s : %b \n" (Ljs_sym_pretty.val_to_string v1) (Ljs_sym_pretty.val_to_string v2) (v1 = v2);*)
    (* Use compare because nan = nan yields false, but we want true.
     * Luckily, compare nan nan = 0! *)
    (compare v1 v2 = 0)
    end

and equiv_sym (id1, pcs1) (v2, pcs2) =
  match v2 with
  | SymScalar id2 ->
    let id2 = rename_prefix ^ id2 in
    let pcs2 = map (alpha_rename rename_prefix) pcs2 in
    let joint_pcs = 
      combinations
        (fun pc1 pc2 ->
          { pc1 with
            (* We only care about constraints and vars
             * because that's all that we use in
             * Ljs_sym_z3.is_sat *)
            constraints = pc1.constraints @ pc2.constraints;
            (* Var maps key sets should be disjoint, so
             * we can union them like so. *)
            vars = IdMap.fold IdMap.add pc1.vars pc2.vars; })
        pcs1 pcs2
    in
    List.exists (fun pc -> is_sat pc ("equiv_sym " ^ id1 ^ ", " ^ id2))
      (map (add_assert (is_equal (SId id1) (SId id2))) joint_pcs)

  | ObjPtr _ -> false
  | Closure _ (* uhh, who knows? *)
  | _ ->
    List.exists (fun pc -> is_sat pc ("equiv_sym " ^ id1))
      (map (add_assert (is_equal (SId id1) (Concrete v2))) pcs1)

and equiv_obj d (loc1, pc1) (loc2, pc2) =
  let obj1 = sto_lookup_obj loc1 pc1 in
  let obj2 = sto_lookup_obj loc2 pc2 in
  match obj1, obj2 with
  | ConObj o1, ConObj o2
  | SymObj (o1, _), SymObj (o2, _) ->
       equiv_attrs d (o1.attrs, pc1) (o2.attrs, pc2) 
    && equiv_props d (o1.conps, pc1) (o2.conps, pc2)
    && equiv_props d (o1.symps, pc1) (o2.symps, pc2)
  (* TODO Preliminary idea: NewSymObjs aren't equal,
   * because we'd have to check the obj at every loc in
   * their lists for equality as well. *)
  | NewSymObj _, NewSymObj _ ->
      (* eh, let it be true for now *)
      true (*false*) 
  (* TODO Preliminary idea: diff obj types aren't equal.
   * This is probably wrong. More likely is that a sym obj
   * is equal to any con obj as long as all the fields present
   * in the sym obj are present and have equal values in
   * the con obj. *)
  | _, _ -> false

and equiv_attrs d (as1, pc1) (as2, pc2) =
  let equiv_attr_opt a1 a2 = match a1, a2 with
    | None, None -> true
    | Some aloc1, Some aloc2 -> equiv_lookup d (aloc1, pc1) (aloc2, pc2)
    | _, _ -> false
  in
     equiv_attr_opt as1.code as2.code
  && equiv_lookup d (as1.proto, pc1) (as2.proto, pc2)
  && equiv_symbool d (as1.extensible, pc1) (as2.extensible, pc2)
  && equiv_symstring d (as1.klass, pc1) (as2.klass, pc2)
  && equiv_attr_opt as1.primval as2.primval

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

and equiv_lookup d (vloc1, pc1) (vloc2, pc2) =
  equiv_value d (sto_lookup_val vloc1 pc1, [pc1])
               (sto_lookup_val vloc2 pc2, [pc2])

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

(* Given two result values and the list of contexts from which
 * they were produced, returns true if there is a pair (v1,pc1) from
 * the first set that is equivalent to a pair (v2,pc2) from the second. *)
let equiv_class (v1, pcs1) (v2, pcs2) =
  equiv_value max_equiv_depth (v1, pcs1) (v2, pcs2)

let rec equiv_classes classes1 classes2 =
  match classes1 with
  | [] -> []
  | cls :: rest -> 
    try
      Equiv (cls, List.find (equiv_class cls) classes2)
        :: equiv_classes rest classes2
    (* short circuit if no equiv class found *)
    with Not_found -> [ Diff (cls, classes2) ]
 
(** MAIN                                 *)
(*****************************************)

let sym_compare path1 path2 : unit =
  let (rets1, exns1) = sym_eval path1 in
  let (rets2, exns2) = sym_eval path2 in
  (*printf "Got results 1: %d results\n" (List.length rets1);*)
  (*printf "Got results 2: %d results\n" (List.length rets2);*)
  
  (* Group returned pcs into equivalence classes by value *)
  let classes1 = classes_of_results rets1 in
  let classes2 = classes_of_results rets2 in

  printf "%s\n" ">>>>>> Results to compare:";
  List.iter
    (fun (v,pcs) -> printf "%s, " (Ljs_sym_pretty.val_to_string v))
    classes1;
  (*Ljs_sym_z3.print_results (rets1, []);*)
  printf "\n%s\n" "=======";
  List.iter
    (fun (v,pcs) -> printf "%s, " (Ljs_sym_pretty.val_to_string v))
    classes2;
  (*Ljs_sym_z3.print_results (rets2, []);*)
  printf "\n%s\n" "<<<<<< Comparing...";

  (* Check for result set equivalence.
   * Our metric will be, for each return value in classes1,
   * does there exist an equivalent return value in classes2 *)
  let results = equiv_classes classes1 classes2 in
  printf "Comparison result: %b\n"
    (List.for_all
       (fun r -> match r with Equiv _ -> true | _ -> false)
       results);
  print_comp_results results

let _ =
  if Array.length Sys.argv - 1 <> 2 then
    printf "Usage: sym-compare file1.js file2.js\n"
  else
    sym_compare Sys.argv.(1) Sys.argv.(2)
