open Prelude
open Ljs_sym_values
open FormatExt

(*type trace_pt = Pos.t * label*) (* from values *)
type path = trace_pt list
type trace =
  | TEmpty
  | TResult of value result list
  | TBranch of Pos.t * (label * trace) list

let rec trace t = match t with
  | TEmpty -> text "<empty>"
  | TResult results -> begin
    horz (intersperse (text "|") (map
      (fun result ->
        match result with
        | Value (v, pc) -> text (Ljs_sym_pretty.val_to_string v)
        | Exn (ev, pc) -> begin
          match ev with
          | Throw v -> horz [text "Exn:";
                             text (Ljs_sym_pretty.val_to_string v)]
          | _ -> text "Exn"
        end
        | Unsat pc -> text "<unsat>")
      results))
  end
  | TBranch (pos, branches) ->
    vert (text (Pos.string_of_pos pos)
      :: (map (fun (label, t) ->
                horz [text label; text ":"; trace t])
            branches))

let trace_to_string = to_string trace

(* Returns the list where the oldval associated with the first occurrence
 * of key is replaced with (replace oldval). If key not in the list, appends the pair *)
let rec replace_assoc (key : 'a) (replace : ('b option -> 'b)) (assoc : ('a * 'b) list)
      : ('a * 'b) list =
  match assoc with
  | [] -> [(key, replace None)]
  | (k, v)::assoc ->
    if k = key
    then (key, (replace (Some v)))::assoc
    else (k, v)::(replace_assoc key replace assoc)

let rec trace_of_path (res, path) =
  match path with
  | [] -> TResult [res]
  | (pos, label)::path ->
    TBranch (pos, [(label, trace_of_path (res, path))])

let exn_hack_id =
  let count = ref 0 in
  (fun () -> incr count; "exnhack" ^ string_of_int !count)

(* Optimized for when trace2 is linear. *)
let rec merge_traces trace1 trace2 = match trace1, trace2 with
  | TEmpty, t
  | t, TEmpty -> t
  | TResult rs1, TResult rs2 -> TResult (rs2 @ rs1)
  | TBranch (pos1, branches1), TBranch (pos2, branches2) ->
    if pos1 <> pos2 then failwith "Pos mismatch" else
    let new_branches =
      fold_left
        (fun branches1 (label2, subt2) ->
           replace_assoc label2
             (fun subt1 -> match subt1 with
              | Some subt1 -> merge_traces subt1 subt2
              | None -> subt2)
             branches1)
        branches1 branches2 in
    TBranch (pos1, new_branches)
  (* Hack for when exceptions pop up without first performing
   * a proper branching. We shove them into whatever sibling branching
   * we come across. The pos in that branch won't necessarily represent
   * the pos where the exception was thrown, but it might be close. *)
  | TBranch (pos, branches), TResult r 
  | TResult r, TBranch (pos, branches) ->
      TBranch (pos, (exn_hack_id(), TResult r)::branches) 

let trace_from_results results =
  let results = map (fun (res, path) -> (res, List.rev path)) results in
  let traces = map trace_of_path results in
  fold_left merge_traces TEmpty traces

