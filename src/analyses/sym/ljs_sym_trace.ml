open Prelude
open Ljs_sym_values
open FormatExt


(*type trace_pt = Pos.t * label*) (* from values *)
type path = trace_pt list
type trace =
  | TEmpty
  | TResult of value result
  | TBranch of Pos.t * (label * trace) list

(* Returns the list where the value associated with the first occurrence
 * of key is replaced with newval. If key not in the list, appends the pair *)
let rec replace_assoc (key : 'a) (newval : 'b) (assoc : ('a * 'b) list)
      : ('a * 'b) list =
  match assoc with
  | [] -> [(key, newval)]
  | (k, v)::assoc ->
    if k = key
    then (key, newval)::assoc
    else (k, v)::(replace_assoc key newval assoc)

let rec insert_path (res, path) trace : trace =
  match trace with
  | TEmpty -> begin
    match path with
    | [] -> TResult res
    | (pos, label)::path ->
      TBranch (pos, [(label, insert_path (res, path) TEmpty)])
  end
  | TResult _ -> failwith "Tried to insert duplicate path"
  | TBranch (bpos, branches) -> begin
    match path with
    | [] -> failwith "Tried to insert empty path into branch."
    | (pos, label)::path ->
      if bpos <> pos then failwith "Pos mismatch" else
      let branch = try List.assoc label branches
                   with Not_found -> TEmpty in
      TBranch (bpos,
               replace_assoc label
                 (insert_path (res, path) branch)
                 branches)
  end

let trace_from_results results =
  let results = map (fun (res, trace) -> (res, List.rev trace)) results in
  fold_left (flip insert_path) TEmpty results

let rec trace t = match t with
  | TEmpty -> text "<empty>"
  | TResult result -> begin
    match result with
    | Value (v, pc) -> text (Ljs_sym_pretty.val_to_string v)
    | Exn (ev, pc) -> begin
      match ev with
      | Throw v -> horz [text "Exn:"; text (Ljs_sym_pretty.val_to_string v)]
      | _ -> text "Exn"
    end
    | Unsat pc -> text "Unsat"
  end
  | TBranch (pos, branches) ->
    vert (text (Pos.string_of_pos pos)
      :: (map (fun (label, t) ->
                horz [text label; text ":"; trace t])
            branches))

let trace_to_string = to_string trace

