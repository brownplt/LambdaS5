open OUnit
open Format
open Str

(* A test is a LJS .es5 file with the expected results
 * in a comment on the first line of the file. Expected
 * results should be delimited by commas, and thus should
 * not have commas within them. Example:
 * // 1, 3, "error", %%a
 *)

type value = String of string | Num of float | Sym of string

module EValue =
struct
  type t = value
  let compare v1 v2 = match v1, v2 with
    | Sym id1, Sym id2 -> 0
    | _, _ -> compare v1 v2
  let pp_printer fmtr = function
    | String str -> pp_print_string fmtr str
    | Sym id -> pp_print_string fmtr id
    | Num num -> pp_print_float fmtr num
  let pp_print_sep = OUnitDiff.pp_comma_separator
end

module ListValue = OUnitDiff.ListSimpleMake(EValue);;

let wrap_val v =
      try Num (float_of_string v)  
      with Failure _ ->
        if string_before v 2 = "%%" ||
           (String.length v >= 6 && string_before v 6 = "NewSym")
        then Sym v
        else String v
  
let rec parse_results chan =
  try 
    let line = input_line chan in
    let i = String.length(line) in
    if (String.sub line 0 (min i 7) = "Result:")
    then wrap_val (String.sub line 8 (i-9)) :: parse_results chan
    else parse_results chan
  with End_of_file -> [] 

let make_test es5_path = es5_path >:: (fun () ->
  skip_if (Str.string_match (regexp "sym/obj") es5_path 0) "sym obj test has too many branches";
  (*
  (* Convert JS to AST *)
  let ast_path = js_path ^ ".ast" in
  let js2ast = "../../../bin/js ../../json_print.js sym/harness/" ^
    js_path ^ " > " ^ ast_path in
  if Sys.command js2ast <> 0
  then todo ("Could not convert JS to AST: " ^ js_path)
  else 

  (* Run the symbolic evaluator on the AST *)
  let res_path = js_path ^ ".result" in
  let symeval = "../../../src/s5.d.byte" ^
    " -desugar " ^ ast_path ^
    " -env ../../../envs/es5.env" ^
    " -sym-eval > " ^ res_path in
  Sys.remove ast_path;
  *)
  
  (* Read first line as expected results *)
  let chan = open_in es5_path in
  let line = input_line chan in
  let expected = List.map (global_replace (regexp "^ +") "")
    (List.map (global_replace (regexp " +$") "")
    (split (regexp "[,]+") (string_after line 2))) in
  close_in chan;

  (* Run sym eval on LJS file *)
  let res_path = es5_path ^ ".result" in
  let symeval = "../../../src/s5.d.byte" ^
    " -s5 " ^ es5_path ^
    " -sym-eval > " ^ res_path in
  let _ = Sys.command symeval in

  (* Get the results *)
  let chan = open_in res_path in
  let results = parse_results chan in
  close_in chan; 
  let eq =
    ListValue.assert_equal
      (ListValue.of_list (List.sort compare
        (List.map wrap_val expected)))
      (ListValue.of_list (List.sort compare results))
  in Sys.remove res_path; eq
);;

let test_dir dir =
  let r = regexp_string ".result" in
  List.fold_left
    (fun tests file ->
      let path = (dir ^ "/" ^ file) in
      let i = (String.length file) - 7 in
      if i >= 0 && string_match r file i
      then (Sys.remove path; tests)
      else make_test path :: tests)
    []
    (Array.to_list (Sys.readdir dir))

let tests = "All Tests" >:::  [
  "Concrete Tests" >::: test_dir "concrete";
  "Sym Tests" >::: test_dir "sym"
];;

let _ = run_test_tt_main tests
