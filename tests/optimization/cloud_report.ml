open Sys
open Filename
open Printf
open Str

let analyze_dir = ref ""
let base_dir = ref ""

let sections =
  let names = ["07"; "08"; "09"; "10"; "11"; "12"; "13"; "14"; "15"] in
  let nonstrict = List.map (fun (s) -> sprintf "ch%s-nonstrict" s) names in
  let strict = List.map (fun (s) -> sprintf "ch%s-strict" s) names in
  List.append strict nonstrict

let set_analyze cmd (str : string) =
  if is_directory str then
    analyze_dir := str
  else
    failwith (sprintf "analyze dir %s not found" str)

let set_base cmd (str : string) =
  if is_directory str then
    base_dir := str
  else
    failwith (sprintf "base dir %s not found" str)

(* Read a file into a string *)
let string_of_file file_name =
  let inchan = open_in file_name in
  let buf = String.create (in_channel_length inchan) in
  really_input inchan buf 0 (in_channel_length inchan);
  close_in inchan;
  buf

(* compare the result *)
type result_t = Pass | Fail | Empty
type cmp_t = Same | Diff | NotFound
type name_t = string (* file name and directory name *)
type path_t = string (* abs path or relative path *)

let analyze_result_hash : (path_t, result_t) Hashtbl.t = Hashtbl.create 16000
let base_result_hash : (path_t, result_t) Hashtbl.t = Hashtbl.create 16000

let hash_to_list (hash : (path_t, result_t) Hashtbl.t) : (path_t * result_t) list =
  Hashtbl.fold (fun k v lst -> (k,v) :: lst) hash []

let get_section_files (section_mode : name_t) (path : path_t) : name_t list =
  let section_path = Filename.concat path section_mode in
  Array.to_list (readdir section_path)

(* compare the result in one directory *)
(* to check whether the name ends with ".result" *)
let dot_result = Str.regexp ".*\\.result$"
let dot_optimizeinfo = Str.regexp ".*\\.optimizeinfo"
let is_result_file name : bool =
  Str.string_match dot_result name 0
let is_optimize_file name : bool =
  Str.string_match dot_optimizeinfo name 0

let fail_exp = Str.regexp "\\(.*failed.*in.*mode[ =]*$\\)\\|\\(.*was expected to fail.*, but did.*\\)"
let pass_exp = Str.regexp "\\(.*passed.*in.*mode\\)\\|\\(.*failed in.*as expected\\)"
(* test case *)
let test_regexp () = 
  let pass_text1 = "=== ch08/8.7/8.7.2/8.7.2-3-a-1gs failed in strict mode as expected ===" in
  let pass_text2 = "=== ch08/8.7/8.7.2/8.7.2-1-s passed in strict mode ===" in
  let fail_text1 = "=== ch09/9.7/S9.7_A2.2 failed in non-strict mode ===" in
  let fail_text2 = "=== ch07/7.8/7.8.3/7.8.3-3gs was expected to fail in strict mode, but didn't ===" in
  let assertpass t = assert (Str.string_match pass_exp t 0) in
  let assertfail t = assert (Str.string_match fail_exp t 0) in
  (* check pass_exp *)
  assertpass pass_text1;
  assertpass pass_text2;
  assert (not (Str.string_match pass_exp fail_text1 0));
  assert (not (Str.string_match pass_exp fail_text2 0));
  (* check fail_exp *)
  assertfail fail_text1;
  assertfail fail_text2;
  assert (not (Str.string_match fail_exp pass_text1 0));
  assert (not (Str.string_match fail_exp pass_text2 0))

let _ = test_regexp ()
    
let get_file_result filepath : result_t =
  let buf = string_of_file filepath in
  if Str.string_match pass_exp buf 0 then
    Pass
  else if Str.string_match fail_exp buf 0 then
    Fail
  else
    Empty

let get_section_result (section_mode : name_t) (path : path_t) (result_hash : (path_t, result_t) Hashtbl.t) : unit =
  let get_files_result (paths : path_t list) (result_hash : (path_t, result_t) Hashtbl.t) : unit =
    List.iter (fun path ->
        let result = get_file_result path in
        Hashtbl.replace result_hash path result) 
      paths
  in
  let files : name_t list = get_section_files section_mode path in
  let files : name_t list = List.filter (fun fname -> is_result_file fname) files in
  let files : path_t list = List.map (fun fname -> 
      (Filename.concat path (Filename.concat section_mode fname))) files in
  get_files_result files result_hash

(* get cache or call get_section_result *)
let get_base_result (section_mode : name_t) (path : path_t) result_hash : unit =
  get_section_result section_mode path result_hash

let num_pass_fail (lst : (path_t * result_t) list) : (int * int) =
  let passed = List.filter (fun (_, r) -> r = Pass) lst in
  let failed = List.filter (fun (_, r) -> r = Fail) lst in
  List.length passed, List.length failed

let compare_section (section : name_t) : unit =
  assert ( List.mem section sections );
  get_section_result section !analyze_dir analyze_result_hash;
  get_base_result section !base_dir base_result_hash;
  let analyze_result_list = hash_to_list analyze_result_hash in
  let base_result_list = hash_to_list base_result_hash in
  let analyze_pass, analyze_fail = num_pass_fail analyze_result_list in
  let base_pass, base_fail = num_pass_fail base_result_list in
  print_endline ("section: " ^ section);
  printf "%-10s%-40s%-30s\n" "" (Filename.basename !analyze_dir) (Filename.basename !base_dir);
  printf "%-10s%15d%30d\n" "PASS"  analyze_pass base_pass;
  printf "%-10s%15d%30d\n" "FAIL"  analyze_fail base_fail;
  printf "%!"
    


  (*
  let analyze_cmp_list : (path_t * cmp_t) list = List.map (fun (file, result) ->
      try
        let base_result = Hashtbl.find base_result_hash file in
        (file, if base_result = result then Same else Diff)
      with _ -> (file, NotFound)
    ) analyze_result_list
  in
  List.sort (fun (p1,_) (p2,_) -> compare p1 p2) analyze_cmp_list
*)

let compare cmd (sec : string) =
  let _ = if !analyze_dir = "" || !base_dir= "" then
      raise (Arg.Bad "-set-analyze and -set-base is required") in
  match sec with
  | "all" ->
    List.iter (fun section -> compare_section section) sections
  | sec when (List.mem sec sections) ->
    compare_section sec
  | _ ->
    raise (Arg.Bad "e.g. -compare ch15-nonstrict") 

(* ============================= produce performance ============================= *)
let performance cmd () =
  let _ = if !analyze_dir = "" then
      raise (Arg.Bad "-set-analyze is required") in
  ()


let cmpsection cmd (sec : string) =
  ()
  

let strCmd optName func desc =
  (optName, Arg.String (func optName), desc)

let unitCmd optName func desc =
  (optName, Arg.Unit (func optName), desc)

let main () : unit =
  Arg.parse
    [
      strCmd "-set-analyze" set_analyze
        "<dir> which directory contains the ready-to-analyze files";
      strCmd "-set-base" set_base
        "<dir> which directory contains the baseline files";
      strCmd "-compare" compare
        "<which section-strict>|<which-section-nonstrict>|<all> compare pass/fail results in section";
      unitCmd "-performance" performance
        "produce optimization performance(measured by AST node shrinkage) results";
      strCmd "-cmpsection" cmpsection
        "list files that passed in base directory but failed in analyze directory";
    ]
    (fun s -> printf "anot: %s" s)
    ("Note: argument order matters.")

let _ = main()
