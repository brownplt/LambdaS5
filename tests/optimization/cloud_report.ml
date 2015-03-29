open Sys
open Filename
open Printf
open Str

let analyze_dir = ref ""
let base_dir = ref ""
let latex_format = ref false

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

let string_of_result = function
  | Pass -> "Pass"
  | Fail -> "Fail"
  | Empty -> "Empty"

let analyze_result_hash : (name_t, result_t) Hashtbl.t = Hashtbl.create 16000
let base_result_hash : (name_t, result_t) Hashtbl.t = Hashtbl.create 16000

let hash_to_list (hash : (name_t, result_t) Hashtbl.t) : (path_t * result_t) list =
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
  let get_files_result (fnames : name_t list) (result_hash : (name_t, result_t) Hashtbl.t) : unit =
    List.iter (fun fname ->
        let path = Filename.concat path (Filename.concat section_mode fname)in
        let result = get_file_result path in
        Hashtbl.replace result_hash fname result)
      fnames
  in
  let files : name_t list = get_section_files section_mode path in
  let files : name_t list = List.filter (fun fname -> is_result_file fname) files in
  get_files_result files result_hash

(* get cache or call get_section_result *)
let get_base_result (section_mode : name_t) (path : path_t) result_hash : unit =
  get_section_result section_mode path result_hash

let num_pass_fail (lst : (name_t * result_t) list) : (int * int) =
  let passed = List.filter (fun (_, r) -> r = Pass) lst in
  let failed = List.filter (fun (_, r) -> r = Fail) lst in
  List.length passed, List.length failed

let compare_section (section : name_t) : unit =
  assert ( List.mem section sections );
  let analyze_result_hash = Hashtbl.create 7000 in
  let base_result_hash = Hashtbl.create 7000 in
  get_section_result section !analyze_dir analyze_result_hash;
  get_base_result section !base_dir base_result_hash;
  (* NOTE: here the two lists below may contains Empty(No test to run) files *)
  let analyze_result_list = hash_to_list analyze_result_hash in
  let base_result_list = hash_to_list base_result_hash in
  let analyze_pass, analyze_fail = num_pass_fail analyze_result_list in
  let base_pass, base_fail = num_pass_fail base_result_list in
  if not (!latex_format) then begin
    print_endline ("section: " ^ section);
    printf "%-10s%-40s%-30s\n" "" (Filename.basename !analyze_dir) (Filename.basename !base_dir);
    printf "%-10s%15d%30d\n" "PASS"  analyze_pass base_pass;
    printf "%-10s%15d%30d\n" "FAIL"  analyze_fail base_fail;
    printf "%!"
  end else begin
    (*section | transformed pass | base pass | percentage *)
    printf "%s & %d & %d & %s \\\\\n\\hline\n%!"
      section analyze_pass base_pass 
        (if base_pass = 0 then
           sprintf "N/A"
        else
           sprintf "%.1f\\%%" ((float_of_int analyze_pass) /. (float_of_int base_pass) *. 100.0))
  end

(* ============================= produce performance ============================= *)
type count_t = int * int
type optinfo_t = count_t list
type fileinfo_t = (name_t, optinfo_t) Hashtbl.t

(* filename -> [(env1,usr1);(env2,usr2)...] *)
let get_file_optinfo filepath (hash : fileinfo_t) : unit =
  let get_env_count line : int =
    let env_count = regexp ".*env(\\([0-9]+\\)).*" in
    try
      int_of_string (Str.replace_first env_count "\\1" line)
    with _ -> failwith (sprintf "get env count error: %s" line)
  in
  let get_usr_count line : int =
    let usr_count = regexp ".*usr(\\([0-9]+\\)).*" in
    try
      int_of_string (Str.replace_first usr_count "\\1" line)
    with _ -> failwith (sprintf "get usr count error: %s" line)
  in
  let parse_line line : count_t =
    get_env_count line, get_usr_count line
  in
  let parse_buf buf : count_t list =
    let lines = Str.split (Str.regexp "\n") buf in
    List.map parse_line lines
  in
  try
    let buf = string_of_file filepath in
    let numbers : count_t list = parse_buf buf in
    let name = (Filename.chop_extension
                  (Filename.basename filepath)) in
    Hashtbl.replace hash name numbers
  with _ -> ()

let get_section_optinfo (section_mode : name_t) (path : path_t) : fileinfo_t =
  let files : name_t list = get_section_files section_mode path in
  let files : name_t list = List.filter (fun fname -> is_optimize_file fname) files in
  let files : path_t list = List.map (fun fname ->
      (Filename.concat path (Filename.concat section_mode fname))) files in
  let file_optinfo : fileinfo_t = Hashtbl.create 16000 in
  List.iter (fun f -> get_file_optinfo f file_optinfo) files;
  file_optinfo

(* give a list of int(or float) i1,i2,i3,..., compute
   (i1-i2)/i1, (i2-i3)/i2, ...
   NOTE: (i1-in)/i1 is also returned as the last element
*)
let get_ratio (lst : int list) : float list =
  let len = List.length lst in
  let div ith jth =
    (float_of_int ((List.nth lst ith) - (List.nth lst jth))) /.
    (float_of_int (List.nth lst ith))
  in
  let rec ratio index : float list =
    if index = len - 1 then []
    else 
      (div index (index+1)) :: ratio (index + 1)
  in
  if len = 0 then []
  else
    let result = (ratio 0) @ [div 0 (len-1)] in
    List.map (fun f->f *. 100.) result

let pretty_config (path : path_t) =
  let buf = string_of_file path in
  let args = Str.split (Str.regexp " +") (String.trim buf) in
  let args = List.filter (fun arg -> 
      (*Str.string_match (Str.regexp "^-count-nodes.*") arg 0 ||*)
      Str.string_match (Str.regexp "^-opt-.*") arg 0) args in
  printf "p0: base AST nodes\n";
  let phases = List.mapi (fun i arg-> sprintf "p%d: %s" (i+1) arg) args in
  List.iter (fun p->printf "%s\n" p) phases

(* pretty print the hash table(filename -> optinfo_t) *)
let pretty_fileinfo (hash : fileinfo_t) : unit =
  let fnames = Hashtbl.fold (fun fname _ lst -> fname :: lst) hash [] in
  let fnames = List.sort compare fnames in (* sort the name *)
  (* title varies with fname contents, if fname is bad then we need automatically choose another one *)
  let pretty_title fname : unit =
    let optinfo = Hashtbl.find hash fname in
    (* get index list for title phase name *)
    let nums = List.mapi (fun i _ -> i) optinfo in
    printf "%25s      " " ";
    List.iter (fun n->printf "%7s" (sprintf "p%d" n)) nums;
    printf " | ";
    List.iter2 (fun a b->printf "%8s"
                   (if a < b then
                     (sprintf "p%d->p%d" a b)
                   else
                     (sprintf "p%d->p%d" b a))
               ) nums ((List.tl nums) @ [List.hd nums]);
    printf "\n%!";
    (* ====== print underlines ===== *)
    printf "%25s======" (String.make 25 '=');
    List.iter (fun n->printf "%7s" (String.make 7 '=')) nums;
    printf "===";
    List.iter2 (fun a b->printf "========") nums nums;
    printf "\n%!"
  in
  let pretty_one_file fname =
    try
      let optinfo = Hashtbl.find hash fname in
      let env, usr = List.split optinfo in
      let env_ratio = get_ratio env in
      let usr_ratio = get_ratio usr in
      let print_total_saving () =
        let len = List.length env in
        if len >= 1 then
          let basen = (List.hd env) + (List.hd usr) in
          let finaln = (List.nth env (len-1)) + (List.nth usr (len-1)) in
          printf "%8.1f%%\n%!" ( 100.0 *. (float_of_int (basen - finaln))
                                 /. (float_of_int basen))
      in
      (* print env count *)
      printf "%25s env: " fname;
      List.iter (fun n->printf "%7d" n) env;
      printf " |";
      (* print env count saving *)
      List.iter (fun f->printf "%8.1f" f) env_ratio;
      printf "\n%!";
      
      (* print usr count *)
      printf "%25s usr: " fname;
      List.iter (fun n->printf "%7d" n) usr;
      printf " |";
      (* print usr count saving *)
      List.iter (fun f->printf "%8.1f" f) usr_ratio;
      print_total_saving();
      (* print end line *)
      printf "\n%25s\n%!" "--------------------"
    with _ -> failwith ("errors occur when processing " ^ fname)
  in
  if fnames = [] then
    printf "empty directory"
  else begin
    pretty_title (List.nth fnames 0);
    List.iter pretty_one_file fnames
  end

let get_last_one (lst : 'a list) : 'a =
  let len = List.length lst in
  let _ = assert (len <> 0) in
  List.nth lst (len-1)

let get_first_one (lst : 'a list) : 'a =
  let len = List.length lst in
  let _ = assert (len <> 0) in
  List.nth lst 0
    
let get_mean (lst : float list) : float =
  let sum = List.fold_left (+.) 0. lst in
  sum /. (float_of_int (List.length lst))

let get_median (lst : float list) : float =
  let len = List.length lst in
  if (len mod 2) = 1 then
    let middle = len - 1
                 |> float_of_int
                 |> (fun n -> n /. 2.0)
                 |> int_of_float in
    List.nth lst middle
  else
    let middle1 = len
                 |> float_of_int
                 |> (fun n -> n /. 2.0)
                 |> int_of_float in
    let middle2 = middle1 - 1 in
    ((List.nth lst middle1) +. (List.nth lst middle2)) /. 2.0

(* ratio: max, min, mean, median *)
let pretty_summary (use_latex: bool) (section: string) (hash : fileinfo_t) : unit =
  let calculate (lst : int list) : float =
    (* given [i1, i2, ...in], calculate (i1-in)/i1 *)
    let last = (get_last_one lst)
               |> float_of_int in
    let fst =  (get_first_one lst)
               |> float_of_int in
    ((fst -. last) /. fst) *. 100.0
  in
  let get_max_min_mean_median (lst : float list) : (float * float * float * float) =
    get_last_one lst,
    get_first_one lst,
    get_mean lst,
    get_median lst
  in
  let print_info (prefix : string) (lst : float list) : unit =
    let max, min, mean, median =
      get_max_min_mean_median lst in
    if use_latex then
      if prefix = "All" then
        (* latex only needs the overall summary *)
        printf "%s & %.2f & %.2f & %.2f & %.2f \\\\\n\\hline\n%!" section max min mean median
      else
        ()
    else
      begin 
        printf "%s: Max %8.2f, Min %8.2f, Mean %8.2f, Median %8.2f\n%!"
          prefix max min mean median
      end
  in
  let print_empty_info () : unit =
    (if use_latex then
      printf "%s & N/A & N/A & N/A & N/A \\\\\n\\hline\n%!" section
    else
      printf "\nSection %s is empty" section);
    printf "\n%!";
  in
  (* for each file, get overall shrinkage of #env, #usr, #total *)
  let shrinkage : (float * float * float) list = Hashtbl.fold
      (fun fname optinfo lst ->
         let env, usr = List.split optinfo in
         (*let _ = printf "get shrinkage info of file %s\n%!" fname in
         let _ = printf "env length: %d\n" (List.length env) in
         let _ = calculate env in
         let _ = printf "get shrinkage info of file %s\n%!" fname in
         let _ = calculate usr in
         let _ = printf "get shrinkage info of file %s\n%!" fname in*)
         (calculate env,
          calculate usr,
          calculate (List.map2 (fun e u -> e + u) env usr)) :: lst)
      hash []
  in
  if shrinkage = [] then
    print_empty_info ()
  else
    (* in increasing orders *)
    let env_lst = List.sort compare
        (List.map (fun (a,_,_)->a) shrinkage) in
    let usr_lst = List.sort compare
        (List.map (fun (_,b,_)->b) shrinkage) in
    let all_lst = List.sort compare
        (List.map (fun (_,_,c)->c) shrinkage) in
    begin
      if not use_latex then
        printf "\nSection: %s\n" section;
      print_info "Env" env_lst;
      print_info "Usr" usr_lst;
      print_info "All" all_lst
    end
    
  
  
         
let diff_section (section : name_t) : unit =
  assert (List.mem section sections);
  let analyze_result_hash = Hashtbl.create 7000 in
  let base_result_hash = Hashtbl.create 7000 in
  get_section_result section !analyze_dir analyze_result_hash;
  get_base_result section !base_dir base_result_hash;
  let diff : name_t list = Hashtbl.fold (fun fname result lst ->
      try
        if result <> Empty then begin
          let analyze_result = Hashtbl.find analyze_result_hash fname in
          if result <> analyze_result then
            fname :: lst
          else lst
        end
        else lst
      with _ -> fname :: lst
    ) base_result_hash []
  in
  printf "Section: %s[#diff: %d]\n" section (List.length diff);
  (*List.iter (fun fname -> printf "%s\n%!" fname) diff;*)
  List.iter (fun fname ->
      let name = Filename.chop_extension
          (Filename.basename fname) in
      let baseinfo =
        try 
          (string_of_result (Hashtbl.find base_result_hash fname))
        with _ -> "x"
      in
      let analyzeinfo =
        try 
          (string_of_result (Hashtbl.find analyze_result_hash fname))
        with _ -> "x"
      in
      printf "%-30s base:%-10s analyze:%-10s\n" name baseinfo analyzeinfo)
    diff;
  printf "\n%!"

(* ========== CMD ========== *)
let existing_sections () =
  List.filter (fun sec ->
      Sys.file_exists (Filename.concat !analyze_dir sec)) sections
  
let compare cmd (sec : string) =
  let _ = if !analyze_dir = "" || !base_dir= "" then
      raise (Arg.Bad "-set-analyze and -set-base is required") in
  let sections = existing_sections () in
  (*let rec compare_sec = function
    | [] -> ()
    | hd :: tl ->
      let 
  in*)
  match sec with
  | "all" ->
    List.iter (fun section -> compare_section section) sections
  | sec when (List.mem sec sections) ->
    compare_section sec
  | _ ->
    raise (Arg.Bad "e.g. -compare ch15-nonstrict") 


let performance cmd () =
  let _ = if !analyze_dir = "" then
      raise (Arg.Bad "-set-analyze is required") in
  let rec pretty_sec rest_sections = match rest_sections with
    | [] -> ()
    | hd :: tl ->
      let fileinfo = get_section_optinfo hd !analyze_dir in
      printf "\nSection: %s\n" hd;
      let config = Filename.concat !analyze_dir "config.txt" in
      pretty_config config;
      pretty_fileinfo fileinfo;
      pretty_sec tl
  in
  let sections = existing_sections () in
  pretty_sec sections

let summary cmd (sec : string) =
  let _ = if !analyze_dir = "" then
      raise (Arg.Bad "-set-analyze is required") in
  let print_summary sec =
    let fileinfo = get_section_optinfo sec !analyze_dir in
    pretty_summary (!latex_format) sec fileinfo;
  in
  let sections = existing_sections () in
  match sec with
  | "all" ->
    List.iter (fun section -> print_summary section) sections
  | sec when (List.mem sec sections) ->
    print_summary  sec
  | _ ->
    raise (Arg.Bad (sprintf "section %s is not found" sec))


let list_section_diff cmd (sec : string) =
  let _ = if !analyze_dir = "" || !base_dir= "" then
      raise (Arg.Bad "-set-analyze and -set-base is required") in
  let sections = existing_sections () in
  match sec with
  | "all" ->
    List.iter (fun section -> diff_section section) sections
  | sec when (List.mem sec sections) ->
    diff_section sec
  | _ ->
    raise (Arg.Bad (sprintf "section %s is not found" sec))

let use_latex_format cmd () =
  latex_format := true

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
      unitCmd "-use-latex-format" use_latex_format
        "if '-summary' is followed, summary is printed as latex tabular";
      strCmd "-list-section-diff" list_section_diff
        "list files that passed in base directory but failed in analyze directory";
      strCmd "-summary" summary
        "<section>|<all> give summary for specific section(or all sections)";
    ]
    (fun s -> printf "anot: %s" s)
    ("Note: argument order matters.")

let _ = main()
