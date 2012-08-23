open Prelude
open SpiderMonkey
module S = Ljs_syntax
open Ljs_values
open Exprjs_to_ljs
open Js_to_exprjs
open Unix
open Filename
open Str

(* This function is exactly as ridiculous as you think it is.  We read,
   parse, desugar, and evaluate the string, storing it to temp files along
   the way.  We make no claims about encoding issues that may arise from
   the filesystem. 

   TODO(joe): I have no idea what happens on windows. *)
let desugar jsonPath str = 
  let jsfilename = temp_file "evaljs" ".js" in
  let jsfile = open_out jsfilename in
  (* This puts the appropriate *javascript* in a temp file; the argument
     to eval is a string that we'll try to interpret as javascript *)
  output_string jsfile str;
  close_out jsfile;
  (* We create two files for output; one that will contain
     Spidermonkey's desugared json, and one that will contain stderr
     for reporting parser errors *)
  let jsonfilename = temp_file "evaljson" ".json" in
  let jsonfile = openfile jsonfilename [O_RDWR] 0o600 in
  let errfilename = temp_file "evalerr" ".err" in
  let errfile = openfile errfilename [O_RDWR] 0o600 in
  let (null_stdin, nothing) = pipe () in
  let cleanup () =
    List.iter close [jsonfile; errfile; null_stdin; nothing];
    List.iter unlink [jsfilename; jsonfilename; errfilename] in
  (* This checks for parser errors from Spidermonkey's spew to stderr.
     The environment checks for the thrown string "EvalError" to
     construct the appropriate exception object. *)
  let do_err_check st i =
    let spidermonkey_err = string_of_file errfilename in
    (* We're done with all the files here, so just clean them up *)
    cleanup ();
    let json_err = regexp (quote "SyntaxError") in
    begin try
      ignore (search_forward json_err spidermonkey_err 0);
      S.Throw (Pos.dummy,
        S.App (Pos.dummy, S.Id (Pos.dummy, "%SyntaxError"),
               [S.String (Pos.dummy, "Syntax error in eval()")]))
    with Not_found ->
      raise (PrimErr ([], String
        (sprintf "Fatal eval error, exit code of desugar was: %s %d" st i)))
    end;
  in
  (* If we didn't find an error there, we parse the stdout file as a
     JSON representation of the JS AST (e.g. the string passed to eval()
     was in fact well-formed JavaScript).  Then we desugar it and eval
     it in the same environment and store as the current one. *)
  let do_eval () =
    try
      let ast = parse_spidermonkey (open_in jsonfilename) jsonfilename in
      (* We're done with all the files here, so just clean them up *)
      cleanup ();
      let (used_ids, exprjsd) = 
        js_to_exprjs Pos.dummy ast (Exprjs_syntax.IdExpr (Pos.dummy, "%global"))
      in
      exprjs_to_ljs Pos.dummy used_ids exprjsd
    (* SpiderMonkey parse had some terrible error *)
    with
      (* parse_spidermonkey throws Failures for all errors it can have *)
      | Failure s ->
        cleanup ();
        raise (PrimErr ([], String ("SpiderMonkey parse error: " ^ s)) )
      (* Other exceptions need to flow through from the underlying eval *)
      | e ->
        cleanup ();
        raise e
  in
  (* Now we run the provided json executable with the name of the file
     we wrote the eval JS argument to (TODO(joe): maybe it should read
     this from stdin).
     Then, we send its stdout and stderr to the jsonfile and errfile,
     respectively.  Note that we need to pass two arguments in args to
     please Ocaml create_process, the JS filename being second makes
     it be the $1 argument in the script. *)
  let args = Array.of_list [jsonPath; jsfilename] in
  let pid = create_process jsonPath args null_stdin jsonfile errfile in
  let (_, status) = waitpid [] pid in
  begin match status with
    | WEXITED 0 -> do_eval ()
    | WEXITED i -> do_err_check "WEXITED" i
    | WSIGNALED i -> do_err_check "WSIGNALED" i
    | WSTOPPED i -> do_err_check "WSTOPPED" i
  end

