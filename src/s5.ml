open Prelude
open Es5
open Es5_eval
open Es5_syntax
open Es5_parser
open Es5_pretty
open Es5_values
open Exprjs_pretty

module S5 = struct

  open Format
  open Js_to_exprjs
  open Exprjs_to_ljs
  open Exprjs_syntax

  let srcES5 = ref (Es5_syntax.Undefined dummy_pos)
  let srcEJS = ref (Exprjs_syntax.Undefined (dummy_pos))

  let jsonPath = ref ""

  let load_s5 (path : string) : unit =
    srcES5 := Es5_syntax.Seq (dummy_pos, !srcES5,
		              Es5.parse_es5 (open_in path) path)

  let set_json (path : string) : unit =
    jsonPath := path

  let get_json () = !jsonPath

  let print_s5 (choice : string) : unit =
    match choice with 
    | "es5" -> Es5_pretty.exp !srcES5 std_formatter; print_newline ()
    | "exprjs" -> Exprjs_pretty.exp !srcEJS std_formatter; print_newline ()
    | _ -> failwith "bad option string"

  let eval () : unit =
    let v = Es5_eval.eval_expr !srcES5 !jsonPath in
    printf "%s" (pretty_value v);
    print_newline ()

  let env (path : string) : unit =
    let envFunc = Es5.parse_es5_env (open_in path) path in
    srcES5 := envFunc !srcES5

  let desugar_spidermonkey_js (path : string) : unit = 
    let ast = SpiderMonkey.parse_spidermonkey (open_in path) path in
    let (used_ids, exprjsd) = js_to_exprjs ast (Exprjs_syntax.IdExpr (dummy_pos, "global")) in
    let desugard = exprjs_to_ljs used_ids exprjsd in
    srcEJS := exprjsd; srcES5 := desugard

  let desugar_c3_js (path : string) : unit = 
    let ast = C3.parse_c3 (open_in path) path in
    let (used_ids, exprjsd) = js_to_exprjs ast (Exprjs_syntax.IdExpr (dummy_pos, "global")) in
    let desugard = exprjs_to_ljs used_ids exprjsd in
    srcEJS := exprjsd; srcES5 := desugard

  let main () : unit =
    Arg.parse
      [
        ("-desugar", Arg.String desugar_spidermonkey_js,
        "<file> desugar json ast file");
        ("-c3desugar", Arg.String desugar_c3_js,
        "<file> desugar json ast file");
        ("-s5", Arg.String load_s5,
         "<file> load file as s5");
        ("-print", Arg.String print_s5,
         "<exprjs|s5|both> pretty-print s5/exprjs code");
        ("-eval", Arg.Unit eval,
        "evaluate code");
        ("-env", Arg.String env,
         "wrap the program in an environment");
        ("-json", Arg.String set_json,
         "the path to a script that converts js to json")
      ]
      load_s5
      "Usage: s5 <action> <path> ...";;

end;;
S5.main ()
