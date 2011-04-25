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
  open SpiderMonkey
  open Js_to_exprjs
  open Exprjs_to_ljs

  let srcES5 = ref (Es5_syntax.Undefined dummy_pos)
  let srcEJS = ref (Exprjs_syntax.Undefined (dummy_pos))

  let load_s5 (path : string) : unit =
    srcES5 := Es5_syntax.Seq (dummy_pos, !srcES5,
		              Es5.parse_es5 (open_in path) path)

  let print_s5 (choice : string) : unit =
    match choice with 
    | "es5" -> Es5_pretty.exp !srcES5 std_formatter; print_newline ()
    | "exprjs" -> Exprjs_pretty.exp !srcEJS std_formatter; print_newline ()
    | _ -> failwith "bad option string"

  let eval () : unit =
    let v = Es5_eval.eval_expr !srcES5 in
    printf "%s" (pretty_value v);
    print_newline ()

  let desugar_js (path : string) : unit = 
    let ast = parse_spidermonkey (open_in path) path in
    let open Exprjs_syntax in
    let exprjsd = srcElts ast (Undefined (dummy_pos)) in
    let desugard = exprjs_to_ljs exprjsd in
    srcEJS := exprjsd; srcES5 := desugard
    (*
  let desugar_js (path : string) : unit =
    let ast = parse_spidermonkey (open_in path) path in
    let exprjsd = srcElts ast (ObjectExpr (dummy_pos, [])) in
    let desugard = exprjs_to_ljs exprjsd in
    srcES5 := desugard
    *)

  let main () : unit =
    Arg.parse
      [
        ("-desugar", Arg.String desugar_js,
        "<file> desugar json ast file");
        ("-s5", Arg.String load_s5,
         "<file> load file as s5");
        ("-print", Arg.String print_s5,
         "<exprjs|s5|both> pretty-print s5/exprjs code");
        ("-eval", Arg.Unit eval,
        "evaluate code");
      ]
      load_s5
      "Usage: s5 <action> <path> ...";;
(*
    let rec ast = parse_spidermonkey stdin "stdin" in
    let desugared = srcElts ast in
    printf "Hello, world\n";
*)
end;;
S5.main ()
