open Prelude
open Es5
open Es5_eval
open Es5_syntax
open Es5_parser
open Es5_pretty
open Es5_values

module S5 = struct

  open Format
  open SpiderMonkey
  open Js_to_exprjs
  open Exprjs_to_ljs

  let srcES5 = ref (Es5_syntax.Undefined dummy_pos)

  let load_s5 (path : string) : unit =
    srcES5 := Es5_syntax.Seq (dummy_pos, !srcES5,
		              Es5.parse_es5 (open_in path) path)

  let print_s5 () : unit =
    Es5_pretty.exp !srcES5 std_formatter;
    print_newline ()

  let eval () : unit =
    let v = Es5_eval.eval_expr !srcES5 in
    printf "%s" (pretty_value v);
    print_newline ()

  let desugar_js (path : string) : unit = 
    let ast = parse_spidermonkey (open_in path) path in
    let open Exprjs_syntax in
    let exprjsd = srcElts ast (Null (dummy_pos)) in
    let desugard = exprjs_to_ljs exprjsd in
    srcES5 := desugard
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
        ("-pretty", Arg.Unit print_s5,
         "pretty-print s5 code");
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
