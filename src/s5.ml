open Prelude
open Es5
open Es5_eval
open Es5_syntax
open Es5_parser
open Es5_pretty

module S5 = struct

  open Format
  open SpiderMonkey
  open Js_to_exprjs

  let srcES5 = ref (Es5_syntax.Undefined dummy_pos)

  let load_s5 (path : string) : unit =
    srcES5 := Es5_syntax.Seq (dummy_pos, !srcES5,
		              Es5.parse_es5 (open_in path) path)

  let print_s5 () : unit =
    Es5_pretty.exp !srcES5 std_formatter;
    print_newline ()

  let eval () : unit =
    Es5_eval.eval_expr !srcES5;
    print_newline ()

  let main () : unit =
    Arg.parse
      [
        ("-s5", Arg.String load_s5,
         "<file> load file as s5");
        ("-pretty", Arg.Unit print_s5,
         "pretty-print s5 code");
        ("-eval", Arg.Unit eval,
         "evaluate code")
      ]
      load_s5
      "Usage: s5 <action> <path> ...";;
(*
    let rec ast = parse_spidermonkey stdin "stdin" in
    printf "Hello, world\n";
*)
end;;
S5.main ()
