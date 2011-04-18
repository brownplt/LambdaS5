open Es5_eval
open Es5_parser
open Es5_pretty

module S5 = struct

  open Format
  open SpiderMonkey
  open Js_to_exprjs

  let main () : unit =
    let rec ast = parse_spidermonkey stdin "stdin" in
    let desugared = srcElts ast in
    printf "Hello, world\n";


end;;

S5.main ()
