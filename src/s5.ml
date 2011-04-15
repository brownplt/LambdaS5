open Es5_eval
open Es5_parser
open Es5_pretty

module S5 = struct

  open Format
  open SpiderMonkey
  
  module X = Js_to_exprjs
    
    

  let main () : unit =
    let ast = parse_spidermonkey stdin "stdin" in
    printf "Hello, world\n";


end;;

S5.main ()
