open Es5_eval

module S5 = struct

  open Format
  open SpiderMonkey
  
  module X = Js_to_exprjs
    
  let main () : unit =
    let ast = parse_spidermonkey stdin "stdin" in
    printf "Hello, world\n";


end;;

S5.main ()
