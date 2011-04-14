open Es5_eval
open Es5_eval_test

module S5 = struct

  open Format
  open SpiderMonkey
    
  let main () : unit =
    let ast = parse_spidermonkey stdin "stdin" in
    printf "Hello, world\n";
    test ()


end;;

S5.main ()
