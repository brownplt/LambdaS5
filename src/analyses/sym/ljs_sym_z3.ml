open Ljs_sym_values

let is_sat (p : path) : bool =
  let (inch, outch) = Unix.open_process "z3 -smt2 -in" in 
  match p with
    | { constraints = cs; vars = vs; } -> 
      
      List.iter
        (fun (id, tp) -> output_string outch 
          (Printf.sprintf "(declare-fun %s () %s)" id tp))
        vs;
      
      List.iter
        (fun pc -> output_string outch 
          (Printf.sprintf "(assert %s)" (pretty_sym_exp pc)))
        cs;

      output_string outch "(check-sat)";
      close_out outch;
      let res = input_line inch in
      close_in inch; 
      (res = "sat")
        
let rec collect_vars vars exp : var list =
  match exp with
  | Concrete(_) -> vars
  | SId(id) -> 
    if List.mem_assoc id vars then vars 
    else ((id,"Real") :: vars) (* no type info! *)
  | SOp1(op, e) -> collect_vars vars e
  | SOp2(op, e1, e2) -> collect_vars (collect_vars vars e1) e2
  | SApp(e1, e2s) -> List.fold_left collect_vars (collect_vars vars e1) e2s
