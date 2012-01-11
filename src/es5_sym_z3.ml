open Prelude
open Es5_sym_values
open Unix

(*  *)
(* let is_sat z3 pcs : bool = *)
(*   printf "insat"; *)
(*   let (inch, outch) = z3 in  *)
(*   output_string outch "(declare-fun %%x () Real)"; *)
(*   List.iter *)
(*     (fun pc -> output_string outch (Printf.sprintf "(assert %s)\n" (pretty_sym_exp pc))) *)
(*     pcs; *)
(*   output_string outch "(check-sat)"; *)
(*   output_string outch "(exit)"; *)
(*   flush_all (); *)
(*   let res = input_line inch in *)
(*   printf "z3 response: %s" res; *)
(*   output_string outch "(reset)"; *)
(*   (res = "sat") *)

let is_sat pcs : bool =
  let (inch, outch) = open_process "z3 -smt2 -in" in 
  output_string outch "(declare-fun %%x () Real)";
  List.iter
    (fun pc -> output_string outch (Printf.sprintf "(assert %s)\n" (pretty_sym_exp pc)))
    pcs;
  output_string outch "(check-sat)";
  close_out outch;
  let res = input_line inch in
  close_in inch; 
  (res = "sat")

