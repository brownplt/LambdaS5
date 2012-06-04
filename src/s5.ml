open Prelude
open Ljs
open Ljs_eval
open Ljs_syntax
open Ljs_parser
open Ljs_pretty
open Ljs_values
open Exprjs_pretty

module S5 = struct

  open Format
  open Js_to_exprjs
  open Exprjs_to_ljs
  open Exprjs_syntax
  open Js_syntax
  open Format
  open FormatExt

  let srcJS = ref [Js_syntax.Stmt (Js_syntax.Expr (dummy_pos, Js_syntax.Lit
(dummy_pos, Js_syntax.Null)))]
  let srcES5 = ref (Ljs_syntax.Undefined dummy_pos)
  let srcEJS = ref (Exprjs_syntax.Undefined (dummy_pos))
  let cpsES5 = ref (Ljs_cps.AppRetCont(Ljs_cps.Label.dummy, Ljs_cps.RetId(Ljs_cps.Label.dummy,"fake"), Ljs_cps.Id(dummy_pos,Ljs_cps.Label.dummy,"fake")))

  let jsonPath = ref ""

  let load_s5 (path : string) : unit =
    srcES5 := Ljs_syntax.Seq (dummy_pos, !srcES5,
		              Ljs.parse_es5 (open_in path) path)

  let set_json (path : string) : unit =
    jsonPath := path

  let get_json () = !jsonPath

  let print_s5 (choice : string) : unit =
    match choice with 
    | "es5" -> Ljs_pretty.exp !srcES5 std_formatter; print_newline ()
    | "exprjs" -> Exprjs_pretty.exp !srcEJS std_formatter; print_newline ()
    | "cps5" -> Ljs_cps_pretty.exp true !cpsES5 std_formatter; print_newline ()
    | _ -> failwith "bad option string"

  let eval () : unit =
    let (v, _) = Ljs_eval.eval_expr !srcES5 !jsonPath in
    printf "%s" (pretty_value v);
    print_newline ()

  let sym_eval () : unit =
    (* let z3 = Unix.open_process "z3 -smt2 -in" in *)
    (* let (inch, outch) = z3 in begin *)
    let (results, exns) = 
      Ljs_sym_eval.eval_expr !srcES5 !jsonPath 50 Ljs_sym_values.mtPath in
      List.iter
        (fun (v, p) ->
          printf "Result: %s:\n" (Ljs_sym_pretty.val_to_string v);
          List.iter
            (fun c ->
              printf "%s\n" (Ljs_sym_z3.to_string c p))
            p.Ljs_sym_values.constraints;
          (*printf "%s\n" (Ljs_sym_pretty.store_to_string p.Ljs_sym_values.store);*)
          print_newline())
        results;
      List.iter
        (fun (v, p) -> match v with
          | Ljs_sym_values.Throw v ->
            printf "Exn: %s:\n" (Ljs_sym_pretty.val_to_string v)
          | _ -> printf "Exn: something other than a Throw\n")
        exns
  (* close_in inch; close_out outch *)

  let env (path : string) : unit =
    let envFunc = Ljs.parse_es5_env (open_in path) path in
    srcES5 := envFunc !srcES5

  let load_spidermonkey_js (path : string) : unit = 
    let ast = SpiderMonkey.parse_spidermonkey (open_in path) path in
    srcJS := ast

  let get_fvs () : unit =
    let fvs = Js_syntax.used_vars_sel !srcJS in
    printf "%s\n" ((FormatExt.to_string (fun lst -> (vert (map text lst))))
                            (IdSet.elements fvs))
    
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

  (* let cfg () : unit = *)
  (*   let cfg = Cfg.build !cpsES5 in *)
  (*   printf "%s" (Cfg.print_cfg cfg) ; *)
  (*   printf "Done building CFG"; *)
  (*   print_newline () *)

  let cps () =
    cpsES5 := Ljs_cps.cps_tail !srcES5 
      "%error"
      (Ljs_cps.RetId(Ljs_cps.Label.dummy,"%answer"))
  let alphatize () = 
    cpsES5 := fst (Ljs_cps_util.alphatize true (!cpsES5, IdMap.add "%error" 0 (IdMap.add "%answer" 0 IdMap.empty))) 
  let uncps () =
    srcES5 := Ljs_cps.de_cps !cpsES5

  let cps_eval () =
    let v = Cfg.eval !cpsES5 in
    (match v with
    | Cfg.Ans v -> printf "ANSWER %s" (Ljs_cps_values.pretty_bind v)
    | Cfg.Err v -> printf "ERROR %s" (Ljs_cps_values.pretty_bind v));
    print_newline ()

  let cps_abs_eval () =
    let module FX = FormatExt in
    let (finalEnv, finalStore, finalLab) = Cfg_abs.eval !cpsES5 in
    printf "Finished evaling...finalLab is %s\n" (Ljs_cps.Label.toString finalLab);
    let ans = Cfg_abs.getBinding finalLab "%%ANSWER" finalEnv finalStore in
    let err = Cfg_abs.getBinding finalLab "%%ERROR" finalEnv finalStore in
    FX.vert [FX.horz [FX.text "ANSWER <="; Ljs_cps_absdelta.ValueLattice.pretty ans];
             FX.horz [FX.text "ERROR  <="; Ljs_cps_absdelta.ValueLattice.pretty err]] Format.str_formatter;
    printf "%s\n" (Format.flush_str_formatter ())

  let main () : unit =
    Arg.parse
      [
        ("-desugar", Arg.String desugar_spidermonkey_js,
        "<file> desugar json ast file");
        ("-load", Arg.String load_spidermonkey_js,
        "<file> load file as JavaScript AST");
        ("-fvs", Arg.Unit get_fvs,
        "print JavaScript free variables");
        ("-c3desugar", Arg.String desugar_c3_js,
        "<file> desugar json ast file");
        ("-s5", Arg.String load_s5,
         "<file> load file as s5");
        ("-print", Arg.String print_s5,
         "<exprjs|es5|cps5> pretty-print s5/exprjs code");
        ("-cps", Arg.Unit cps,
         "Convert to CPS");
        ("-alph", Arg.Unit alphatize,
         "Alpha-convert the CPS representation");
        ("-un-cps", Arg.Unit uncps,
         "Unwrap from CPS back to \\JS");
        (* ("-cfg", Arg.Unit cfg, *)
	(*  "construct the control flow graph for the current program"); *)
        ("-eval", Arg.Unit eval,
        "evaluate code");
        ("-cps-eval", Arg.Unit cps_eval,
        "evaluate code in CPS form");
        ("-cps-abs-eval", Arg.Unit cps_abs_eval,
        "abstractly evaluate code in CPS form");
        ("-sym-eval", Arg.Unit sym_eval,
        "evaluate code symbolically");
        ("-env", Arg.String env,
         "wrap the program in an environment");
        ("-json", Arg.String set_json,
         "the path to a script that converts js to json")
      ]
      load_s5
      "Usage: s5 <action> <path> ...";;

end;;
S5.main ()
