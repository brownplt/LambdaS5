open List
open Prelude
open Ljs
open Ljs_eval
open Ljs_syntax
open Ljs_parser
open Ljs_pretty
open Ljs_pretty_value
open Ljs_values
open Exprjs_pretty

type node =
  | Js of Js_syntax.program
  | Ejs of IdSet.t * Exprjs_syntax.expr
  | Ljs of Ljs_syntax.exp
  | Cps of Ljs_cps.cps_exp
  | Env of (Ljs_syntax.exp -> Ljs_syntax.exp)
  | Store of Ljs_values.store

type nodeType = JsT | EjsT | LjsT | CpsT | EnvT | StoreT

let nodeType (node : node) : nodeType =
  match node with
  | Js _ -> JsT
  | Ejs _ -> EjsT
  | Ljs _ -> LjsT
  | Cps _ -> CpsT
  | Env _ -> EnvT
  | Store _ -> StoreT


let showNodeType (nodeType : nodeType) : string =
  match nodeType with
  | JsT -> "JS"
  | EjsT -> "ExprJS"
  | LjsT -> "S5"
  | CpsT -> "S5-cps"
  | EnvT -> "S5-env"
  | StoreT -> "Heap"


module S5 = struct

  open Format
  open Js_to_exprjs
  open Exprjs_to_ljs
  open Exprjs_syntax
  open Js_syntax
  open Ljs_desugar
  open Format
  open FormatExt


  (* Global Options *)

  let jsonPath = ref "../tests/desugar.sh"
  let stack_trace = ref true

  let set_stack_trace (cmdName : string) (on : bool) : unit =
    stack_trace := on

  let set_json (cmdName : string) (path : string) : unit =
    jsonPath := path


  (* Stack Operations *)

  let stack : node list ref = ref []

  let push (node : node) : unit =
    stack := node :: !stack

  let type_error (cmd : string) (expected : nodeType) (found : node) : 'a =
    failwith (cmd ^ ": expected " ^ showNodeType expected ^ ", but found " ^ showNodeType (nodeType found))

  let underflow_error (cmd : string) : 'a =
    failwith (cmd ^ ": stack underflow")

  let pop cmd : node =
    match !stack with
    | first :: rest ->
        stack := rest;
        first
    | _ -> underflow_error cmd

  let peek cmd : node =
    match !stack with
    | first :: rest -> first
    | _ -> underflow_error cmd

  let pop_js cmd : Js_syntax.program =
    match pop cmd with
    | Js src -> src
    | node -> type_error cmd JsT node

  let pop_ejs cmd : IdSet.t * Exprjs_syntax.expr =
    match pop cmd with
    | Ejs (used_ids, src) -> (used_ids, src)
    | node -> type_error cmd EjsT node

  let pop_ljs cmd : Ljs_syntax.exp =
    match pop cmd with
    | Ljs src -> src
    | node -> type_error cmd LjsT node

  let pop_cps cmd : Ljs_cps.cps_exp =
    match pop cmd with
    | Cps src -> src
    | node -> type_error cmd CpsT node

  let pop_env cmd : Ljs_syntax.exp -> Ljs_syntax.exp =
    match pop cmd with
    | Env src -> src 
    | node -> type_error cmd EnvT node

  let pop_store cmd : Ljs_values.store =
    match pop cmd with
    | Store store -> store
    | node -> type_error cmd StoreT node

  let push_js js = push (Js js)
  let push_ejs (used_ids, ejs) = push (Ejs (used_ids, ejs))
  let push_ljs ljs = push (Ljs ljs)
  let push_cps cps = push (Cps cps)
  let push_env env = push (Env env)
  let push_store store = push (Store store)


  (* Pushing Commands *)

  let load_c3_js cmd path =
    push_js (C3.parse_c3 (open_in path) path)

  let load_js cmd path =
    push_js (SpiderMonkey.parse_spidermonkey (open_in path) path)

  let load_ljs cmd path =
    push_ljs (Ljs.parse_es5 (open_in path) path)

  let load_env cmd path =
    push_env (Ljs.parse_es5_env (open_in path) path)

  let load_internal_env cmd name = match name with
    | "env-vars" ->
      push_env (Env_free_vars.vars_env)
    | _ -> failwith ("Unknown internal environment " ^ name)

  (* Conversion Commands *)

  let js_to_ejs cmd () =
    let convert js = js_to_exprjs Pos.dummy js (Exprjs_syntax.IdExpr (Pos.dummy, "global")) in
    push_ejs (convert (pop_js cmd))

  let ejs_to_ljs cmd () =
    let convert (used_ids, exprjsd) = exprjs_to_ljs Pos.dummy used_ids exprjsd in
    push_ljs (convert (pop_ejs cmd))

  let ljs_to_cps cmd () =
    let convert ljs = Ljs_cps.cps_tail ljs "%error" (Ljs_cps.RetId(Pos.dummy, Ljs_cps.Label.dummy, "%answer")) in
    push_cps (convert (pop_ljs cmd))

  let cps_to_ljs cmd () =
    push_ljs (Ljs_cps.de_cps (pop_cps cmd))

  let ljs_to_env cmd () =
    let src1 = pop_ljs cmd in
    push_env (fun src2 -> Ljs_syntax.Seq (Pos.dummy, src1, src2))

  let alphatize cmd () =
    let alph cps = fst (Ljs_cps_util.alphatize true (cps, IdMap.add "%error" 0 (IdMap.add "%answer" 0 IdMap.empty))) in
    push_cps (alph (pop_cps cmd))


  (* Composition Commands *)

  let apply cmd () =
    let ljs = pop_ljs cmd in
    let env = pop_env cmd in
    push_ljs (env ljs)

  let applyR cmd () =
    let env = pop_env cmd in
    let ljs = pop_ljs cmd in
    push_ljs (env ljs)

  (* This should be defined such that composing and then applying
     has the same effect as applying twice. *)
  let compose cmd () =
    let env1 = pop_env cmd in
    let env2 = pop_env cmd in
    push_env (fun ljs -> env2 (env1 ljs))

  (* Printing Commands *)

  let print_src cmd () =
    match peek cmd with
    | Ejs (used_ids, src) -> Exprjs_pretty.exp src std_formatter; print_newline ()
    | Ljs src -> Ljs_pretty.exp src std_formatter; print_newline ()
    | Cps src -> Ljs_cps_pretty.exp true src std_formatter; print_newline ()
    | node -> failwith (cmd ^ ": print: unsupported source type" ^ showNodeType (nodeType node))

  let print_js_fvs cmd () =
    let js = pop_js cmd in
    let fvs = Js_syntax.used_vars_sel js in
    push_js js; (* put it back *)
    printf "%s\n" ((FormatExt.to_string (fun lst -> (vert (map text lst))))
                      (IdSet.elements fvs))

  let print_store cmd () =
    let store = pop_store cmd in
    Ljs_pretty_value.print_store store


  (* Evaluation Commands *)

  let cps_eval cmd () =
    let cps = pop_cps cmd in
    let v = Cfg.eval cps in
    (match v with
    | Cfg.Ans v -> printf "ANSWER %s" (Ljs_cps_values.pretty_bind v)
    | Cfg.Err v -> printf "ERROR %s" (Ljs_cps_values.pretty_bind v));
    print_newline ()

  let cps_eval_abs cmd () =
    let cps = pop_cps cmd in
    let module FX = FormatExt in
    let (finalEnv, finalStore, finalLab) = Cfg_abs.eval cps in
    printf "Finished evaling...finalLab is %s\n" (Ljs_cps.Label.toString finalLab);
    let ans = Cfg_abs.getBinding finalLab "%%ANSWER" finalEnv finalStore in
    let err = Cfg_abs.getBinding finalLab "%%ERROR" finalEnv finalStore in
    FX.vert [FX.horz [FX.text "ANSWER <="; Ljs_cps_absdelta.ValueLattice.pretty ans];
             FX.horz [FX.text "ERROR  <="; Ljs_cps_absdelta.ValueLattice.pretty err]] Format.str_formatter;
    printf "%s\n" (Format.flush_str_formatter ())

  let ljs_eval cmd () =
    let ljs = pop_ljs cmd in
    let (v, store) = Ljs_eval.eval_expr ljs !jsonPath !stack_trace in
    push_store store;
    printf "%s" (pretty_value v);
    print_newline ()

  let do_sym_eval cmd =
    let ljs = pop_ljs cmd in
    let t1 = Sys.time() in
    let res = Ljs_sym_eval.eval_expr ljs !jsonPath 50 Ljs_sym_values.mtPath in
    let t2 = Sys.time() in
    printf "Spent %f secs in sym eval\n" (t2 -. t1);
    res

  let ljs_sym_eval cmd () =
    (* let z3 = Unix.open_process "z3 -smt2 -in" in *)
    (* let (inch, outch) = z3 in begin *)
    let results = do_sym_eval cmd in
    Ljs_sym_z3.print_results results
  (* close_in inch; close_out outch *)

  let ljs_sym_eval_raw cmd () = 
    let results = do_sym_eval cmd in
    print_string "RAW RESULTS"; print_newline();
    output_value stdout results;
    print_newline()


  (* Main *)

  let command spec optName func desc = (optName, spec (func optName), desc)
  let strCmd = command (fun cmd -> Arg.String cmd)
  let boolCmd = command (fun cmd -> Arg.Bool cmd)
  let unitCmd = command (fun cmd -> Arg.Unit cmd)
  let showType fromTypes toTypes =
    let showTypeList types = String.concat " " (List.map showNodeType types) in
    "(" ^ showTypeList fromTypes ^ " -> " ^ showTypeList toTypes ^ ")"
  let main () : unit =
    Arg.parse
      [
        (* Global Options *)
        strCmd "-set-json" set_json
          "<file> set the path to a script that converts js to json";
        boolCmd "-set-stack-trace" set_stack_trace
          "<bool> enable/disable stack traces from the interpreter";
        (* Loading *)
        strCmd "-js" load_js "<file> load file as JavaScript AST";
        strCmd "-c3-js" load_c3_js "<file> load javascript using C3";
        strCmd "-s5" load_ljs "<file> load file as S5";
        strCmd "-env" load_env "<file> load file as S5-env";
        strCmd "-internal-env" load_internal_env
          ("[env-vars] load an internal environment as S5-env.  " ^
          "Options are currently only env-vars, which sets up the " ^
          "global environment for nested evals");
        (* Conversion *)
        unitCmd "-js-to-ejs" js_to_ejs (showType [JsT] [EjsT]);
        unitCmd "-ejs-to-s5" ejs_to_ljs (showType [EjsT] [LjsT]);
        unitCmd "-js-to-s5"
          (fun cmd () -> js_to_ejs cmd (); ejs_to_ljs cmd ())
          (showType [JsT] [LjsT]);
        unitCmd "-cps" ljs_to_cps (showType [LjsT] [CpsT]);
        unitCmd "-un-cps" cps_to_ljs (showType [CpsT] [LjsT]);
        unitCmd "-to-env" ljs_to_env (showType [LjsT] [EnvT]);
        (* Composition Operations *)
        unitCmd "-apply" applyR (showType [LjsT; EnvT] [LjsT]);
        (* Printing *)
        unitCmd "-alph" alphatize
          "Alpha-convert the CPS representation";
        unitCmd "-print" print_src
          "pretty-print s5 or exprjs code";
        unitCmd "-print-fvs" print_js_fvs
          "print JavaScript free variables";
        unitCmd "-print-heap" print_store
          "print heap after evaluation";
        (* Evaluation *)
        unitCmd "-eval" ljs_eval
          "evaluate S5 code";
        unitCmd "-eval-cps" cps_eval
          "evaluate code in CPS form";
        unitCmd "-eval-cps-abs" cps_eval_abs
          "abstractly evaluate code in CPS form";
        unitCmd "-sym-eval" ljs_sym_eval
          "evaluate code symbolically";
        unitCmd "-sym-eval-raw" ljs_sym_eval_raw
          "evaluate code symbolically and print raw OCaml results";
      ]
      (load_ljs "-s5")
      ("Usage: s5 <action> <path> ...\n"
       ^ "  After loading, sources are held on a stack.\n"
       ^ "  There are five types: "
       ^ String.concat ", " (List.map showNodeType [JsT; EjsT; LjsT; CpsT; EnvT]) ^ "\n");;

end;;
S5.main ()
