open Ljs_sym_values

(* pretty printing for Z3 format *)
open Prelude

open Format
open FormatExt

let rec vert_intersperse a lst = match lst with
  | [] -> []
  | [x] -> [x]
  | x :: xs -> squish [x; a] :: (vert_intersperse a xs)

let rec value v = 
  match v with
  | Null -> text "null"
  | Undefined -> text "undefined"
  | Num n -> text (string_of_float n)
  | String s -> text ("\"" ^ s ^ "\"")
  | True -> text "true"
  | False -> text "false"
  | VarCell v -> horz [squish [text "&<"; value (!v); text ">"]]
  | ObjCell o ->
    let (avs, props) = !o in
    horz [squish [text "@"; (braces (vert [attrsv avs; 
                                           vert (vert_intersperse (text ",") 
                                                   (map prop (IdMap.bindings props)))]))]]
  | Closure func -> text "(closure)"
  (* | Lambda (p,lbl, ret, exn, xs, e) -> *)
  (*   label verbose lbl (vert [squish [text "lam"; parens (horz (text "Ret" :: text ret :: text "," :: *)
  (*                                                                text "Exn" :: text exn :: text ";" ::  *)
  (*                                                                (intersperse (text ",") (map text xs))))]; *)
  (*                            braces (exp e)]) *)
  | Sym e -> exp e

(* and prim verbose p =  *)
(*   let value = value verbose in *)
(*   match p with *)
(*   | GetAttr (p,lbl, a, o, f) -> *)
(*     label verbose lbl (squish [value o; *)
(*                                brackets (horz [value f; angles (horz [text (Ljs_syntax.string_of_attr a)])])]) *)
(*   | SetAttr (p,lbl, a, o, f, v) -> *)
(*     label verbose lbl (squish [value o; *)
(*                                brackets (squish [value f; angles (horz [text (Ljs_syntax.string_of_attr a)]); *)
(*                                                  text "="; value v])]) *)
(*   | SetBang (p,lbl, x, e) -> *)
(*     label verbose lbl (horz [text x; text "<-"; value e]) *)
(*   | MutableOp1 (p,lbl, op, e) ->  *)
(*     label verbose lbl (squish [text "mutPrim"; parens (horz [text ("\"" ^ op ^ "\","); value e])]) *)
(*   | DeleteField (p,lbl, o, f) -> *)
(*     label verbose lbl (squish [value o; brackets (horz [text "delete"; value f])]) *)

and exp e = 
  match e with
  | Concrete v -> value v
  | SId id -> text id
  | SOp1 (op, e) -> 
    parens (horz [text op; exp e])
  | SOp2 (op, e1, e2) ->
    parens (horz [text op; exp e1; exp e2])
  | SApp (f, args) ->
    parens (horz ((exp f) :: (map exp args)))
  | SLet (id, e1, e2) ->
    vert [parens(horz [text "declare-const"; text id; text "JS"; exp e1]);
          exp e2]
    

and attrsv { proto = p; code = c; extensible = b; klass = k } =
  let proto = [horz [text "#proto:"; value p]] in
  let code = match c with None -> [] 
    | Some e -> [horz [text "#code:"; value e]] in
  brackets (vert (map (fun x -> squish [x; (text ",")])
                  (proto@
                    code@
                    [horz [text "#class:"; text ("\"" ^ k ^ "\"")]; 
                     horz [text "#extensible:"; text (string_of_bool b)]])))
              
(* TODO: print and parse enum and config *)
and prop (f, prop) = match prop with
  | Data ({value=v; writable=w}, enum, config) ->
    horz [text ("'" ^ f ^ "'"); text ":"; braces (horz [text "#value"; 
                                          value v; text ","; 
                                          text "#writable";  
                                          text (string_of_bool w);
                                          text ",";
                                          text "#configurable";
                                          text (string_of_bool config)])]
  | Accessor ({getter=g; setter=s}, enum, config) ->
    horz [text ("'" ^ f ^ "'"); text ":"; braces (horz [text "#getter";
                                          value g; text ",";
                                          text "#setter";
                                          value s])]
;;
let to_string v = value v Format.str_formatter; Format.flush_str_formatter() 





(* communicating with Z3 *)
let is_sat (p : path) : bool =
  let (inch, outch) = Unix.open_process "z3 -smt2 -in" in 
  let { constraints = cs; vars = vs; } = p in      
  List.iter
    (fun (id, tp) -> 
      Printf.printf "(declare-const %s %s)\n" id tp;
      output_string outch (Printf.sprintf "(declare-const %s %s)" id tp))
    vs;
  
  List.iter
    (fun pc -> 
      Printf.printf "(assert %s)\n" (to_string (Sym pc));
      output_string outch 
        (Printf.sprintf "(assert %s)" (to_string (Sym pc))))
    cs;
  
  output_string outch "(check-sat)";
  close_out outch;
  flush stdout;
  let res = input_line inch in
  close_in inch; 
  Printf.printf "z3 said: %s\n" res;
  (res = "sat")
    
let rec collect_vars vars exp : var list =
  match exp with
  | Concrete(_) -> vars
  | SId(id) -> 
    if List.mem_assoc id vars then vars 
    else ((id,"JS") :: vars) (* no type info! *)
  | SOp1(op, e) -> collect_vars vars e
  | SOp2(op, e1, e2) -> collect_vars (collect_vars vars e1) e2
  | SApp(e1, e2s) -> List.fold_left collect_vars (collect_vars vars e1) e2s
  | _ -> vars
