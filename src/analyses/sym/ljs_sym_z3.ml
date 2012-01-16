open Ljs_sym_values

(* pretty printing for Z3 format *)
open Prelude

open Format
open FormatExt

let rec vert_intersperse a lst = match lst with
  | [] -> []
  | [x] -> [x]
  | x :: xs -> squish [x; a] :: (vert_intersperse a xs)

let prim_to_z3 op = match op with
  | "NOT" -> "not"
  | "stx=" -> "="
  | _ -> op

let rec value v = 
  match v with
  | Null -> text "NULL"
  | Undefined -> text "UNDEF"
  | Num n -> parens (horz [text "NUM"; text (string_of_float n)])
  | String s -> parens (horz [text "STR"; text ("\"" ^ s ^ "\"")])
  | True -> text "(BOOL true)"
  | False -> text "(BOOL false)"
  | VarCell v -> horz [squish [text "&<"; value (!v); text ">"]]
  | ObjCell o ->
    let (avs, props) = !o in
(*    horz [(braces (vert [attrsv avs;  *) (* ignoring avs for the moment *)
    parens (horz [text "OBJ";
                  List.fold_left (fun acc (f, p) ->
                    let value = 
                      match p with
                      | Data ({value=v; writable=w}, enum, config) -> value v
                      (* horz [text ("'" ^ f ^ "'"); text ":"; braces (horz [text "#value";  *)
        (*                                                     value v; text ",";  *)
        (*                                                     text "#writable";   *)
        (*                                                     text (string_of_bool w); *)
        (*                                                     text ","; *)
        (*                                                     text "#configurable"; *)
        (*                                                     text (string_of_bool config)])] *)
                      | Accessor ({getter=g; setter=s}, enum, config) -> text "DUMMY" 
      (* horz [text ("'" ^ f ^ "'"); text ":"; braces (horz [text "#getter"; *)
      (*                                                     value g; text ","; *)
      (*                                                     text "#setter"; *)
      (*                                                     value s])] *)
                    in parens (vert [horz[text "store"; acc]; horz[text f; value]])) 
                    (text "mtObj") (IdMap.bindings props)])
  | Closure func -> text "(FUN closure)"
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
  let castFn t e = match t with
    | TNum -> parens (horz [text "n"; e])
    | TBool -> parens (horz [text "b"; e])
    | TString -> parens (horz [text "s"; e])
    | TFun _ -> parens (horz [text "f"; e])
    | TObj -> parens (horz [text "fields"; e])
    | _ -> e in
  let uncastFn t e = match t with
    | TNum -> parens (horz [text "NUM"; e])
    | TBool -> parens (horz [text "BOOL"; e])
    | TString -> parens (horz [text "STR"; e])
    | TFun _ -> parens (horz [text "FUN"; e])
    | TObj -> parens (horz [text "OBJ"; e])
    | _ -> e in
  match e with
    | Concrete v -> value v
    | SId id -> text id
    | SOp1 (op, e) -> 
      let (t, ret) = Ljs_sym_delta.typeofOp1 op in
      uncastFn ret (parens (horz [text (prim_to_z3 op); castFn t (exp e)]))
    | SOp2 (op, e1, e2) ->
      let (t1, t2, ret) = Ljs_sym_delta.typeofOp2 op in
      uncastFn ret (parens (horz [text (prim_to_z3 op); castFn t1 (exp e1); castFn t2 (exp e2)]))
    | SApp (f, args) ->
      parens (horz ((exp f) :: (map exp args)))
    | SLet (id, e1) ->
      parens(horz [text "assert"; parens(horz[text "="; text id; exp e1])])
    | SIsTrue e ->
      parens(horz [text "assert"; parens(horz[text "b"; exp e])])
    | SIsFalse e ->
      parens(horz [text "assert"; parens(horz[text "not"; parens(horz[text "b"; exp e])])])
    | SGetField (id, f) ->
      uncastFn TAny (parens(horz [text "select"; (parens(horz [text "field2js"; castFn TObj (text id);])); castFn TString (text f)]))

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
  
   
let log_z3 = true

(* communicating with Z3 *)


let is_sat (p : path) : bool =
  let z3prelude = "\
(declare-sort Str)\n\
(declare-sort Fun)\n\
(declare-sort Fields)\n\
(declare-datatypes\n\
 ()\n\
 ((JS\n\
   (NUM (n Real))\n\
   (UNDEF)\n\
   (NULL)\n\
   (ABSENT)\n\
   (BOOL (b Bool))\n\
   (STR (s Str))\n\
   (FUN (f Fun))\n\
   (OBJ (fields Fields)))))\n\
(declare-fun js2Field ((Array Str JS)) Fields)\n\
(declare-fun field2js (Fields) (Array Str JS))\n\
(assert (forall ((f Fields)) (= (js2Field (field2js f)) f)))\n" in

(* (declare-const mtObj Fields)\n\
(assert (= (field2js mtObj) ((as const (Array Str JS)) ABSENT)))  *)

  let (inch, outch) = Unix.open_process "z3 -smt2 -in" in 
  let { constraints = cs; vars = vs; } = p in      
  if log_z3 then Printf.printf "%s\n" z3prelude;
  output_string outch z3prelude; output_string outch "\n";
  IdMap.iter
    (fun id tp -> 
      let assertion =
      match tp with
      | TNull -> Printf.sprintf "(assert (= %s NULL))\n" id
      | TUndef -> Printf.sprintf "(assert (= %s UNDEF))\n" id
      | TString -> Printf.sprintf "(assert (exists ((s Str))(= %s (STR s))))\n" id
      | TBool -> Printf.sprintf "(assert (exists ((b Bool)) (= %s (BOOL b))))\n" id
      | TNum -> Printf.sprintf "(assert (exists ((n Real)) (= %s (NUM n))))\n" id
      | TObj -> Printf.sprintf "(assert (exists ((f Fields)) (= %s (OBJ f))))\n" id
      | TFun arity -> Printf.sprintf "(assert (exists ((f Fun)) (= %s (FUN f))))\n" id
      | TAny -> ""
      in
      if log_z3 then Printf.printf "(declare-const %s JS)\n" id;
      output_string outch (Printf.sprintf "(declare-const %s JS)\n" id);
      if log_z3 then Printf.printf "%s" assertion;
      output_string outch assertion;
    )
    vs; 
  
  let (lets, rest) = List.partition (fun pc -> match pc with SLet _ -> true | _ -> false) cs in
  let print_pc pc = 
      if log_z3 then Printf.printf "%s\n" (to_string (Sym pc));
      output_string outch 
        (Printf.sprintf "%s\n" (to_string (Sym pc))) in
  List.iter print_pc lets;
  List.iter print_pc rest;

  output_string outch "(check-sat)";
  close_out outch;
  flush stdout;
  let res = input_line inch in
  close_in inch; 
  if log_z3 then Printf.printf "z3 said: %s\n" res;
  let res = if (String.length res) > 3 then String.sub res 0 3 else res in (* strip line endings... *)
  (res = "sat")
    
