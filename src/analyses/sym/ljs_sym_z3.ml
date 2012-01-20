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

let rec value v store = 
  match v with
  | Null -> text "NULL"
  | Undefined -> text "UNDEF"
  | Num n -> 
    if (n = infinity) then text "(NUM inf)"
    else if (n = neg_infinity) then text "(NUM neg_inf)"
    else if (n <> n) then text "(NUM NaN)"
    else parens (horz [text "NUM"; text (string_of_float n)])
  | String s -> parens (horz [text "STR"; text ("S_" ^ s)]) (* for now; this doesn't support spaces... *)
  | True -> text "(BOOL true)"
  | False -> text "(BOOL false)"
  | VarCell v -> cell (Store.lookup v store) store
  | ObjCell o -> cell (Store.lookup o store) store
  | Closure func -> text "(FUN closure)"
  (* | Lambda (p,lbl, ret, exn, xs, e) -> *)
  (*   label verbose lbl (vert [squish [text "lam"; parens (horz (text "Ret" :: text ret :: text "," :: *)
  (*                                                                text "Exn" :: text exn :: text ";" ::  *)
  (*                                                                (intersperse (text ",") (map text xs))))]; *)
  (*                            braces (exp e)]) *)
  | Sym id -> text id

and cell c store = 
  match c with
  | Value v -> horz [squish [text "&<"; value v store; text ">"]]
  | ObjLit o ->
    let (avs, props) = o in
    (*    horz [(braces (vert [attrsv avs;  *) (* ignoring avs for the moment *)
    parens (
      horz [text "OBJ";
            parens 
              (horz [text "js2Field";
                     List.fold_left (fun acc (f, p) ->
                       let value = 
                         match p with
                         | Data ({value=v; writable=w}, enum, config) -> 
                           parens (horz [text "Data"; (value v store); 
                                         text (string_of_bool w);
                                         text (string_of_bool enum); 
                                         text (string_of_bool config)])
                         | Accessor ({getter=g; setter=s}, enum, config) -> 
                           parens (horz [text "Accessor";  (value g store);
                                         (value s store);
                                         text (string_of_bool enum); 
                                         text (string_of_bool config)])
                       in parens (vert [horz[text "store"; acc]; horz[parens (horz[text "s"; text f]); value]]))
                    (text "mtObj") (IdMap.bindings props)])])


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

and exp e store = 
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
  | Concrete v -> value v store
  | SId id -> text id
  | SOp1 (op, e) -> 
    let (t, ret) = Ljs_sym_delta.typeofOp1 op in
    uncastFn ret (parens (horz [text (prim_to_z3 op); castFn t (exp e store)]))
  | SOp2 (op, e1, e2) ->
    let (t1, t2, ret) = Ljs_sym_delta.typeofOp2 op in
    uncastFn ret (parens (horz [text (prim_to_z3 op); castFn t1 (exp e1 store); castFn t2 (exp e2 store)]))
  | SApp (f, args) ->
    parens (horz ((exp f store) :: (map (fun a -> exp a store) args)))
  | SLet (id, e1) ->
    parens(horz [text "assert"; parens(horz[text "="; text id; exp e1 store])])
  | SCastJS (t, e) -> castFn t (exp e store)
  | SUncastJS (t, e) -> uncastFn t (exp e store)
  | SNot e -> parens (horz [text "not"; exp e store])
  | SAnd es -> parens (horz (text "and" :: (map (fun e -> exp e store) es)))
  | SOr es -> parens (horz (text "or" :: (map (fun e -> exp e store) es)))
  | SImplies (pre, post) -> parens (horz [text "=>"; exp pre store; exp post store])
  | SAssert e -> parens (horz [text "assert"; exp e store])
  | SIsMissing e ->
    parens (horz [text "="; exp e store; text "ABSENT"])
  | SGetField (id, f) ->
    uncastFn TAny (parens(horz [text "select"; (parens(horz [text "field2js"; castFn TObj (text id);])); castFn TString (text f)]))

and attrsv store { proto = p; code = c; extensible = b; klass = k } =
  let proto = [horz [text "#proto:"; value p store]] in
  let code = match c with None -> [] 
    | Some e -> [horz [text "#code:"; value e store]] in
  brackets (vert (map (fun x -> squish [x; (text ",")])
                    (proto@
                       code@
                       [horz [text "#class:"; text ("\"" ^ k ^ "\"")]; 
                        horz [text "#extensible:"; text (string_of_bool b)]])))
    
(* TODO: print and parse enum and config *)
and prop store (f, prop) = match prop with
  | Data ({value=v; writable=w}, enum, config) ->
    horz [text ("'" ^ f ^ "'"); text ":"; braces (horz [text "#value"; 
                                                        value v store; text ","; 
                                                        text "#writable";  
                                                        text (string_of_bool w);
                                                        text ",";
                                                        text "#configurable";
                                                        text (string_of_bool config)])]
  | Accessor ({getter=g; setter=s}, enum, config) ->
    horz [text ("'" ^ f ^ "'"); text ":"; braces (horz [text "#getter";
                                                        value g store; text ",";
                                                        text "#setter";
                                                        value s store])]
;;
let to_string v store = exp v store Format.str_formatter; Format.flush_str_formatter() 


let is_num t l = SApp(SId "isNum", [t; l])
let is_undef t l = SApp(SId "isUndef", [t; l])
let is_null t l = SApp(SId "isNull", [t; l])
let is_absent t l = SApp(SId "isAbsent", [t; l])
let is_bool t l = SApp(SId "isBool", [t; l])
let is_str t l = SApp(SId "isStr", [t; l])
let is_fun t l = SApp(SId "isFun", [t; l])
let is_objcell t l = SApp(SId "isObjCell", [t; l])
let is_varcell t l = SApp(SId "isVarCell", [t; l])
let is_obj t l = SApp(SId "isObj", [t; l])

let lookup_store t l = SApp(SId "lookup", [t; l])

let lookup_field o f = SApp(SId "lookupField", [o; f])
let add_dataField o f v w e c = SApp(SId "addField", [o; f; v; w; e; c])
let update_dataField o f v = SApp(SId "updateField", [o; f; v])

  
  
let log_z3 = true

(* communicating with Z3 *)


let is_sat (p : ctx) : bool =
  let z3prelude = "\
(declare-sort Str)
(declare-sort Fun)
(declare-sort Fields)
(declare-datatypes ()
 ((Attr Config Enum Writable Value Getter Setter)))
(declare-datatypes ()
 ((JS
   (NUM (n Real))
   (UNDEF)
   (NULL)
   (BOOL (b Bool))
   (STR (s Str))
   (FUN (f Fun))
   (OBJ (fields Fields)))
  (Prop
   (ABSENT)
   (Data (value JS) (writable Bool) (enumerable Bool) (config Bool))
   (Accessor (getter JS) (setter JS) (enumerable Bool) (config Bool)))))
(declare-fun js2Field ((Array Str Prop)) Fields)
(declare-fun field2js (Fields) (Array Str Prop))
(assert (forall ((f Fields)) (= (js2Field (field2js f)) f)))
(declare-fun get_field (Fields Str) Prop)
(declare-fun get_attr (Fields Str Attr) JS)
(declare-fun typeof (JS) Str)
(declare-fun prim->str (JS) Str)
(declare-fun hasOwnProperty (Fields Str) Bool)
(declare-const mtObj (Array Str Prop))
(assert (= mtObj ((as const (Array Str Prop)) ABSENT)))
(define-fun neg_inf () Real (- 0.0 1234567890.984321))
(define-fun inf () Real 12345678.321)
(define-fun NaN () Real 876545689.24565432)
" in


  let (inch, outch) = Unix.open_process "z3 -smt2 -in" in 
  let { constraints = cs; vars = vs; store = store } = p in      
  if log_z3 then Printf.printf "%s\n" z3prelude;
  output_string outch z3prelude; output_string outch "\n";
  IdMap.iter
    (fun id (tp, hint) -> 
      let assertion =
        match tp with
        | TNull -> Printf.sprintf "(assert (is-NULL %s))\n" id
        | TUndef -> Printf.sprintf "(assert (i-UNDEF %s))\n" id
        | TString -> Printf.sprintf "(assert (is-STR %s))\n" id
        | TBool -> Printf.sprintf "(assert (is-BOOL %s))\n" id
        | TNum -> Printf.sprintf "(assert (is-NUM %s))\n" id
        | TObj -> Printf.sprintf "(assert (exists ((f Fields)) (= %s (OBJ f))))\n" id
        | TFun arity -> Printf.sprintf "(assert (is-FUN %s))\n" id
        | TAny -> ""
        | TData -> Printf.sprintf 
          "(assert (is-Data %s))\n" id
        | TAccessor -> Printf.sprintf
          "(assert (is-Accessor %s))\n" id
      in
      if log_z3 then Printf.printf "(declare-const %s JS) ;; \"%s\"\n" id hint;
      output_string outch (Printf.sprintf "(declare-const %s JS) ;; \"%s\"\n" id hint);
      if log_z3 then Printf.printf "%s" assertion;
      output_string outch assertion;
    )
    vs; 
  
  let (lets, rest) = List.partition (fun pc -> match pc with SLet _ -> true | _ -> false) cs in
  let print_pc pc = 
    if log_z3 then Printf.printf "%s\n" (to_string pc store);
    output_string outch 
      (Printf.sprintf "%s\n" (to_string pc store)) in
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
    
