open Prelude
open Ljs_sym_values

open Format
open FormatExt

let rec vert_intersperse a lst = match lst with
  | [] -> []
  | [x] -> [x]
  | x :: xs -> squish [x; a] :: (vert_intersperse a xs)

let rec value v store = 
  match v with
  | Null -> text "null"
  | Undefined -> text "undefined"
  | Num n -> text (string_of_float n)
  | String s -> text ("\"" ^ s ^ "\"")
  | True -> text "true"
  | False -> text "false"
  | VarCell v -> cell (Store.lookup v store) store
  | ObjCell o -> cell (Store.lookup o store) store
  | Closure func -> text "(closure)"
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
    horz [squish [text "@"; (braces (vert [attrsv store avs; 
                                           vert (vert_intersperse (text ",") 
                                                   (map (prop store) (IdMap.bindings props)))]))]]


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
(*   | DeleteField (p,lbl, o, f) -> *)
(*     label verbose lbl (squish [value o; brackets (horz [text "delete"; value f])]) *)
and castFn t e store = match t with
    | TNum -> parens (horz [text "num"; exp e store])
    | TBool -> parens (horz [text "bool"; exp e store])
    | TString -> parens (horz [text "string"; exp e store])
    | TFun _ -> parens (horz [text "fun"; exp e store])
    | TObj -> parens (horz [text "fields"; exp e store])
    | _ -> exp e store
and uncastFn t e store = match t with
    | TNum -> parens (horz [text "NUM"; exp e store])
    | TBool -> parens (horz [text "BOOL"; exp e store])
    | TString -> parens (horz [text "STR"; exp e store])
    | TFun _ -> parens (horz [text "FUN"; exp e store])
    | TObj -> parens (horz [text "OBJ"; exp e store])
    | _ -> exp e store 

and exp e store = 
  match e with
  | Concrete v -> value v store
  | STime t -> horz[text "time:"; int t]
  | SLoc l -> horz[text "&"; text (Store.print_loc l)]
  | SId id -> text id
  | SOp1 (op, e) -> 
    (squish [text "prim"; parens (horz [text ("\"" ^ op ^ "\","); exp e store])])
  | SOp2 (op, e1, e2) ->
    (squish [text "prim"; parens (horz [text ("\"" ^ op ^ "\","); 
                                        exp e1 store; text ","; exp e2 store])])
  | SApp (f, args) ->
    (squish [exp f store; parens (squish (intersperse (text ", ") (map (fun a -> exp a store) args)))])
  | SLet (id, e1) -> 
    squish [text "let"; text id; text "="; exp e1 store]
  | SCastJS (t, e) -> castFn t e store
  | SUncastJS (t, e) -> uncastFn t e store
  | SNot e -> parens (horz [text "!"; exp e store])
  | SAnd es -> parens (horz (text "&&" :: (map (fun e -> exp e store) es)))
  | SOr es -> parens (horz (text "||" :: (map (fun e -> exp e store) es)))
  | SAssert e -> parens (horz [text "ASSERT"; exp e store])
  | SImplies (pre, post) -> parens (horz [exp pre store; text "=>"; exp post store])
  | SIsMissing e ->
    horz [exp e store; text "IS MISSING"]
  | SGetField (id, f) ->
    squish [text id; text "."; text f]

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
let to_string v store = value v store Format.str_formatter; Format.flush_str_formatter(); 
