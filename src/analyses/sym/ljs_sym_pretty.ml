open Prelude
open Ljs_sym_values

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
    (squish [text "prim"; parens (horz [text ("\"" ^ op ^ "\","); exp e])])
  | SOp2 (op, e1, e2) ->
    (squish [text "prim"; parens (horz [text ("\"" ^ op ^ "\","); 
                                        exp e1; text ","; exp e2])])
  | SApp (f, args) ->
    (squish [exp f; parens (squish (intersperse (text ", ") (map exp args)))])
  | SLet (id, e1, e2) -> 
    vert [squish [text "let"; text id; text "="; exp e1];
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
let to_string v = value v Format.str_formatter; Format.flush_str_formatter(); 
