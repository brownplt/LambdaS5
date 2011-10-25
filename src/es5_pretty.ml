open Prelude
open Es5_syntax

open Format
open FormatExt

let rec vert_intersperse a lst = match lst with
  | [] -> []
  | [x] -> [x]
  | x :: xs -> squish [x; a] :: (vert_intersperse a xs)

let rec exp e = match e with
  | Null _ -> text "null"
  | Undefined _ -> text "undefined"
  | Num (_,n) -> text (string_of_float n)
  | String (_,s) -> text ("\"" ^ s ^ "\"")
  | True _ -> text "true"
  | False _-> text "false"
  | Id (p, x) -> text x
  | Object (p, avs, props) ->
    braces (vert [attrsv avs; vert (vert_intersperse (text ",") (map prop props))])
  | SetField (p, o, f, v, args) ->
    squish [exp o; brackets (horz [exp f; text "="; exp v; text ","; exp args])]
  | GetField (p, o, f, args) ->
    squish [exp o; brackets (horz [exp f; text ","; exp args])]
  | DeleteField (p, o, f) ->
    squish [exp o; brackets (horz [text "delete"; exp f])]
  | GetAttr (p, a, o, f) ->
    squish [exp o;
            brackets (horz [exp f; angles (horz [text (string_of_attr a)])])]
  | SetAttr (p, a, o, f, v) ->
    squish [exp o;
            brackets (squish [exp f; angles (horz [text (string_of_attr a)]);
                              text "="; exp v])]
  | SetBang (p, x, e) ->
    horz [text x; text ":="; exp e]
  | Op1 (p, op, e) -> 
    squish [text "prim"; parens (horz [text ("\"" ^ op ^ "\","); exp e])]
  | Op2 (p, op, e1, e2) ->
    squish [text "prim"; parens (horz [text ("\"" ^ op ^ "\","); exp e1; text ","; exp e2])]
  | If (p, c, t, e) -> 
    horz [text "if"; vert [parens (horz [exp c]);
                           braces (exp t);
                           text "else";
			   (match e with
			   | If _ -> (exp e)
			   | _ -> braces (exp e))]]
  | App (p, f, args) ->
    squish [exp f; parens (vert (vert_intersperse (text ",") (map exp args)))]
  | Seq (p, e1, e2) ->
    vert [squish [exp e1; text ";"]; exp e2]
  | Let (p, x, e, body) ->
    horz [text "let"; vert [parens (horz [text x; text "="; exp e]);
                            opt_braces body]]
  | Rec (p, x, e, body) -> 
    horz [text "rec"; vert [parens (horz [text x; text "="; exp e]);
                            opt_braces body]]
  | Label (p, l, e) ->
    vert [horz [text "label"; text l; text ":"]; braces (exp e)]
  | Break (p, l, e) ->
    horz [text "break"; text l; exp e]
  | TryCatch (p, body, catch) ->
    vert [text "try"; braces (exp body); text "catch"; braces (exp catch)]
  | TryFinally (p, body, fin) ->
    vert [text "try"; braces (exp body); text "finally"; braces (exp fin)]
  | Throw (p, e) ->
    horz [text "throw"; exp e]
  | Lambda (p, xs, e) ->
    vert [squish [text "func"; parens (horz (intersperse (text ",") (map text xs)))];
          braces (exp e)]
  | Eval (p, s) -> 
      squish [text "@eval"; parens (exp s)]
  | Hint (p, hint, e) ->
      parens (vert [squish [text "/*: "; text hint; text "*/"];
	                 exp e])

and opt_braces expr = match expr with
  | Seq _ -> braces (exp expr)
  | _ -> exp expr

and attrsv { proto = p; code = c; extensible = b; klass = k } =
  let proto = match p with None -> [] 
    | Some e -> [horz [text "#proto:"; exp e]] in
  let code = match c with None -> [] 
    | Some e -> [horz [text "#code:"; exp e]] in
  brackets (vert (map (fun x -> squish [x; (text ",")])
                  (proto@
                    code@
                    [horz [text "#class:"; text ("\"" ^ k ^ "\"")]; 
                     horz [text "#extensible:"; text (string_of_bool b)]])))
              
(* TODO: print and parse enum and config *)
and prop (f, prop) = match prop with
  | Data ({value=v; writable=w}, enum, config) ->
    horz [text ("'" ^ f ^ "'"); text ":"; braces (horz [text "#value"; 
                                          exp v; text ","; 
                                          text "#writable";  
                                          text (string_of_bool w);
                                          text ",";
                                          text "#configurable";
                                          text (string_of_bool config)])]
  | Accessor ({getter=g; setter=s}, enum, config) ->
    horz [text ("'" ^ f ^ "'"); text ":"; braces (horz [text "#getter";
                                          exp g; text ",";
                                          text "#setter";
                                          exp s])]

