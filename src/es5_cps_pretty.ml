open Prelude
open Es5_cps

open Format
open FormatExt

let rec vert_intersperse a lst = match lst with
  | [] -> []
  | [x] -> [x]
  | x :: xs -> squish [x; a] :: (vert_intersperse a xs)

let rec value v = match v with
  | Null _ -> text "null"
  | Undefined _ -> text "undefined"
  | Num (_,_,n) -> text (string_of_float n)
  | String (_,_,s) -> text ("\"" ^ s ^ "\"")
  | True _ -> text "true"
  | False _-> text "false"
  | Id (p,_, x) -> text x
  | Object (p,_, avs, props) ->
    braces (vert [attrsv avs; vert (vert_intersperse (text ",") (map prop props))])
  | Lambda (p,_, ret, exn, xs, e) ->
    vert [squish [text "lam"; parens (horz (text "Ret" :: text ret :: text "," ::
                                              text "Exn" :: text exn :: text ";" :: 
                                              (intersperse (text ",") (map text xs))))];
          braces (exp false e)]

and prim p = match p with
  | GetAttr (p,_, a, o, f) ->
    squish [value o;
            brackets (horz [value f; angles (horz [text (Es5_syntax.string_of_attr a)])])]
  | SetAttr (p,_, a, o, f, v) ->
    squish [value o;
            brackets (squish [value f; angles (horz [text (Es5_syntax.string_of_attr a)]);
                              text "="; value v])]
  | SetBang (p,_, x, e) ->
    horz [text x; text "<-"; value e]
  | Op1 (p,_, op, e) -> 
    squish [text "prim"; parens (horz [text ("\"" ^ op ^ "\","); value e])]
  | Op2 (p,_, op, e1, e2) ->
    squish [text "prim"; parens (horz [text ("\"" ^ op ^ "\","); value e1; text ","; value e2])]
  | DeleteField (p,_, o, f) ->
    squish [value o; brackets (horz [text "delete"; value f])]

and label verbose lbl ret = if verbose then squish [int lbl; text ":"; ret] else ret

and exp verbose e = 
  let exp = exp verbose in match e with
  | LetValue (p,lbl, x, v, body) ->
    label verbose lbl (vert [horz [text "letVal"; vert [parens (horz [text x; text "="; value v])]];
                                 horz [text "in"; vert [exp body]]])
  | RecValue (p,lbl, x, v, body) ->
    label verbose lbl (vert [horz [text "recVal"; vert [parens (horz [text x; text "="; value v])]];
          horz [text "in"; vert [exp body]]])
  | LetPrim (p,lbl, x, pr, body) ->
    label verbose lbl (vert [horz [text "letPrim"; vert [parens (horz [text x; text "="; prim pr])]];
          horz [text "in"; vert [exp body]]])
  | LetRetCont (lbl,ret, x, e, body) ->
    label verbose lbl (vert [horz [text "letRet"; horz [text ret; parens (text x); text "="]; vert [exp e]];
          horz [text "in"; vert [exp body]]])
  | LetExnCont (lbl,exn, x, l, e, body) ->
    label verbose lbl (vert [horz [text "letExn"; horz [text exn; parens (horz [text x; text l]); text "="; vert [exp e]]];
          horz [text "in"; vert [exp body]]])
  | If (p,lbl, c, t, e) -> 
    label verbose lbl (vert [horz [text "if  "; vert [parens (horz [value c])]];
          horz [text "then"; braces (exp t)];
          horz [text "else"; (match e with
	  | If _ -> (exp e)
	  | _ -> braces (exp e))]])
  | AppFun (p,lbl, f, ret, exn, args) ->
    label verbose lbl (squish [value f; parens (squish (text "Ret " :: text ret :: text ", " ::
                                       text "Exn " :: text exn :: text "; " :: 
                                       intersperse (text ", ") (map value args)))])
  | AppRetCont (lbl,r, x) ->
    label verbose lbl (horz [squish [text r; parens (horz [value x])]])
  | AppExnCont (lbl,e, x, l) ->
    label verbose lbl (horz [squish [text e; parens (horz [value x ; text ","; value l])]])
  | Eval (p,lbl, s) -> 
    label verbose lbl (squish [text "@eval"; parens (exp s)])

and attrsv { proto = p; code = c; extensible = b; klass = k } =
  let proto = match p with None -> [] 
    | Some e -> [horz [text "#proto:"; value e]] in
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
                                          text v; text ","; 
                                          text "#writable";  
                                          text (string_of_bool w);
                                          text ",";
                                          text "#configurable";
                                          text (string_of_bool config)])]
  | Accessor ({getter=g; setter=s}, enum, config) ->
    horz [text ("'" ^ f ^ "'"); text ":"; braces (horz [text "#getter";
                                          text g; text ",";
                                          text "#setter";
                                          text s])]
;;
Es5_cps.pretty_print := (fun e fmt -> exp false e fmt)
let cps_value_to_string v = value v Format.str_formatter; Format.flush_str_formatter(); 
