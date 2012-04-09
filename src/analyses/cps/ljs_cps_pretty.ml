open Prelude
open Ljs_cps

open Format
open FormatExt

let rec vert_intersperse a lst = match lst with
  | [] -> []
  | [x] -> [x]
  | x :: xs -> squish [x; a] :: (vert_intersperse a xs)

let rec value verbose v = 
  let exp = exp verbose in 
  match v with
  | Null _ -> text "null"
  | Undefined _ -> text "undefined"
  | Num (_,_,n) -> text (string_of_float n)
  | String (_,_,s) -> text ("\"" ^ s ^ "\"")
  | True _ -> text "true"
  | False _-> text "false"
  | Id (p,_, x) -> text x
  | Object (p,lbl, avs, props) -> begin
    match props with
    | [] -> label verbose lbl (braces (attrsv verbose avs))
    | _ -> label verbose lbl (braces (vert [attrsv verbose avs; 
                                            vert (vert_intersperse (text ",") (map prop props))]))
  end
  | Lambda (p,lbl, ret, exn, xs, e) ->
    label verbose lbl (vert [squish [text "lam"; parens (horz (text "Ret" :: text ret :: text "," ::
                                                                 text "Exn" :: text exn :: text ";" :: 
                                                                 (intersperse (text ",") (map text xs))))];
                             braces (exp e)])

and prim verbose p = 
  let value = value verbose in
  match p with
  | GetAttr (p,lbl, a, o, f) ->
    label verbose lbl (squish [value o;
                               brackets (horz [value f; angles (horz [text (Ljs_syntax.string_of_attr a)])])])
  | SetAttr (p,lbl, a, o, f, v) ->
    label verbose lbl (squish [value o;
                               brackets (squish [value f; angles (horz [text (Ljs_syntax.string_of_attr a)]);
                                                 text "="; value v])])
  | GetObjAttr (p,lbl, a, o) ->
    label verbose lbl (squish [value o;
                               angles (horz [text (Ljs_syntax.string_of_oattr a)])])
  | SetObjAttr (p,lbl, a, o, v) ->
    label verbose lbl
      (squish [value o;
               angles (horz [text (Ljs_syntax.string_of_oattr a);
                             text "=";
                             value v])])
  | SetBang (p,lbl, x, e) ->
    label verbose lbl (horz [text x; text "<-"; value e])
  | Op1 (p,lbl, op, e) -> 
    label verbose lbl (squish [text "prim"; parens (horz [text ("\"" ^ op ^ "\","); value e])])
  | Op2 (p,lbl, op, e1, e2) ->
    label verbose lbl (squish [text "prim"; parens (horz [text ("\"" ^ op ^ "\","); 
                                                          value e1; text ","; value e2])])
  | DeleteField (p,lbl, o, f) ->
    label verbose lbl (squish [value o; brackets (horz [text "delete"; value f])])
  | OwnFieldNames (p, lbl, obj) ->
    label verbose lbl (squish [text "get-own-field-names"; parens (value obj)])

and label verbose lbl ret = if verbose then squish [Label.pretty lbl; text ":"; ret] else ret

and print_ret verbose r = match r with
  | RetId(lbl, id) -> label verbose lbl (text id)
  | RetLam(lbl, arg, body) -> 
    label verbose lbl (squish [text "\\"; text arg; text "->"; exp verbose body])
and print_exn verbose e = match e with
  | ExnId(lbl, id) -> label verbose lbl (text id)
  | ExnLam(lbl, arg, lab, body) -> 
    label verbose lbl (squish [text "\\"; text arg; text ","; text lab; text "->"; exp verbose body])

and exp verbose e = 
  let exp = exp verbose in 
  let prim = prim verbose in
  let value = value verbose in match e with
  | LetValue (p,lbl, x, v, body) ->
    label verbose lbl (vert [horz [text "letVal"; parens (horz [text x; text "="; value v])];
                             horz [text "in"; vert [exp body]]])
  | RecValue (p,lbl, x, v, body) ->
    label verbose lbl (vert [horz [text "recVal"; parens (horz [text x; text "="; value v])];
                             horz [text "in"; vert [exp body]]])
  | LetPrim (p,lbl, x, pr, body) ->
    label verbose lbl (vert [horz [text "letPrim"; parens (horz [text x; text "="; prim pr])];
                             horz [text "in"; vert [exp body]]])
  | LetRetCont (lbl,ret, r, body) ->
    label verbose lbl (vert [horz [text "letRet"; horz [text ret; text "="]; vert [print_ret verbose r]];
          horz [text "in"; vert [exp body]]])
  | LetExnCont (lbl,exn, e, body) ->
    label verbose lbl (vert [horz [text "letExn"; horz [text exn; text "="; vert [print_exn verbose e]]];
          horz [text "in"; vert [exp body]]])
  | If (p,lbl, c, t, e) -> 
    label verbose lbl (vert [horz [text "if  "; vert [parens (horz [value c])]];
          horz [text "then"; braces (exp t)];
          horz [text "else"; (match e with
	  | If _ -> (exp e)
	  | _ -> braces (exp e))]])
  | AppFun (p,lbl, f, ret, exn, args) ->
    let rec pairOff l = match l with
      | [] -> []
      | [i] -> [i]
      | i::s::l -> squish[i;s] :: pairOff l in      
    label verbose lbl (squish [value f; 
                               parens (horzOrVert 
                                         [wrapBox [squish [text "Ret "; print_ret verbose ret; text ","];
                                                       squish [text "Exn "; print_exn verbose exn; text ";"]];
                                          wrapBox (pairOff (intersperse (text ",") (map value args)))])])
  | AppRetCont (lbl,r, x) ->
    label verbose lbl (horz [squish [print_ret verbose r; parens (horz [value x])]])
  | AppExnCont (lbl,e, x, l) ->
    label verbose lbl (horz [squish [print_exn verbose e; parens (horz [value x ; text ","; value l])]])
  | Eval (p,lbl, s) -> 
    label verbose lbl (squish [text "@eval"; parens (exp s)])


and attrsv verbose { proto = p; code = c; extensible = b; klass = k } =
  let value = value verbose in
  let proto = match p with None -> [] 
    | Some e -> [horz [text "#proto:"; value e]] in
  let code = match c with None -> [] 
    | Some e -> [horz [text "#code:"; value e]] in
  brackets (horzOrVert (map (fun x -> squish [x; (text ",")])
                          (proto@
                             code@
                             [horz [text "#class:"; text ("\"" ^ k ^ "\"")]; 
                              horz [text "#extensible:"; text (string_of_bool b)]])))
              
(* TODO: print and parse enum and config *)
and prop (f, prop) = match prop with
  | Data ({value=v; writable=w}, enum, config) ->
    horz [text ("'" ^ f ^ "'"); text ":"; 
          braces (horzOrVert [horz [text "#value"; squish [text v; text ","]]; 
                              horz [text "#writable"; squish [text (string_of_bool w); text ","]];
                              horz [text "#configurable"; text (string_of_bool config)]])]
  | Accessor ({getter=g; setter=s}, enum, config) ->
    horz [text ("'" ^ f ^ "'"); text ":"; braces (horz [text "#getter";
                                          squish [text g; text ","];
                                          text "#setter";
                                          text s])]
;;
Ljs_cps.pretty_print := (fun e fmt -> exp false e fmt)
let cps_value_to_string v = value false v Format.str_formatter; Format.flush_str_formatter(); 
