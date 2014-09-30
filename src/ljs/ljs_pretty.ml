open Prelude
open Ljs_syntax

open Format
open FormatExt

let rec vert_intersperse a lst = match lst with
  | [] -> []
  | [x] -> [x]
  | x :: xs -> squish [x; a] :: (vert_intersperse a xs)

(* Takes a function exprec to use for all recursive calls. This allows us to create the
 * standard recursive printer, defined below as exp, but also to override the printer for
 * certain cases, like so:
 * let rec myexp e = match e with
 * | Num _ -> text (string_of_int 42)
 * | If (_, c, t, _) -> horz [text "if"; myexp c; text "then"; myexp t]
 * | _ -> exp_helper myexp e
 * For a real example, check out ljs_sym_trace.ml.
 *)
let rec exp_helper exprec e = match e with
  | Null _ -> text "null"
  | Undefined _ -> text "undefined"
  | Num (_,n) -> text (string_of_float n)
  | String (_,s) -> text ("\"" ^ (String.escaped s) ^ "\"")
  | True _ -> text "true"
  | False _-> text "false"
  | Id (p, x) -> text x
  | Object (p, avs, props) -> begin
    match props with
    | [] -> braces (attrsv exprec avs)
    | _ -> braces (vert [attrsv exprec avs; vert (vert_intersperse (text ",") (map (prop exprec) props))])
  end
  | SetField (p, o, f, v, args) ->
    squish [exprec o; brackets (horzOrVert [horz [exprec f; text "="; exprec v; text ","]; exprec args])]
  | GetField (p, o, f, args) ->
    squish [exprec o; brackets (horz [exprec f; text ","; exprec args])]
  | DeleteField (p, o, f) ->
    squish [exprec o; brackets (horz [text "delete"; exprec f])]
  | GetAttr (p, a, o, f) ->
    squish [exprec o;
            brackets (horz [exprec f; angles (horz [text (string_of_attr a)])])]
  | SetAttr (p, a, o, f, v) ->
    squish [exprec o;
            brackets (squish [exprec f; angles (horz [text (string_of_attr a)]);
                              text "="; exprec v])]
  | GetObjAttr (p, a, o) ->
    squish [exprec o;
            brackets (angles (horz [text (string_of_oattr a)]))]
  | SetObjAttr (p, a, o, v) ->
    squish [exprec o;
            brackets (squish [angles (horz [text (string_of_oattr a)]);
                              text "="; exprec v])]
  | OwnFieldNames (p, o) ->
    squish [text "get-own-field-names"; parens (exprec o)]
  | SetBang (p, x, e) ->
    horz [text x; text ":="; exprec e]
  | Op1 (p, op, e) -> 
    squish [text "prim"; parens (horz [text ("\"" ^ op ^ "\","); exprec e])]
  | Op2 (p, op, e1, e2) ->
    squish [text "prim"; parens (horz [text ("\"" ^ op ^ "\","); exprec e1; text ","; exprec e2])]
  | If (p, c, t, e) -> 
    horz [text "if"; vert [parens (horz [exprec c]);
                           braces (exprec t);
                           text "else";
			   (match e with
			   | If _ -> (exprec e)
			   | _ -> braces (exprec e))]]
  | App (p, f, args) ->
    squish [exprec f; parens (vert (vert_intersperse (text ",") (map exprec args)))]
  | Seq (p, e1, e2) ->
    vert [squish [exprec e1; text ";"]; exprec e2]
  | Let (p, x, e, body) ->
    braces (horz [text "let"; vert [parens (horz [text x; text "="; exprec e]);
                                    opt_braces exprec body]])
  | Rec (p, x, e, body) -> 
    horz [text "rec"; vert [parens (horz [text x; text "="; exprec e]);
                            opt_braces exprec body]]
  | Label (p, l, e) ->
    vert [horz [text "label"; text l; text ":"]; braces (exprec e)]
  | Break (p, l, e) ->
    horz [text "break"; text l; exprec e]
  | TryCatch (p, body, catch) ->
    vert [text "try"; braces (exprec body); text "catch"; braces (exprec catch)]
  | TryFinally (p, body, fin) ->
    vert [text "try"; braces (exprec body); text "finally"; braces (exprec fin)]
  | Throw (p, e) ->
    horz [text "throw"; exprec e]
  | Lambda (p, xs, e) ->
    vert [squish [text "func"; parens (horz (intersperse (text ",") (map text xs)))];
          braces (exprec e)]
  | Hint (p, hint, e) ->
      parens (vert [squish [text "/*: "; text hint; text "*/"];
	                 exprec e])

and opt_braces exprec expr = match expr with
  | Seq _ -> braces (exprec expr)
  | _ -> exprec expr

and attrsv exprec { proto = p; code = c; extensible = b; klass = k } =
  let proto = match p with None -> [] 
    | Some e -> [horz [text "#proto:"; exprec e]] in
  let code = match c with None -> [] 
    | Some e -> [horz [text "#code:"; exprec e]] in
  brackets (horzOrVert (map (fun x -> squish [x; (text ",")])
                          (proto@
                             code@
                             [horz [text "#class:"; text ("\"" ^ k ^ "\"")]; 
                              horz [text "#extensible:"; text (string_of_bool b)]])))
              
(* TODO: print and parse enum and config *)
and prop exprec (f, prop) = match prop with
  | Data ({value=v; writable=w}, enum, config) ->
    horz [text ("'" ^ f ^ "'"); text ":"; 
          braces (horzOrVert [horz [text "#value"; parens (exprec v); text ","]; 
                              horz [text "#writable"; text (string_of_bool w); text ","];
                              horz [text "#configurable"; text (string_of_bool config)]])]
  | Accessor ({getter=g; setter=s}, enum, config) ->
    horz [text ("'" ^ f ^ "'"); text ":"; braces (vert [horz [text "#getter";
                                          exprec g; text ","];
                                          horz[text "#setter";
                                               exprec s]])]

let rec exp e = exp_helper exp e


(* Remove duplicate leading chains (like the environment) from a trace *)
let remove_prefix_dups exprs =
  match exprs with
  | [] -> []
  | v::rest ->
    v::(snd
      (List.fold_left (fun (first, trace) expr ->
        match first with
        | Some expr' ->
            let nm e = Pos.fname (pos_of e) in
            if nm expr = nm expr' then (first, trace) else (None, trace@[expr])
        | None -> (None, trace@[expr])
      ) (Some v, []) rest))

let filter_dummies exprs =
  List.filter (fun expr -> not (Pos.isSynthetic (pos_of expr))) exprs

let stack_trace exprs =
  let filtered = remove_prefix_dups (filter_dummies exprs) in
    vert (map (fun expr -> text (Pos.string_of_pos (pos_of expr))) filtered)

let string_stack_trace =
  FormatExt.to_string stack_trace

