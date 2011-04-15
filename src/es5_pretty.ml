open Prelude
open Es5_syntax

open Format
open FormatExt

let rec exp e = match e with
  | Null _ -> text "null"
  | Undefined _ -> text "undefined"
  | Num (_,n) -> text (string_of_float n)
  | String (_,s) -> text s
  | True _ -> text "true"
  | False _-> text "false"
  | Id (p, x) -> text x
  | Object (p, avs, props) ->
      parens (vert [text "object";
                    attrsv avs;
		    vert (map prop props)])
  | SetField (p, o, f, v, args) ->
      parens (horz 
		 [text "update-field";
		 exp o;
		 exp f;
		 exp v])
  | GetField (p, o, f, args) ->
      parens (horz 
		 [text "get-field";
		 exp o;
		 exp f;])
  | DeleteField (p, o1, f) ->
      parens (horz
		 [text "delete-field";
		 exp o1;
		 exp f])
  | GetAttr (p, a, o, f) ->
      parens (horz
		[text "attr-get";
		 text (string_of_attr a);
		 exp o;
		 exp f])
  | SetAttr (p, a, o, f, v) ->
      parens (horz 
		[text "attr-set";
		 text (string_of_attr a);
		 exp o;
		 exp f;
		 exp v])
  | SetBang (p, x, e) ->
      parens (horz
		[text "set!";
		 text x;
		 exp e])
  | Op1 (p, op, e) -> 
    parens (horz [text op; exp e])
  | Op2 (p, op, e1, e2) ->
    parens (horz [text op; exp e1; exp e2])
  | If (p, c, t, e) -> 
      parens (vert [horz [text "if"; exp c];
		    exp t;
		    exp e;])
  | App (p, f, args) ->
      parens (horz (exp f :: map exp args))
  | Seq (p, e1, e2) ->
      parens (vert [text "begin"; exp e1; exp e2])
  | Let (p, x, e, body) ->
      parens (vert [horz [text "let"; parens (horz [text x; exp e])];
		    exp body])
  | Rec (p, x, e, body) -> 
      parens (vert [horz [text "letrec"; parens (horz [text x; exp e])];
		    exp body])
  | Label (p, l, e) ->
      parens (vert [text "label"; text l; exp e])
  | Break (p, l, e) ->
      parens (horz [text "break"; text l; exp e])
  | TryCatch (p, body, catch) ->
      parens (vert [text "try-catch"; exp body; exp catch])
  | TryFinally (p, body, fin) ->
      parens (vert [text "try-finally"; exp body; exp fin])
  | Throw (p, e) ->
      parens (horz [text "throw"; exp e])
  | Lambda (p, xs, e) ->
      parens (vert [horz [text "lambda";
			  parens (horz (map text xs))];
		    exp e])

and attrsv { proto = p; code = c; extensible = b; klass = k } =
  let proto = match p with None -> [] 
    | Some e -> [horz [text "#proto:"; exp e]] in
  let code = match c with None -> [] 
    | Some e -> [horz [text "#code:"; exp e]] in
  brackets (vert (proto@
                    code@
                    [horz [text "#class:"; text k]; 
                     horz [text "#extensible"; text (string_of_bool b)]]))
              
(* TODO: print and parse enum and config *)
and prop (f, prop) = match prop with
  | Data ({value=v; writable=w}, enum, config) ->
    horz [text f; text ":"; brackets (horz [text "#value:"; 
                                            exp v; text ","; 
                                            text "#writable:";  
                                            text (string_of_bool w)])]
  | Accessor ({getter=g; setter=s}, enum, config) ->
    horz [text f; text ":"; brackets (horz [text "#getter:";
                                            exp g; text ",";
                                            text "#setter:";
                                            exp s])]
  | _ -> failwith "generic printing nyi"

