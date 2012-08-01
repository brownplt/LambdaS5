(** Parses JSON ASTs produced by SpiderMonkey's API. *)
open Prelude
open Json_type
open Js_syntax
open Printf

let mk_pos (v : json_type) : Pos.t = 
  let jstart = get "start" v in
  let jend = get "end" v in
  let fname = match (get "source" v) with
  | Json_type.String s -> s
  | Json_type.Null -> "<unknown>" 
  | _ -> failwith "Expected JSON string or null in mk_pos" in
  let json_pos_to_prelude_pos pos = {
    Lexing.pos_fname = fname;
    Lexing.pos_lnum = int_of_float (float (get "line" pos));
    Lexing.pos_bol = int_of_float (float (get "column" pos));
    Lexing.pos_cnum = -1
  } in
  Pos.real (json_pos_to_prelude_pos jstart, json_pos_to_prelude_pos jend)


let pos_error expr msg = 
  failwith ((Pos.string_of_pos (mk_pos (get "loc" expr))) ^ ":\n" ^ msg)

let maybe (f : json_type -> 'a) (v : json_type) : 'a option =
  match Json_type.is_null v with
    | true -> None
    | false -> Some (f v)

let identifier (v : json_type) : id = match string (get "type" v) with
  | "Identifier" -> string (get "name" v)
  | typ -> failwith (sprintf "expected Identifier, got %s as type" typ)

let literal (v : json_type) : lit = match string (get "type" v) with
  | "Literal" -> begin match get "value" v with
      | Json_type.Null -> Js_syntax.Null
      | Json_type.Bool b -> Js_syntax.Bool b
      | Json_type.Float f -> Num f
      | Json_type.Int n -> Num (float_of_int n)
      | Json_type.String s -> Str s
      | Json_type.Object [("re_lit", String re_val)] -> Regexp re_val
      | Json_type.Array _ -> pos_error v "Bad/unexpected array literal"
      | Json_type.Object _ -> pos_error v "Bad/unexpected object literal"
  end
  | typ -> failwith (sprintf "expected Literal, got %s as type" typ)

let propName (v : json_type) : propName = match string (get "type" v) with
  | "Identifier" -> PropId (string (get "name" v))
  | "Literal" -> begin match literal v with
      | Num n -> PropNum n
      | Str s -> PropStr s
      | _ -> failwith (sprintf "illegal literal used as property name")
  end
  | typ -> 
    failwith (sprintf "expected Literal or Identifier as prop-name, got %s" typ)


let rec stmt (v : json_type) : stmt = 
  let p = mk_pos (get "loc" v) in
  let typ = 
    let x = string (get "type" v) in
    (* Verify that x is prefixed by Statement, then drop the prefix. *)
    if String.length x > 9 && (String.sub x (String.length x - 9) 9 = "Statement") then
      String.sub x 0 (String.length x - 9) 
    else
      x (* could be a VariableDeclaration *) in
  match typ with
    | "VariableDeclaration" -> begin match string (get "kind" v) with
	| "var" -> Var (p, map varDecl (list (get "declarations" v)))
	| kind -> failwith (sprintf "%s declarations are not valid ES5" kind)
    end
    | "Empty" -> Empty p
    | "Block" -> Block (p, block (get "body" v))
    | "Expression" -> Expr (p, expr (get "expression" v))
    | "If" ->
      If (p, expr (get "test" v),
	  stmt (get "consequent" v), 
	  maybe stmt (get "alternate" v))
    | "Labeled" -> Labeled (p, identifier (get "label" v), stmt (get "body" v))
    | "Break" -> Break (p, maybe identifier (get "label" v))
    | "Continue" -> Continue (p, maybe identifier (get "label" v))
    | "With" -> With (p, expr (get "object" v), stmt (get "body" v))
    | "Switch" ->
      Switch (p, expr (get "discriminant" v), map case (list (get "cases" v)))
    | "Return" -> Return (p, maybe expr (get "argument" v))
    | "Throw" -> Throw (p, expr (get "argument" v))
    | "Try" -> Try (p, block (get "block" v),
      (* NOTE(jpolitz): We simply take the first handler --- multiple 
         handlers are Spidermonkey-specific.  JS only specifies one
         or zero catch blocks. *)
      (match (list (get "handlers" v)) with
        | [] -> None
        | [handler] -> catch handler
        | _ -> pos_error v "More than one catch handler provided"),
      maybe block (get "finalizer" v))
    | "While" -> While (p, expr (get "test" v), stmt (get "body" v))
    | "DoWhile" -> DoWhile (p, stmt (get "body" v), expr (get "test" v))
    | "For" -> 
      let init = get "init" v in
      let test = maybe expr (get "test" v) in
      let update = maybe expr (get "update" v) in
      let body = stmt (get "body" v) in
      begin match init with
        | Json_type.Null -> For (p, None, test, update, body)
        | _ ->
          begin match string (get "type" init) with
	    | "VariableDeclaration" -> 
	      ForVar (p, map varDecl (list (get "declarations" init)), 
                      test, update, body)
            | _ -> For (p, Some (expr init), test, update, body)
          end
      end
    | "ForIn" -> 
      let left = get "left" v in
      let right = expr (get "right" v) in
      let body = stmt (get "body" v) in
      (* TODO: What is each? *)
      (* let each = bool (get "each" v) in *)
      begin match string (get "type" left) with
        | "VariableDeclaration" -> 
          ForInVar (p, List.nth (map varDecl (list (get "declarations" left))) 0, 
                    right, body)
        | _ -> ForIn (p, expr left, right, body)
      end
    | "Debugger" -> Debugger p
    | "FunctionDeclaration" ->
      (* 12: Statements
       * NOTE Several widely used implementations of ECMAScript are known to 
       * support the use of FunctionDeclaration as a Statement. However there 
       * are significant and irreconcilable variations among the implementations 
       * in the semantics applied to such FunctionDeclarations. Because of these 
       * irreconcilable differences, the use of a FunctionDeclaration as a 
       * Statement results in code that is not reliably portable among 
       * implementations. It is recommended that ECMAScript implementations 
       * either disallow this usage of FunctionDeclaration or issue a warning 
       * when such a usage is encountered. Future editions of ECMAScript may 
       * define alternative portable means for declaring functions in a Statement 
       * context.
       *)
      failwith "Function Delcarations not allowed as statements"
    | _ -> failwith (sprintf "unexpected %s statement" typ)

and varDecl (v : json_type) : varDecl = 
    VarDecl (identifier (get "id" v), maybe expr (get "init" v))

and mem (v : json_type) : mem = 
    let name = propName (get "key" v) in
    let value = expr (get "value" v) in
    match string (get "kind" v) with
      | "init" -> Field (name, value)
      | "get" -> begin match value with
	  | Func (p, None, [], body) -> Get (name, body)
	  | _ -> failwith (sprintf "invalid body for getter")
      end
      | "set" -> begin match value with
	  | Func (p, None, [x], body) -> Set (name, x, body)
	  | _ -> failwith (sprintf "invalid body for setter")
      end
      | kind -> failwith (sprintf "invalid kind of member: %s" kind)

and expr (v : json_type) : expr = 
  let p = mk_pos (get "loc" v) in
  let typ = 
    let x = string (get "type" v) in
    (* Verify that x is prefixed by Expression, then drop the prefix. *)
    if String.length x < 10 || (String.sub x (String.length x - 10) 10 <> "Expression") then
      x (* perhaps a Literal, which isn't suffixed with Expression. *)
    else 
      String.sub x 0 (String.length x - 10) in  
  match typ with
    | "Literal" -> Lit (p, literal v)
    | "Identifier" -> Id (p, string (get "name" v))
    | "This" -> This p
    | "Array" ->
      let f = function 
        | Json_type.Null -> Js_syntax.Id (p, "undefined")
        | e -> expr e in
      Array (p, map f (list (get "elements" v)))
    | ("Object" | "ObjectExpression") -> Object (p, map mem (list (get "properties" v)))
    | "Function" ->
      Func (p, maybe identifier (get "id" v), 
	    map identifier (list (get "params" v)),
	    (* Pull the body out of the BlockStatement *)
	    srcElts (get "body" (get "body" v)))
    | "Sequence" -> List (p, map expr (list (get "expressions" v)))
    | "Unary" -> 
      if bool (get "prefix" v) then
	Prefix (p, string (get "operator" v),
		expr (get "argument" v))
      else
	failwith "unexpected POSTFIX unary operator"
    | "Binary"
    | "Logical" ->
      Infix (p, string (get "operator" v),
	     expr (get "left" v), expr (get "right" v))
    | "Assignment" -> 
      Assign (p, string (get "operator" v),
	      expr (get "left" v), expr (get "right" v))
    (* "UpdateOperator" disagrees with docs---operator is just a string *)
    | "Update" ->
      let op = 
	(if bool (get "prefix" v) then "prefix:" else "postfix:") ^
	  string (get "operator" v) in
      UnaryAssign (p, op, expr (get "argument" v))
    | "Conditional" ->
      Cond (p, expr (get "test" v), expr (get "consequent" v),
	    expr (get "alternate" v))
    | "New" ->
      New (p, expr (get "callee" v),
	   let args = get "arguments" v in
	   if is_null args then []
	   else map expr (list args))
    | "Call" ->
      Call (p, expr (get "callee" v), map expr (list (get "arguments" v)))
    | ("Member" | "MemberExpression") -> 
      if bool (get "computed" v) then
	Bracket (p, expr (get "object" v), expr (get "property" v))
      else
	Dot (p, expr (get "object" v), identifier (get "property" v))
    | typ -> failwith (sprintf "%s expressions are not in ES5" typ)

and case (v : json_type) : case =
  let p = mk_pos (get "loc" v) in
  let e = get "test" v in
  let stmts = Block (p, map stmt (list (get "consequent" v))) in
  match e with
    | Json_type.Null -> Default (p, stmts)
    | _ -> Case (p, expr e, stmts)

and catch (v : json_type) : catch = 
    if is_array v then failwith "Multiple catches are spidermonky-only"
    else
      if is_null v then None
      else
        let param = match (get "type" (get "param" v)) with
	  String s -> begin match s with
          | "Identifier" -> string (get "name" (get "param" v))
          | param -> (printf "param was %s" param; param)
	  end
        | _ -> failwith "Param wasn't a string" in
        let body = block (get "body" v) in Some (param, body)

and block (v : json_type) : block = match is_array v with
  | true -> map stmt (list v)
  | false -> match string (get "type" v) with
      | "BlockStatement" -> map stmt (list (get "body" v))
      | _ -> failwith "expected array of statements or a BlockStatement"

and srcElt (v : json_type) : srcElt = match string (get "type" v) with
  | "FunctionDeclaration" -> 
    FuncDecl (identifier (get "id" v),
	      map identifier (list (get "params" v)),
	      srcElts (get "body" (get "body" v)))
  | _ -> Stmt (stmt v) 

and srcElts (v : json_type) : srcElt list =
    map srcElt (list v)

let program (v : json_type) : srcElt list = 
  match Json_type.string (Json_type.get "type" v) with
    | "Program" -> map srcElt (Json_type.list (Json_type.get "body" v))
    | typ -> failwith (sprintf "expected Program, got %s" typ)

let parse_spidermonkey (cin : in_channel) (name : string) : Js_syntax.program = 
  let lexbuf = Lexing.from_channel cin in
  try 
    lexbuf.Lexing.lex_curr_p <- { lexbuf.Lexing.lex_curr_p with Lexing.pos_fname = name };
    program
      (Json_parser.main (Json_lexer.token (Json_lexer.make_param ())) lexbuf)
    with
      |  Failure "lexing: empty token" ->
          raise (Failure (sprintf "lexical error at %s"
                       (Pos.string_of_pos (Pos.real
                          (lexbuf.Lexing.lex_curr_p, lexbuf.Lexing.lex_curr_p)))))
      | Failure "utf8_of_point not implemented" ->
          raise (Failure "Parser doesn't do some UTF8 encoding crap")
      | Parsing.Parse_error ->
          raise (Failure (sprintf "parse error at %s; unexpected token %s"
                      (Pos.string_of_pos (Pos.real
                         (lexbuf.Lexing.lex_curr_p, lexbuf.Lexing.lex_curr_p)))
                      (Lexing.lexeme lexbuf)))
      | _ -> raise (Failure "Unexpected error in parse_spidermonkey")

