(** Parses JSON ASTs produced by SpiderMonkey's API. *)
open Prelude
open Json_type
open Js_syntax

let mk_pos (v : json_type) : pos = Prelude.dummy_pos (* TODO *)

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
      | Float f -> Num f
      | Int n -> Num (float_of_int n)
      | String s -> Str s
      | _ -> failwith "unexpected literal (RegExp?)"
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
    let open String in
    if length x > 9 && (sub x (length x - 9) 9 = "Statement") then
      sub x 0 (length x - 9) 
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
    | "Break" -> Break (p, maybe identifier (get "identifier" v))
    | "Continue" -> Continue (p, maybe identifier (get "identifier" v))
    | "With" -> With (p, expr (get "object" v), stmt (get "body" v))
    | "Switch" ->
      Switch (p, expr (get "test" v), map case (list (get "cases" v)))
    | "Return" -> Return (p, maybe expr (get "argument" v))
    | "Throw" -> Throw (p, expr (get "argument" v))
    | "Try" -> Try (p, block (get "block" v),
		    catch (get "handler" v),
		    maybe block (get "block" v))
    | "While" -> While (p, expr (get "test" v), stmt (get "body" v))
    | "DoWhile" -> DoWhile (p, stmt (get "body" v), expr (get "test" v))
    | "For" -> 
      let init = get "init" v
      and test = get "test" v
      and update = get "update" v
      and body = get "body" v in
      let init_typ = get "type" init in
      let result = match (string init_typ) with
        | "VariableDeclaration" -> failwith "ForVar NYI"
        | _ -> let i = Some (expr init)
          and t = Some (expr test)
          and u = Some (expr update) in
          For (p, i, t, u, stmt body) in
      result
    | "ForIn" -> failwith "NYI"
    | "Debugger" -> Debugger p
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
    let open String in
    if length x < 10 || (sub x (length x - 10) 10 <> "Expression") then
      x (* perhaps a Literal, which isn't suffixed with Expression. *)
    else 
      sub x 0 (length x - 10) in  
  match typ with
    | "Literal" -> Lit (p, literal v)
    | "Identifier" -> Id (p, string (get "name" v))
    | "This" -> This p
    | "Array" -> Array (p, map expr (list (get "elements" v)))
    | ("Object" | "ObjectExpression") -> Object (p, map mem (list (get "properties" v)))
    | "Function" ->
      Func (p, maybe identifier (get "id" v), 
	    map identifier (list (get "params" v)),
	    (* Pull the body out of the BlockStatement *)
	    srcElts (get "body" (get "body" v)))
    | "Sequence" -> List (p, map expr (list (get "expressions" v)))
    | "Unary" -> 
      if bool (get "prefix" v) then
	Prefix (p, string (get "token" (get "operator" v)),
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
    | "Update" ->
      let op = 
	(if bool (get "prefix" v) then "prefix:" else "postfix:") ^
	  string (get "token" (get "operator" v)) in
      UnaryAssign (p, op, expr (get "argument" v))
    | "Conditional" ->
      Cond (p, expr (get "test" v), expr (get "consequent" v),
	    expr (get "alternate" v))
    | "New" ->
      New (p, expr (get "constructor" v),
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

and case (v : json_type) : case = failwith "case NYI"

and catch (v : json_type) : catch = failwith "catch NYI"

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
  let open Json_type in
  match string (get "type" v) with
    | "Program" -> map srcElt (list (get "body" v))
    | typ -> failwith (sprintf "expected Program, got %s" typ)

let parse_spidermonkey (cin : in_channel) (name : string) : Js_syntax.program = 
  let open Lexing in
  let lexbuf = from_channel cin in
  try 
    lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with pos_fname = name };
    program
      (Json_parser.main (Json_lexer.token (Json_lexer.make_param ())) lexbuf)
    with
      |  Failure "lexing: empty token" ->
           failwith (sprintf "lexical error at %s"
                       (string_of_position 
                          (lexbuf.lex_curr_p, lexbuf.lex_curr_p)))
      | Json_parser.Error ->
           failwith (sprintf "parse error at %s; unexpected token %s"
                       (string_of_position 
                          (lexbuf.lex_curr_p, lexbuf.lex_curr_p))
                       (lexeme lexbuf))

