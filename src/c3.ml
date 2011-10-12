(** Parses JSON ASTs produced by C3's API. *)
open Prelude
open Json_type
open Js_syntax

let mk_pos (v : json_type) : Prelude.pos = 
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
  (json_pos_to_prelude_pos jstart, json_pos_to_prelude_pos jend)

let maybe (f : json_type -> 'a) (v : json_type) : 'a option =
  match Json_type.is_null v with
    | true -> None
    | false -> Some (f v)

let identifier (v : json_type) : id = match string (get "type" v) with
  | "SimpleName" -> string (get "name" v)
  | typ -> failwith (sprintf "expected Identifier, got %s as type" typ)

let literal (v : json_type) : lit = match string (get "type" v) with
  | "ConstantWrapper" -> begin match get "value" v with
      | Json_type.Null -> Js_syntax.Null
      | Json_type.Bool b -> Js_syntax.Bool b
      | Float f -> Num f
      | Int n -> Num (float_of_int n)
      | String s -> Str s
      | Json_type.Object [("re_lit", String re_val)] -> Regexp re_val
      | x -> failwith "unexpected literal"
  end
  | typ -> failwith (sprintf "expected Literal, got %s as type" typ)

let propName (v : json_type) : propName = match string (get "type" v) with
  | "ConstantWrapper" -> begin match literal v with
      | Num n -> PropNum n
      | Str s -> PropStr s
      | _ -> failwith (sprintf "illegal literal used as property name")
  end
  | typ -> failwith (sprintf "expected ConstantWrapper as prop-name, got %s" typ)


let rec stmt (v : json_type) : stmt = 
  let p = mk_pos (get "loc" v) in
  let label stmt typ = 
    match try_get "label" typ with
      None -> stmt
    | Some l -> Labeled (p, string l, stmt) in
  let typ = string (get "type" v) in
  let unlabeled = match typ with
    | "VariableDeclaration" -> Var (p, [ VarDecl (identifier (get "identifier" v), maybe expr (get "initializer" v)) ])
    | "Empty" -> Empty p
    | "Block" -> Block (p, block (get "statements" v))
    | "ExpressionStatement" -> Expr (p, expr (get "operand" v))
    | "If" ->
      If (p, expr (get "condition" v),
	  stmt (get "true_branch" v), 
	  maybe stmt (get "false_branch" v))
    | "Break" -> Break (p, maybe string (get "targetLabel" v))
    | "Continue" -> Continue (p, maybe string (get "targetLabel" v))
    | "With" -> With (p, expr (get "object" v), stmt (get "body" v))
    | "Switch" ->
      Switch (p, expr (get "discriminant" v), map case (list (get "cases" v)))
    | "Return" -> Return (p, maybe expr (get "operand" v))
    | "Throw" -> Throw (p, expr (get "operand" v))
    | "Try" -> 
	let catch = match (try_get "identifier" v, try_get "handler" v) with
	| (None, None) -> None
	| (Some i, Some h) -> Some (identifier i, block (get "statements" h))
	| (None, _) -> failwith "Missing handler but had identifier in try block"
	| (_, None) -> failwith "Missing identifier but had handler in try block" in
	Try (p, block (get "body" v), catch,
	     maybe block (get "finally_block" v))
    | "While" -> While (p, expr (get "condition" v), stmt (get "body" v))
    | "DoWhile" -> DoWhile (p, stmt (get "body" v), expr (get "condition" v))
    | "For" -> 
      let init = get "initializer" v in
      let test = maybe expr (get "condition" v) in
      let update = maybe expr (get "incrementer" v) in
      let body = stmt (get "body" v) in
      begin match init with
        | Json_type.Null -> For (p, None, test, update, body)
        | _ ->
          begin match string (get "type" init) with
	    | "VariableDeclaration" -> ForVar (p, [ varDecl init ], test, update, body)
            | _ -> For (p, Some (expr init), test, update, body)
          end
      end
    | "ForIn" -> 
	let leftExp = match get "initializer" v with Json_type.Null -> get "var" v | i -> i in
	let left = match get "initializer" v with 
	  Json_type.Null -> VarDecl (identifier (get "var" v), None)
	| i -> varDecl i in
	let right = expr (get "collection" v) in
	let body = stmt (get "body" v) in
	begin match string (get "type" leftExp) with
        | "VariableDeclaration" -> ForInVar (p, left, right, body)
        | _ -> ForIn (p, expr leftExp, right, body)
      end
    | "DebugBreak" -> Debugger p
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
    | _ -> failwith (sprintf "unexpected %s statement" typ) in
  label unlabeled v

and varDecl (v : json_type) : varDecl = 
    VarDecl (identifier (get "identifier" v), maybe expr (get "initializer" v))

and mem (v : json_type) : mem = 
  if (is_array v) 
  then match (list v) with
  | [name'; value'] ->
      let name = propName name' in
      let value = expr value' in
      begin match string (get "type" value') with
      | "FunctionExpression" -> let kind = string (get "kind" (get "meta" value')) in
	begin match kind with
	| "Function" -> Field (name, value)
	| "PropertyGetter" -> begin match value with
	  | Func (p, None, [], body) -> Get (name, body)
	  | _ -> failwith (sprintf "invalid body for getter")
	end
	| "PropertySetter" -> begin match value with
	  | Func (p, None, [x], body) -> Set (name, x, body)
	  | _ -> failwith (sprintf "invalid body for setter")
	end
	| kind -> failwith (sprintf "invalid kind of member: %s" kind)
	end
      | _ -> Field (name, value)
      end
  | _ -> failwith "Unknown format of member: it's a list with other than 2 elements"
  else 
    begin match string (get "type" v) with
    | "FunctionExpression" -> let kind = string (get "kind" (get "meta" v)) in
      begin match kind with
      | "Function" -> let name = PropStr (identifier (get "id" v)) in
	Field (name, expr v)
      | "PropertyGetter" -> begin match (expr v) with
	| Func (p, Some name, [], body) -> Get (PropStr name, body)
	| Func _ -> failwith "invalid body for getter -- it is a Func, though"
	| _ -> failwith (sprintf "invalid body for getter")
      end
      | "PropertySetter" -> begin match (expr v) with
	| Func (p, Some name, [x], body) -> Set (PropStr name, x, body)
	| _ -> failwith (sprintf "invalid body for setter")
      end
      | kind -> failwith (sprintf "invalid kind of member: %s" kind)
      end
    | _ -> failwith "Unknown format of member"
    end


and expr (v : json_type) : expr = 
  let p = mk_pos (get "loc" v) in
  let typ = string (get "type" v) in
  let mkInfix p op v = Infix (p, op, expr (get "operand1" v), expr (get "operand2" v)) in
  match typ with
    | "ConstantWrapper" -> Lit (p, literal v)
    | "RegExpLiteral" -> Lit (p, Regexp (string (get "source" v))) (* this is incomplete *)
    | "SimpleName" -> Id (p, string (get "name" v))
    | "ThisLiteral" -> This p
    | "ArrayLiteral" ->
      let f = function 
        | Json_type.Null -> Js_syntax.Id (p, "undefined")
        | e -> expr e in
      Array (p, map f (list (get "elements" v)))
    | "ObjectLiteral" -> Object (p, map mem (list (get "propertyList" v)))
    | "FunctionExpression" ->
      Func (p, maybe identifier (get "id" v), 
	    map string (list (get "formal_parameters" v)),
	    srcElts (get "statements" (get "body" v)))
    | "Sequence" -> List (p, map expr (list (get "expressions" v)))
    | "Delete" -> Prefix (p, "delete", expr (get "operand" v))
    | "Typeof" -> Prefix (p, "typeof", expr (get "operand" v))
    | "VoidOp" -> Prefix (p, "void", expr (get "operand" v))
    | "BitwiseBinary"
    | "NumericBinary"
    | "StrictEquality"
    | "Relational" -> 
	let op = match (string (get "operatorTok" v)) with
	| "BitwiseAnd" -> "&" 
	| "BitwiseOr" -> "|"
	| "BitwiseXor" -> "^"
	| "Divide" -> "/"
	| "GreaterThan" -> ">"
	| "GreaterThanEqual" -> ">="
	| "LeftShift" -> "<<"
	| "LessThan" -> "<"
	| "LessThanEqual" -> "<="
	| "Minus" -> "-"
	| "Modulo" -> "%"
	| "Multiply" -> "*"
	| "NotEqual" -> "!="
	| "RightShift" -> ">>"
	| "StrictEquals" -> "==="
	| "StrictNotEquals" -> "!=="
	| "UnsignedRightShift" -> ">>>"
	| _ -> failwith (sprintf "Unknown %s operator: %s" typ (string (get "operatorTok" v))) in 
	mkInfix p op v
    | "BitwiseBinaryAssign" 
    | "NumericBinaryAssign" ->
	let op = match (string (get "operatorTok" v)) with
	| "BitwiseAnd" -> "&="
	| "BitwiseOr" -> "|="
	| "BitwiseXor" -> "^="
	| "Divide" -> "/="
	| "LeftShift" -> "<<="
	| "Minus" -> "-="
	| "Modulo" -> "%="
	| "Multiply" -> "*="
	| "RightShift" -> ">>="
	| "UnsignedRightShift" -> ">>>="
	| _ -> failwith (sprintf "Unknown %s operator: %s" typ (Json_type.json_to_string v 3)) in 
	Assign (p, op, expr (get "operand1" v), expr (get "operand2" v))
    | "Plus" -> mkInfix p "+" v
    | "PlusAssign" -> 	Assign (p, "+=", expr (get "operand1" v), expr (get "operand2" v))
    | "Comma" -> mkInfix p "," v
    | "Instanceof" -> mkInfix p "instanceof" v
    | "Equality" -> mkInfix p "==" v
    | "Logical_and" -> mkInfix p "&&" v
    | "Logical_or" -> mkInfix p "||" v
    | "Assign" -> Assign (p, "=", expr (get "lhside" v), expr (get "rhside" v))
    | "NumericUnary" ->
	let mkPrefix p op v = Prefix (p, op, expr (get "operand" v)) in
	begin match (string (get "operatorTok" v)) with
	| "UnaryPlus" -> mkPrefix p "+" v
	| "UnaryMinus" -> mkPrefix p "-" v
	| "BitwiseNot" -> mkPrefix p "~" v
	| "LogicalNot" -> mkPrefix p "!" v
	| _ -> failwith (sprintf "Unknown NumericUnary operator: %s" (Json_type.json_to_string v 3))
	end
    | "PostOrPrefixOperator" ->
	let mkAssign p op v = UnaryAssign (p, op, expr (get "operand" v)) in
	begin match (string (get "operatorTok" v)) with
	| "PrefixIncrement" -> mkAssign p "prefix:++" v
	| "PrefixDecrement" -> mkAssign p "prefix:--" v
	| "PostfixIncrement" -> mkAssign p "postfix:++" v
	| "PostfixDecrement" -> mkAssign p "postfix:--" v
	| _ -> failwith (sprintf "Unknown PostOrPrefix operator: %s" (Json_type.json_to_string v 3))
	end
    | "Conditional" ->
      Cond (p, expr (get "condition" v), expr (get "operand1" v),
	    expr (get "operand1" v))
    | "Call" -> 
	if bool (get "isConstructor" v) 
	then New (p, expr (get "func" v), map expr (list (get "args" v)))
	else Call (p, expr (get "func" v), map expr (list (get "args" v)))
    | "Eval" -> Call (p, Lit(p, Str "eval"), [expr (get "operand" v)]) (* this is a hack *)
    | "ParenExpression" -> expr (get "wrapped" v)
    | "Indexer" -> Bracket (p, expr (get "obj" v), expr (get "index" v))
    | "QualifiedName" -> Dot (p, expr (get "rootObject" v), string (get "name" v))
    | typ -> failwith (sprintf "%s expressions are not in ES5" typ)

and case (v : json_type) : case =
  let p = mk_pos (get "loc" v) in
  let e = get "test" v in
  let stmts = Block (p, map stmt (list (get "consequent" v))) in
  match e with
    | Json_type.Null -> Default (p, stmts)
    | _ -> Case (p, expr e, stmts)

and block (v : json_type) : block = match is_array v with
  | true -> map stmt (list v)
  | false -> match string (get "type" v) with
      | "Block" -> map stmt (list (get "statements" v))
      | _ -> failwith "expected array of statements or a BlockStatement"

and srcElt (v : json_type) : srcElt = match string (get "type" v) with
  | "FunctionDeclaration" -> 
    FuncDecl (identifier (get "id" v),
	      map string (list (get "formal_parameters" v)),
	      srcElts (get "statements" (get "body" v)))
  | _ -> Stmt (stmt v) 

and srcElts (v : json_type) : srcElt list =
    map srcElt (list v)

let program (v : json_type) : srcElt list = 
  match string (get "type" v) with
    | "Block" -> map srcElt (Json_type.list (Json_type.get "statements" v))
    | typ -> failwith (sprintf "expected Program, got %s" typ)

let parse_c3 (cin : in_channel) (name : string) : Js_syntax.program = 
  let lexbuf = Lexing.from_channel cin in
  try 
    lexbuf.Lexing.lex_curr_p <- { lexbuf.Lexing.lex_curr_p with Lexing.pos_fname = name };
    program
      (Json_parser.main (Json_lexer.token (Json_lexer.make_param ())) lexbuf)
    with
      |  Failure "lexing: empty token" ->
           failwith (sprintf "lexical error at %s"
                       (string_of_position 
                          (lexbuf.Lexing.lex_curr_p, lexbuf.Lexing.lex_curr_p)))
      | Failure "utf8_of_point not implemented" ->
        failwith "Parser doesn't do some UTF8 encoding crap"
      | Parsing.Parse_error ->
           failwith (sprintf "parse error at %s; unexpected token %s"
                       (string_of_position 
                          (lexbuf.Lexing.lex_curr_p, lexbuf.Lexing.lex_curr_p))
                       (Lexing.lexeme lexbuf))

