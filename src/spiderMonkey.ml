(** Parses JSON ASTs produced by SpiderMonkey's API. *)
open Prelude
open Json_type
open Js_syntax

let mk_pos (v : json_type) : pos = Prelude.dummy_pos (* TODO *)

let identifier (v : json_type) : id = match string (get "type" v) with
  | "identifier" -> string (get "name" v)
  | typ -> failwith (sprintf "expected identifier, got %s" typ)

let maybe (f : json_type -> 'a) (v : json_type) : 'a option =
  match Json_type.is_null v with
    | true -> None
    | false -> Some (f v)

let rec stmt (v : json_type) : stmt = 
  let p = mk_pos (get "loc" v) in
  let typ = 
    let x = string (get "type" v) in
    (* Verify that x is prefixed by Statement, then drop the prefix. *)
    let open String in
    if length x < 9 || (sub x (length x - 9) 9 != "Statement") then
      failwith (sprintf "expected statement, got %s" x)
    else 
      sub x 0 (length x - 9) in  
  match typ with
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
    | "For" -> failwith "NYI"
(*      let init = get "init" v in
      begin match string (get "type" init) with
	| "VariableDeclaration" -> 
	  ForInVar (p, varDecls init, *)
    | "ForIn" -> failwith "NYI"
    | "Debugger" -> Debugger p
    | _ -> failwith (sprintf "unexpected %s statement" typ)

and expr (v : json_type) : expr = 
  let p = mk_pos (get "loc" v) in
  let typ = 
    let x = string (get "type" v) in
    (* Verify that x is prefixed by Expression, then drop the prefix. *)
    let open String in
    if length x < 10 || (sub x (length x - 10) 10 != "Expression") then
      failwith (sprintf "expected expression, got %s" x)
    else 
      sub x 0 (length x - 10) in  
  match typ with
    | "This" -> This p
    | "Array" -> Array (p, map expr (list (get "elements" v)))
    | _ -> This p (* TODO *)


and case (v : json_type) : case = failwith "NYI"

and catch (v : json_type) : catch = failwith "NYI"

and block (v : json_type) : block = match is_array v with
  | true -> map stmt (list v)
  | false -> match string (get "type" v) with
      | "BlockStatement" -> map stmt (list (get "body" v))
      | _ -> failwith "expected array of statements or a BlockStatement"

and srcElt (v : json_type) : srcElt = Stmt (stmt v) (* TODO *)

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

