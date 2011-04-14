(** Parses JSON ASTs produced by SpiderMonkey's API. *)
open Prelude
open Json_type
open Js_syntax

let parse_spidermonkey (cin : in_channel) (name : string) : Json_type.t = 
  let open Lexing in
  let lexbuf = from_channel cin in
  try 
    lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with pos_fname = name };
    Json_parser.main (Json_lexer.token (Json_lexer.make_param ())) lexbuf
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

let mk_pos (v : json_type) : pos = failwith "nyi"

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
  match typ  with
    | "Empty" -> Empty p
    | "Block" -> Block (p, map stmt (list (get "body" v)))
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
    | "Try" -> Try (p, map stmt (list (get "block" v)),
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

and expr (v : json_type) : expr = failwith "NYI"

and case (v : json_type) : case = failwith "NYI"

and catch (v : json_type) : catch = failwith "NYI"

and block (v : json_type) : block = failwith "NYI"
