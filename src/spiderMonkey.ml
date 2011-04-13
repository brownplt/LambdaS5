(** Parses JSON ASTs produced by SpiderMonkey's API. *)
open Prelude
open Json_type

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

