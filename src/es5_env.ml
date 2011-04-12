open Prelude
open Es5_syntax
open Lexing

type parsed_env = exp -> exp

let parse_env cin name : parsed_env =
  let lexbuf = Lexing.from_channel cin in
    try 
      (* Set the correct filename in lexbuf (for source-tracking). *)
      lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with pos_fname = name };
      Es5_parser.env Es5_lexer.token lexbuf
    with
      |  Failure "lexing: empty token" ->
           failwith (sprintf "lexical error at %s"
                       (string_of_position 
                          (lexbuf.lex_curr_p, lexbuf.lex_curr_p)))
      | Es5_parser.Error ->
           failwith (sprintf "unexpected token %s (at %s)"
                       (lexeme lexbuf)
                       (string_of_position 
                          (lexbuf.lex_curr_p, lexbuf.lex_curr_p)))

let rec enclose_in_env (env : parsed_env) (exp : exp) : exp =
  env exp
