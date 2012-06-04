open Prelude
open Ljs_syntax
open Lexing

let parse_es5 cin name =
  let lexbuf = Lexing.from_channel cin in
    try 
      (* Set the correct filename in lexbuf (for source-tracking). *)
      lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with pos_fname = name };
      Ljs_parser.prog Ljs_lexer.token lexbuf
    with
      |  Failure "lexing: empty token" ->
           failwith (sprintf "lexical error at %s"
                       (Pos.string_of_pos (Pos.real
                          (lexbuf.lex_curr_p, lexbuf.lex_curr_p))))
      | Failure "utf8_of_point not implemented" ->
        failwith "Parser doesn't do some UTF8 encoding crap"
      | _ ->
           failwith (sprintf "parse error at %s; unexpected token %s"
                       (Pos.string_of_pos (Pos.real
                          (lexbuf.lex_curr_p, lexbuf.lex_curr_p)))
                       (lexeme lexbuf))

let parse_es5_env cin name =
  let lexbuf = Lexing.from_channel cin in
    try 
      (* Set the correct filename in lexbuf (for source-tracking). *)
      lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with pos_fname = name };
      Ljs_parser.env Ljs_lexer.token lexbuf
    with
      |  Failure "lexing: empty token" ->
           failwith (sprintf "lexical error at %s"
                       (Pos.string_of_pos (Pos.real
                          (lexbuf.lex_curr_p, lexbuf.lex_curr_p))))
      | Parsing.Parse_error ->
           failwith (sprintf "parse error at %s; unexpected token %s"
                       (Pos.string_of_pos (Pos.real
                          (lexbuf.lex_curr_p, lexbuf.lex_curr_p)))
                       (lexeme lexbuf))
