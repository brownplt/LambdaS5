open Prelude
open Lexing

(* parse a string to produce ljs *)
let parse str =
  let lexbuf = Lexing.from_string str in
  try
    lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with pos_fname = "stdin" };
    Ljs_parser.prog Ljs_lexer.token lexbuf
  with
  |  Failure "lexing: empty token" ->
      failwith (sprintf "lexical error at %s"
                        (Pos.string_of_pos (Pos.real
                                              (lexbuf.lex_curr_p, lexbuf.lex_curr_p))))
  | Failure "utf8_of_point not implemented" ->
     failwith "Parser doesn't do some UTF8 encoding crap"
  | _ ->
     failwith (sprintf "parse error at %s; unexpected token %s in '%s'"
                       (Pos.string_of_pos (Pos.real
                                             (lexbuf.lex_curr_p, lexbuf.lex_curr_p)))
                       (lexeme lexbuf)
                       str)
              

let succeed = begin
    Printf.printf "passed\n"; true
  end

let fail msg = begin
    Printf.printf "failed %s\n" msg; false
  end
