{
open Prelude
open Lexing
open Es5_syntax
open Es5_parser

module S = String

(* Requires: start < String.length str *)
let rec drop_spaces (str : string) (start : int) = 
  match String.get str start with
    ' '  -> drop_spaces str (start + 1)
  | '\t' -> drop_spaces str (start + 1)
  | '\r' -> drop_spaces str (start + 1)
  | '\n' -> drop_spaces str (start + 1)
  |  _   -> String.sub str start (String.length str - start)

(* TODO: if integer conversions overflow, treat as a float *)
let parse_num_lit (s : string) : token =
  if S.contains s 'x' || S.contains s 'X'
    then INT (int_of_string s)
    else if S.contains s '.'
           then NUM (float_of_string s)
           else if S.contains s 'e' || S.contains s 'E'
                  then NUM (float_of_string s)
                  else INT (int_of_string s)
}

(* dec_digit+ corresponds to DecimalDigits in the spec. *)
let dec_digit = ['0'-'9']

let signed_int = dec_digit+ | ('+' dec_digit+) | ('-' dec_digit+)

let expt_part = ['e' 'E'] signed_int

let dec_int_lit = '0' | (['1'-'9'] dec_digit*)

let hex = ['0'-'9' 'A'-'f' 'a'-'f']

let hex_lit = ("0x" | "0X") hex+

let dec_lit = 
  (dec_int_lit '.' dec_digit* expt_part?) | 
  ('.' dec_digit+ expt_part?) |
  (dec_int_lit expt_part?)

let num_lit = dec_lit | hex_lit

let ident = ['a'-'z' 'A'-'Z' '$' '_']['a'-'z' 'A'-'Z' '0'-'9' '$' '_' '-']*

let digit = ['0'-'9']

let char = [^ '"' '\\']

let blank = [ ' ' '\t' ]

let escape_sequence
  = [^ '\r' '\n'] | ('x' hex hex) | ('u' hex hex hex hex)

let double_quoted_string_char = 
  [^ '\r' '\n' '"' '\\'] | ('\\' escape_sequence)

let single_quoted_string_char =
  [^ '\r' '\n' '\'' '\\'] | ('\\' escape_sequence)

rule token = parse
   | blank + { token lexbuf }
   | '\n' { new_line lexbuf; token lexbuf }
   | "/*" {  block_comment lexbuf }
   | "//"[^ '\r' '\n']* [ '\r' '\n' ] { new_line lexbuf; token lexbuf }


   | '"' (double_quoted_string_char* as x) '"' { STRING x }
   | ''' (single_quoted_string_char* as x) ''' { STRING x }
  
   | num_lit as x { parse_num_lit x }
   | "NaN" { NUM nan }
   | "+inf" { NUM infinity }
   | "-inf" { NUM infinity }
   | "{" { LBRACE }
   | "}" { RBRACE }
   | '(' { LPAREN }
   | ')' { RPAREN }
   | "undefined" { UNDEFINED }
   | "null" { NULL }
   | "func" { FUNC }
   | "let" { LET }
   | "fix" { FIX }
   | "delete" { DELETE }
   | "[" { LBRACK }
   | "]" { RBRACK }
   | "<" { LT }
   | ">" { GT }
   | "=" { EQUALS }
   | "," { COMMA }
   | "!" { DEREF }
   | "ref" { REF }
   | ":" { COLON }
   | ":=" { COLONEQ }
   | "prim" { PRIM }
   | "if" { IF }
   | "else" { ELSE }
   | ";" { SEMI }
   | "label" { LABEL }
   | "break" { BREAK }
   | "try" { TRY }
   | "catch" { CATCH }
   | "finally" { FINALLY }
   | "throw" { THROW }
   | "[[" { LLBRACK }
   | "]]" { RRBRACK }
   | "===" { EQEQEQUALS }
   | "!==" { BANGEQEQUALS }
   | "typeof" { TYPEOF }
   | "true" { BOOL true }
   | "false" { BOOL false }
   | "&&" { AMPAMP }
   | "||" { PIPEPIPE }
   | "return" { RETURN }
   | "function" { FUNCTION }
   | "#configurable" { CONFIG }
   | "#setter" { SETTER }
   | "#getter" { GETTER }
   | "#writable" { WRITABLE }
   | "#value" { VALUE }
   | "#enumerable" { ENUM }

   | ident as x { ID x }
 
   | eof { EOF }

and block_comment = parse
    "*/" { token lexbuf }
  | '*' { block_comment lexbuf }
  | [ '\n' '\r' ]  {  block_comment lexbuf }
  | [^ '\n' '\r' '*']+ { block_comment lexbuf }
