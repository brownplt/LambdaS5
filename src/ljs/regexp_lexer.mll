{
  open Prelude
  open Lexing
  open Regexp_parser
  open Regexp_syntax


module S = String

let comment_start_p = ref dummy_pos

let block_comment_buf = Buffer.create 120

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
  (signed_int '.' dec_digit* expt_part?) | 
  ('.' dec_digit+ expt_part?) |
  (dec_int_lit expt_part?)

let num_lit = dec_lit | hex_lit

let ident = ['a'-'z' 'A'-'Z' '$' '_' '%']['%']?['a'-'z' 'A'-'Z' '0'-'9' '$' '_' '-']*

let digit = ['0'-'9']

rule token = parse
  | "|" { PIPE }
  | "-" { DASH }
  | "\\" { BACKSLASH }
  | "(" { LPAREN }
  | ")" { RPAREN }
  | ":" { COLON }
  | "$" { DOLLAR }
  | "^" { CARET }
  | "=" { EQUALS }
  | "*" { TIMES }
  | "+" { PLUS }
  | "?" { QUESTION }
  | "!" { BANG }
  | "{" { LBRACE }
  | "}" { RBRACE }
  | "[" { LBRACK }
  | "]" { RBRACK }
  | "b" { LITTLEB }
  | "B" { BIGB }
  | num_lit as x { parse_num_lit x }
  | hex_lit { HEX }

  | eof { EOF }
