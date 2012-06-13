{
  open Prelude
  open Lexing
  open Regexp_parser
  open Regexp_syntax

}

(* dec_digit+ corresponds to DecimalDigits in the spec. *)
let dec_digit = ['0'-'9']

let dec_int_lit = '0' | (['1'-'9'] dec_digit*)

let hex = ['0'-'9' 'A'-'F' 'a'-'f']

let hex_lit = "x" hex hex

let unicode_lit = "u" hex hex hex hex

let ident = ['a'-'z' 'A'-'Z' '$' '_' '%']['%']?['a'-'z' 'A'-'Z' '0'-'9' '$' '_' '-']*

(* http://es5.github.com/#x15.10 *)
let pattern_character = [^ '\\' '$' '.' '*' '+' '?' '(' ')' '[' ']' '{' '}' '|']
let control_escape = '\\'['f' 'n' 'r' 't' 'v']
let control_letter = '\\''c'['a'-'z' 'A'-'Z']

(* NOTE(joe): This is incompletely implemented.  These are characters
that can be escaped to represent themselves.  In the spec, this is
defined as SourceCharacter (any unicode character) *but not* an
IdentifierPart, which contains interesting sets like alphanumerics, _, $,
and others.  Since ocamllex doesn't have support for unicode, I'm punting
on this right now.  Ulex (available at
http://www.cduce.org/download.html) is the right choice, but we should
move all our parsers to Ulex at once when we decide it's a deal breaker,
since eval and other pieces of the toolchain also have unicode issues. *)

let identity_lit = '\\'[^ 'a'-'z' 'A'-'Z' '0'-'9' '$' '_' '-']

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
  | "." { DOT }
  | "*" { TIMES }
  | "+" { PLUS }
  | "?" { QUESTION }
  | "!" { BANG }
  | "{" { LBRACE }
  | "}" { RBRACE }
  | "[" { LBRACK }
  | "]" { RBRACK }
  | "\\b" { BACKLITTLEB }
  | "\\B" { BACKBIGB }
  | control_escape as x { CONTROLESCAPE x }
  | control_letter as x { CONTROLLETTER x }
  | pattern_character as x { PATTERNC (Char.escaped x) }
  | dec_int_lit as x { INT (int_of_string x) }
  | hex_lit as x { HEX x }
  | unicode_lit as x { UNICODE x }
  | identity_lit as x { IDENTITY x }

  | eof { EOF }
