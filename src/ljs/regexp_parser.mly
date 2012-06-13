%{
open Prelude
open Regexp_syntax
%}

%token <float> NUM
%token <int> INT

%token PIPE DASH BACKSLASH LPAREN RPAREN COLON DOLLAR CARET EQUALS
  TIMES PLUS QUESTION LBRACE RBRACE LBRACK RBRACK HEX BANG
  LITTLEB BIGB

%token EOF

%type <Regexp_syntax.pattern> pattern

%start pattern

%%

pattern :
  | disjunction { $1 }

disjunction :
  | alternative { [$1] }
  | alternative PIPE disjunction { $1 :: $3 }

/* TODO(joe): this can be empty? */
alternative :
  | term { [$1] }
  | alternative term { $1@[$2] }

term :
  | assertion { AssertionTerm ($1) }
/*  | atom { Atom ($1, None) } */
/*  | atom quantifier { Atom ($1, Some $2) } */

assertion :
  | CARET { Beginning }
  | DOLLAR { End }
  | BACKSLASH LITTLEB { Word }
  | BACKSLASH "B" { NotWord }
  | LPAREN QUESTION EQUALS disjunction RPAREN { QuestionEquals ($4) }
  | LPAREN QUESTION BANG disjunction RPAREN { QuestionBang ($4) }
