%{
open Prelude
open Regexp_syntax
%}

%token <float> NUM
%token <int> INT
%token <string> PATTERNC HEX CONTROLLETTER CONTROLESCAPE UNICODE IDENTITY

%token PIPE DASH BACKSLASH LPAREN RPAREN COLON DOLLAR CARET EQUALS
  TIMES PLUS QUESTION LBRACE RBRACE LBRACK RBRACK BANG
  BACKLITTLEB BACKBIGB DOT

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
  | term alternative { $1 :: $2 }

term :
  | assertion { Assertion ($1) }
  | atom { Atom ($1, None) }
/*  | atom quantifier { Atom ($1, Some $2) } */

atom :
  | PATTERNC { PatternCharacter ($1) }
  | DOT { Dot }
  | BACKSLASH INT { EscapedAtom (DecimalEscape $2)}
  | BACKSLASH HEX { EscapedAtom (CharacterEscape (HexEscape $2)) }
  | BACKSLASH UNICODE { EscapedAtom (CharacterEscape (UnicodeEscape $2)) }
  | IDENTITY { EscapedAtom (CharacterEscape (IdentityEscape $1)) }
  | CONTROLESCAPE { EscapedAtom (CharacterEscape (ControlEscape ($1))) }
  | CONTROLLETTER { EscapedAtom (CharacterEscape (ControlLetter ($1))) }


assertion :
  | CARET { Beginning }
  | DOLLAR { End }
  | BACKLITTLEB { Word }
  | BACKBIGB { NotWord }
  | LPAREN QUESTION EQUALS disjunction RPAREN { QuestionEquals ($4) }
  | LPAREN QUESTION BANG disjunction RPAREN { QuestionBang ($4) }
