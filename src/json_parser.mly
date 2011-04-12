%{
  (* 
     Notes about error messages and error locations in ocamlyacc:
     
     1) There is a predefined "error" symbol which can be used as a catch-all,
     in order to get the location of the token that shouldn't be there.
     
     2) Additional rules that match common errors are added, so that when
     they are matched, a nice, handcrafted error message is produced.
     
     3) Token locations are retrieved using functions from the Parsing
     module, which relies on a global state. If you want your error locations
     to be reliable, don't run two ocamlyacc parsers simultaneously.
     

     In the end, the error messages are nicer than the ones that a camlp4
     parser (extensible grammar) would produce because we write them
     manually. However camlp4's messages are all automatic, 
     i.e. they tell you which tokens were expected at a given location.

     For the file/line/char locations to be correct, 
     the lexbuf must be adjusted by the lexer when the file name
     changes or a new line is encountered. This is not performed automatically
     by ocamllex, see file json_lexer.mll.
  *)

  open Printf
  open Json_type
  open Prelude

  let json_error str  = raise (Json_error str)
			
  let rhs_loc n = (Parsing.rhs_start_pos n, Parsing.rhs_end_pos n)
		    
  let unclosed opening_name opening_num closing_name closing_num =
    let msg = 
      sprintf "%s:\nSyntax error: '%s' expected.\n\
               %s:\nThis '%s' might be unmatched."
	(string_of_position (rhs_loc closing_num)) closing_name
	(string_of_position (rhs_loc opening_num)) opening_name in
    json_error msg

  let syntax_error s num =
    let msg = sprintf "%s:\n%s" (string_of_position (rhs_loc num)) s in
    json_error msg

%}
%token <string> STRING
%token <int> INT
%token <float> FLOAT
%token <bool> BOOL
%token OBJSTART OBJEND ARSTART AREND NULL COMMA COLON
%token EOF
%start main
%type <Json_type.t> main
%%
main:
| value EOF    { $1 }
| value error  { syntax_error "Junk after end of data" 2 }
| EOF          { syntax_error "Empty data" 1 }
| error        { syntax_error "Syntax error" 1 }
;
value:
| OBJSTART pair_list OBJEND { Object $2 }
| OBJSTART OBJEND           { Object [] }
| OBJSTART pair_list EOF    { unclosed "{" 1 "}" 3 }
| OBJSTART pair_list error  { unclosed "{" 1 "}" 3 }
| OBJSTART error            { syntax_error 
				"Expecting a comma-separated sequence \
                                 of string:value pairs" 2 }
| ARSTART value_list AREND  { Array $2 }
| ARSTART AREND             { Array [] }
| ARSTART value_list EOF    { unclosed "[" 1 "]" 3 }
| ARSTART value_list error  { unclosed "[" 1 "]" 3 }
| ARSTART error             { syntax_error 
				"Expecting a comma-separated sequence \
                                 of values" 2 }
| STRING { String $1 }
| BOOL { Bool $1 }
| NULL { Null }
| INT  { Int $1 }
| FLOAT { Float $1 }
;
pair_list:
| STRING COLON value COMMA pair_list { ($1, $3) :: $5 }
| STRING COLON value COMMA OBJEND 
                             { syntax_error 
				"End-of-object commas are illegal" 4 }
| STRING COLON value STRING  { syntax_error "Missing ','" 4 }
| STRING COLON value         { [ ($1, $3) ] }
;
value_list:
| value COMMA value_list { $1 :: $3 }
| value COMMA AREND      { syntax_error 
			     "End-of-array commas are illegal" 2 }
| value value            { syntax_error "Missing ',' before this value" 2 }
| value                  { [ $1 ] }
;
