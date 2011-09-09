%{
open Prelude
open Es5_syntax

let true_c p = True p
let false_c p = False p

let undef_c p = Undefined p

let str p s = String (p, s)

let num_c p d = Num (p, d)
let int_c p d = Num (p, float_of_int d)

(* Macros for expanding arguments objects and function objects (a
little bit of desugaring)*)

let rec mk_val p v =
  Data ({ value = v; writable = true }, true, true)

let rec mk_field (p, s, e) =
  (p, s, mk_val p e)

%}

%token <int> INT
%token <float> NUM
%token <string> STRING
%token <bool> BOOL
%token <Prelude.id> ID
%token UNDEFINED NULL FUNC LET DELETE LBRACE RBRACE LPAREN RPAREN LBRACK
  RBRACK EQUALS COMMA DEREF REF COLON COLONEQ PRIM IF ELSE SEMI
  LABEL BREAK TRY CATCH FINALLY THROW EQEQEQUALS TYPEOF
  AMPAMP PIPEPIPE RETURN BANGEQEQUALS FUNCTION REC WRITABLE GETTER SETTER
  CONFIG VALUE ENUM LT GT PROTO CODE EXTENSIBLE CLASS EVAL


%token EOF
%left COLONEQ
%left LPAREN
%left PIPEPIPE
%left AMPAMP
%left EQEQEQUALS BANGEQEQUALS
%left LBRACK


%type <Es5_syntax.exp> prog
%type <Es5_syntax.exp -> Es5_syntax.exp> env

%start prog
%start env


%%

const :
 | NUM { Num ((Parsing.rhs_start_pos 1, Parsing.rhs_end_pos 1), $1) }
 | INT {  Num ((Parsing.rhs_start_pos 1, Parsing.rhs_end_pos 1), (float_of_int $1)) }
 | STRING {  String ((Parsing.rhs_start_pos 1, Parsing.rhs_end_pos 1), $1) }
 | UNDEFINED { Undefined ((Parsing.rhs_start_pos 1, Parsing.rhs_end_pos 1)) }
 | NULL { Null (Parsing.rhs_start_pos 1, Parsing.rhs_end_pos 1) }
 | BOOL { if $1 then True (Parsing.rhs_start_pos 1, Parsing.rhs_end_pos 1) else False (Parsing.rhs_start_pos 1, Parsing.rhs_end_pos 1) }

oattrsv :
 | { d_attrs }
 | VALUE COLON exp COMMA oattrsv { { $5 with primval = Some $3 } }
 | EXTENSIBLE COLON BOOL COMMA oattrsv { { $5 with extensible = $3 } }
 | PROTO COLON exp COMMA oattrsv { { $5 with proto = Some $3 } }
 | CODE COLON exp COMMA oattrsv { {$5 with code = Some $3 } }
 | CLASS COLON STRING COMMA oattrsv { { $5 with klass = $3 } }

attr_name :
 | WRITABLE { Writable }
 | CONFIG { Config }
 | VALUE { Value }
 | SETTER { Setter }
 | GETTER { Getter }
 | ENUM { Enum }

prop_attr :
 | attr_name COLON exp { ($1, $3) }

prop_attrs :
 | WRITABLE BOOL COMMA VALUE exp 
     { Data ({ value = $5; writable = $2 }, false, true) }
 | VALUE exp COMMA WRITABLE BOOL
     { Data ({ value = $2; writable = $5 }, false, false) }
 | VALUE exp COMMA WRITABLE BOOL COMMA CONFIG BOOL
     { Data ({ value = $2; writable = $5 }, $8, false) }
 | GETTER exp COMMA SETTER exp 
     { Accessor ({ getter = $2; setter = $5 }, false, true) }

prop :
 | STRING COLON LBRACE prop_attrs RBRACE { ($1, $4) }
 | ID COLON LBRACE prop_attrs RBRACE { ($1, $4) }

props :
 | { [] }
 | prop { [$1] }
 | prop COMMA props { $1 :: $3 }

exps :
 | { [] }
 | seq_exp { [$1] }
 | seq_exp COMMA exps { $1 :: $3 }

ids :
 | { [] }
 | ID { [$1] }
 | ID COMMA ids { $1 :: $3 }

func :
 | FUNC LPAREN ids RPAREN LBRACE seq_exp RBRACE
   { Lambda ((Parsing.rhs_start_pos 1, Parsing.rhs_end_pos 7), $3, $6) }

atom :
 | const { $1 }
 | ID { Id ((Parsing.rhs_start_pos 1, Parsing.rhs_end_pos 1), $1) }
 | LBRACE LBRACK oattrsv RBRACK props RBRACE 
   { Object ((Parsing.rhs_start_pos 1, Parsing.rhs_end_pos 6), $3, $5 )}
 | LBRACE seq_exp RBRACE
   { $2 }
 | LPAREN seq_exp RPAREN { $2 }
 | func { $1 }
 | TYPEOF atom
     { Op1 ((Parsing.rhs_start_pos 1, Parsing.rhs_end_pos 2), "typeof", $2) }
     
exp :
 | atom { $1 }
 | exp LPAREN exps RPAREN 
   { App ((Parsing.rhs_start_pos 1, Parsing.rhs_end_pos 4), $1, $3) }
 | EVAL LPAREN exp RPAREN
     { Eval ((Parsing.rhs_start_pos 1, Parsing.rhs_end_pos 4), $3) }
 | PRIM LPAREN STRING COMMA seq_exp COMMA seq_exp RPAREN
   { Op2 ((Parsing.rhs_start_pos 1, Parsing.rhs_end_pos 8), $3, $5, $7) }
 | PRIM LPAREN STRING COMMA seq_exp RPAREN
   { Op1 ((Parsing.rhs_start_pos 1, Parsing.rhs_end_pos 6), $3, $5) }
 | ID COLONEQ exp
   { SetBang ((Parsing.rhs_start_pos 1, Parsing.rhs_end_pos 3), $1, $3) }
 | exp EQEQEQUALS exp
     { Op2 ((Parsing.rhs_start_pos 1, Parsing.rhs_end_pos 3), "stx=", $1, $3) }
 | exp BANGEQEQUALS exp
     { let p = (Parsing.rhs_start_pos 1, Parsing.rhs_end_pos 3) in
         If (p, Op2 (p, "stx=", $1, $3),
             False p, True p) }
 | exp LBRACK seq_exp EQUALS seq_exp RBRACK
   { let p = (Parsing.rhs_start_pos 1, Parsing.rhs_end_pos 6) in
       Let (p, "$newVal", $5,
	     SetField (p, $1, $3, 
		       Id (p, "$newVal"), 
		       Object (p, d_attrs,
            [("0", Data ({ value = Id (p, "$newVal");
                          writable = true },
              true, true))])))
    }
 | exp LBRACK seq_exp EQUALS seq_exp COMMA seq_exp RBRACK
   { SetField ((Parsing.rhs_start_pos 1, Parsing.rhs_end_pos 8), $1, $3, $5, $7) }
 | exp LBRACK seq_exp RBRACK
   { let p = (Parsing.rhs_start_pos 1, Parsing.rhs_end_pos 4) in
     GetField (p, $1,  $3,
		       Object (p, d_attrs,
            [])) }
 | exp LBRACK seq_exp COMMA seq_exp RBRACK
   { GetField ((Parsing.rhs_start_pos 1, Parsing.rhs_end_pos 6), $1,  $3, $5) }
 | exp LBRACK DELETE seq_exp RBRACK
     { DeleteField ((Parsing.rhs_start_pos 1, Parsing.rhs_end_pos 5), $1, $4) }
 | exp LBRACK seq_exp LT attr_name GT RBRACK
     { GetAttr ((Parsing.rhs_start_pos 1, Parsing.rhs_end_pos 7), $5, $1, $3) }
 | exp LBRACK seq_exp LT attr_name GT EQUALS seq_exp RBRACK
     { SetAttr ((Parsing.rhs_start_pos 1, Parsing.rhs_end_pos 9), $5, $1, $3, $8) }
 | exp AMPAMP exp
     { If ((Parsing.rhs_start_pos 1, Parsing.rhs_end_pos 3), $1, 
            $3, False (Parsing.rhs_start_pos 1, Parsing.rhs_end_pos 3)) }
 | exp PIPEPIPE exp
     { let p = (Parsing.rhs_start_pos 1, Parsing.rhs_end_pos 3) in
         Let (p, "%or", $1,
               If (p, Id (p, "%or"), Id (p, "%or"), $3)) }


cexp :
 | exp { $1 }
 | IF LPAREN seq_exp RPAREN seq_exp ELSE seq_exp
     { If ((Parsing.rhs_start_pos 1, Parsing.rhs_end_pos 7), $3, $5, $7) }
 | IF LPAREN seq_exp RPAREN seq_exp
     { If ((Parsing.rhs_start_pos 1, Parsing.rhs_end_pos 5), $3, $5, 
	    Undefined (Parsing.rhs_start_pos 1, Parsing.rhs_end_pos 5)) }
 | LABEL ID COLON seq_exp
     { Label ((Parsing.rhs_start_pos 1, Parsing.rhs_end_pos 4), $2, $4) } 
 | BREAK ID cexp
   { Break ((Parsing.rhs_start_pos 1, Parsing.rhs_end_pos 3), $2, $3) }
 | THROW cexp
   { Throw ((Parsing.rhs_start_pos 1, Parsing.rhs_end_pos 2), $2) }
 | TRY LBRACE seq_exp RBRACE CATCH LBRACE seq_exp RBRACE
   { TryCatch ((Parsing.rhs_start_pos 1, Parsing.rhs_end_pos 8), $3, $7) }
 | TRY LBRACE seq_exp RBRACE FINALLY LBRACE seq_exp RBRACE
   { TryFinally ((Parsing.rhs_start_pos 1, Parsing.rhs_end_pos 8), $3, $7) }

seq_exp :
 | cexp { $1 }
 | LET LPAREN ID EQUALS seq_exp RPAREN seq_exp
   { Let ((Parsing.rhs_start_pos 1, Parsing.rhs_end_pos 7), $3, $5, $7) }
 | REC LPAREN ID EQUALS seq_exp RPAREN seq_exp
   { Rec ((Parsing.rhs_start_pos 1, Parsing.rhs_end_pos 7), $3, $5, $7) }
 | cexp SEMI seq_exp
   { Seq ((Parsing.rhs_start_pos 1, Parsing.rhs_end_pos 3), $1, $3) }

env :
 | EOF
     { fun x -> x }
 | LET LBRACK ID RBRACK EQUALS seq_exp env
     { let p = (Parsing.rhs_start_pos 1, Parsing.rhs_end_pos 7) in
         fun x -> 
           Let (p, $3, $6, $7 x) }
 | LBRACE seq_exp RBRACE env
     { let p = (Parsing.rhs_start_pos 1, Parsing.rhs_end_pos 4) in
         fun x -> Seq (p, $2, $4 x) }

prog :
 | seq_exp EOF { $1 }
%%
