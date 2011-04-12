%{
open Prelude
open Es5_syntax
open JavaScript_syntax
open Desugar_helpers

(* All free variables "x" in the environment are renamed to "[[x]]" *)
let rename_env exp : exp  =
  let ren v exp = rename v ("[[" ^ v ^ "]]") exp in
  IdSet.fold ren (fv exp) exp

(* Macros for expanding arguments objects and function objects (a
little bit of desugaring)*)

let rec mk_val p v =
  [(Value, v);
   (Enum, true_c p);
   (Config, true_c p);
   (Writable, true_c p)]

let rec mk_field (p, s, e) =
  (p, s, mk_val p e)
    
let args_obj p arg_list callee = 
  let mk_field n v = (string_of_int n, 
		      mk_val p v) in
    EObject 
      (p, [("proto", EId (p, "Object_prototype"));
	   ("class", str p "Arguments");
	   ("extensible", false_c p)],
       (("length", [(Value, int_c p (List.length arg_list));
		    (Writable, true_c p);
		    (Enum, false_c p);
		    (Config, true_c p)])::
	("callee", [(Getter, 
		     EId (p, "[[ThrowTypeError]]"));
		    (Setter, 
		     EId (p, "[[ThrowTypeError]]"));
		    (Enum, false_c p);
		    (Config, false_c p)])::
	("caller", [(Getter, 
		     EId (p, "[[ThrowTypeError]]"));
		    (Setter, 
		     EId (p, "[[ThrowTypeError]]"));
		    (Enum, false_c p);
		    (Config, false_c p)])::
	  (List.map2 mk_field (iota (List.length arg_list)) arg_list)))
      

(* Used by getters and setters---the function will be known at
runtime *)
let args_thunk p arg_list = 
  ELambda (p, ["func"],
	   args_obj p arg_list (EId (p, "func")))


let rec func_expr_lambda p ids body =
  let folder id ix e = 
    ELet (p, 
	  id,
	  EGetFieldSurface (p, 
			    EId (p, "arguments"), 
			    EConst (p, S.CString (string_of_int ix)),
			    args_thunk p []),
	  e) in
    ELambda (p, 
	     ["this"; "arguments"],
	     List.fold_right2 folder ids (iota (List.length ids)) body)

let rec func_object p ids lambda_exp =
  ELet (p, "$prototype", 
	EObject (p,
		 [("proto", EId (p, "Object_prototype"));
		  ("extensible", true_c p);
		  ("class", EConst (p, S.CString ("Object")))],
		 [("constructor", 
		   [(Value, EConst (p, S.CUndefined));
		    (Writable, true_c p);
		    (Enum, false_c p);
		    (Config, true_c p)])]),
	ELet (p, "$funobj", 
	      EObject (p,
		       [("code", lambda_exp);
			("proto", EId (p, "Function_prototype"));
			("extensible", true_c p);
			("class", str p "Function")],
		       [("length", 
			 [(Value, EConst (p, S.CNum
					      (float_of_int
						 (List.length ids))));
			  (Writable, false_c p);
			  (Enum, false_c p);
			  (Config, false_c p)]);
			("prototype",
			 [(Value, EId (p, "$prototype")); 
			  (Writable, true_c p);
			  (Config, false_c p);
			  (Enum, false_c p)])]),
	      ESeq (p, EUpdateFieldSurface (p, 
					    EId (p, "$prototype"),
					    EConst (p, S.CString ("constructor")),
					    EId (p, "$funobj"),
					    args_thunk p [EId (p, "$funobj")]),
		    EId (p, "$funobj"))))

 %}

%token <int> INT
%token <float> NUM
%token <string> STRING
%token <bool> BOOL
%token <Prelude.id> ID
%token UNDEFINED NULL FUNC LET DELETE LBRACE RBRACE LPAREN RPAREN LBRACK
  RBRACK EQUALS COMMA DEREF REF COLON COLONEQ PRIM IF ELSE SEMI
  LABEL BREAK TRY CATCH FINALLY THROW LLBRACK RRBRACK EQEQEQUALS TYPEOF
  AMPAMP PIPEPIPE RETURN BANGEQEQUALS FUNCTION FIX WRITABLE GETTER SETTER
  CONFIG VALUE ENUM LT GT


%token EOF
%left COLONEQ
%left LPAREN
%left PIPEPIPE
%left AMPAMP
%left EQEQEQUALS BANGEQEQUALS
%left LBRACK

/* http://stackoverflow.com/questions/1737460/
   how-to-find-shift-reduce-conflict-in-this-yacc-file */

%type <Es5_syntax.exp> prog
%type <Es5_syntax.exp -> Es5_syntax.exp> env

%start prog
%start env


%%

const :
 | NUM { JavaScript_syntax.CNum $1 }
 | INT {  JavaScript_syntax.CInt $1 }
 | STRING {  JavaScript_syntax.CString $1 }
 | UNDEFINED { JavaScript_syntax.CUndefined }
 | NULL { JavaScript_syntax.CNull }
 | BOOL { JavaScript_syntax.CBool $1 }

attr :
 | STRING COLON exp { ($1, $3) }
 | ID COLON exp { ($1, $3) }

attrs :
 | { [] }
 | attr { [$1] }
 | attr COMMA attrs { $1 :: $3 }

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
 | { [] }
 | prop_attr { [$1] }
 | prop_attr COMMA prop_attrs { $1 :: $3 }

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
 | FUNC LPAREN ids RPAREN LBRACE RETURN seq_exp RBRACE
   { ELambda (($startpos, $endpos), $3, $7) }

atom :
 | const { EConst (($startpos, $endpos), $1) }
 | ID { EId (($startpos, $endpos), $1) }
 | LBRACE LBRACK attrs RBRACK props RBRACE 
   { EObject (($startpos, $endpos), $3, $5 )}
 | LBRACE seq_exp RBRACE
   { $2 }
 | LPAREN seq_exp RPAREN { $2 }
 | func { $1 }
 | FUNCTION LPAREN ids RPAREN LBRACE RETURN seq_exp RBRACE
     {
       let ids = $3 in
       let body = $7 in
       let p = ($startpos, $endpos) in
	 func_object p ids (func_expr_lambda p ids body)
     }
 | TYPEOF atom
     { EOp1 (($startpos, $endpos), Prim1 "typeof", $2) }
     
exp :
 | atom { $1 }
 | exp LPAREN exps RPAREN 
   { EApp (($startpos, $endpos), $1, $3) }
 | PRIM LPAREN STRING COMMA seq_exp COMMA seq_exp COMMA seq_exp RPAREN
   { EOp3 (($startpos, $endpos), Prim3 $3, $5, $7, $9) }
 | PRIM LPAREN STRING COMMA seq_exp COMMA seq_exp RPAREN
   { EOp2 (($startpos, $endpos), Prim2 $3, $5, $7) }
 | PRIM LPAREN STRING COMMA seq_exp RPAREN
   { EOp1 (($startpos, $endpos), Prim1 $3, $5) }
 | ID COLONEQ exp
   { ESet (($startpos, $endpos), $1, $3) }
 | exp EQEQEQUALS exp
     { EOp2 (($startpos, $endpos), Prim2 "stx=", $1, $3) }
 | exp BANGEQEQUALS exp
     { let p = ($startpos, $endpos) in
         EIf (p, EOp2 (p, Prim2 "stx=", $1, $3),
              EConst (p, CBool false),
              EConst (p, CBool true)) }
 | exp LBRACK seq_exp EQUALS seq_exp RBRACK
   { let p = ($startpos, $endpos) in
       ELet (p, "$newVal", $5,
	     EUpdateFieldSurface (p, $1, $3, 
				  EId (p, "$newVal"), 
				  args_thunk p [EId (p, "$newVal")])) }
 | exp LBRACK seq_exp RBRACK
   { let p = ($startpos, $endpos) in
     EGetFieldSurface (p, $1,  $3, args_thunk p []) }
 | exp LBRACK DELETE seq_exp RBRACK
     { EDeleteField (($startpos, $endpos), $1, $4) }
 | exp LBRACK seq_exp LT attr_name GT RBRACK
     { EAttr (($startpos, $endpos), $5, $1, $3) }
 | exp LBRACK seq_exp LT attr_name GT EQUALS seq_exp RBRACK
     { ESetAttr (($startpos, $endpos), $5, $1, $3, $8) }
 | exp AMPAMP exp
     { EIf (($startpos, $endpos), $1, 
            $3,
            EConst (($startpos, $endpos), CBool false)) }
 | exp PIPEPIPE exp
     { let p = ($startpos, $endpos) in
         ELet (p, "%or", $1,
               EIf (p, EId (p, "%or"), EId (p, "%or"), $3)) }
 | FIX ID exp 
     { EFix (($startpos, $endpos), $2, $3) }


cexp :
 | exp { $1 }
 | IF LPAREN seq_exp RPAREN seq_exp ELSE seq_exp
     { EIf (($startpos, $endpos), $3, $5, $7) }
 | IF LPAREN seq_exp RPAREN seq_exp
     { EIf (($startpos, $endpos), $3, $5, 
	    EConst (($startpos, $endpos), CUndefined)) }
 | LABEL ID COLON seq_exp
     { ELabel (($startpos, $endpos), $2, $4) } 
 | BREAK ID cexp
   { EBreak (($startpos, $endpos), $2, $3) }
 | THROW cexp
   { EThrow (($startpos, $endpos), $2) }
 | TRY LBRACE seq_exp RBRACE CATCH LBRACE seq_exp RBRACE
   { ETryCatch (($startpos, $endpos), $3, $7) }
 | TRY LBRACE seq_exp RBRACE FINALLY LBRACE seq_exp RBRACE
   { ETryFinally (($startpos, $endpos), $3, $7) }

seq_exp :
 | cexp { $1 }
 | LET LPAREN ID EQUALS seq_exp RPAREN seq_exp
   { ELet (($startpos, $endpos), $3, $5, $7) }
 | cexp SEMI seq_exp
   { ESeq (($startpos, $endpos), $1, $3) }

env :
 | EOF
     { fun x -> x }
 | LET LLBRACK ID RRBRACK EQUALS seq_exp env
     { fun x -> 
         ELet (($startpos, $endpos), "[[" ^ $3 ^ "]]", rename_env $6, $7 x) }
 | LBRACE seq_exp RBRACE env
     { fun x -> ESeq (($startpos, $endpos), rename_env $2, $4 x) }

prog :
 | seq_exp EOF { $1 }
%%
