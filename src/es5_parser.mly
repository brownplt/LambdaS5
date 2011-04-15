%{
open Prelude
open Es5_syntax

let true_c p = True p
let false_c p = False p

let undef_c p = Undefined p

let str p s = String (p, s)

let num_c p d = Num (p, d)
let int_c p d = Num (p, float_of_int d)

(* All free variables "x" in the environment are renamed to "[[x]]" *)
let rename_env exp : exp  =
  let ren v exp = rename v ("[[" ^ v ^ "]]") exp in
  IdSet.fold ren (fv exp) exp

(* Macros for expanding arguments objects and function objects (a
little bit of desugaring)*)

let rec mk_val p v =
  Data ({ value = v; writable = true }, true, true)

let rec mk_field (p, s, e) =
  (p, s, mk_val p e)
    
let args_obj p arg_list callee = 
  let mk_field n v = (string_of_int n, 
		      mk_val p v) in
    Object 
      (p, {proto = Some (Id (p, "Object_prototype"));
           klass = "Arguments";
           extensible = false;
           code = None},
       (("length", Data ({value = int_c p (List.length arg_list);
		         writable = true; },
	                 false, true))::
	("callee", Accessor ({getter = Id (p, "[[ThrowTypeError]]");
		              setter = Id (p, "[[ThrowTypeError]]"); },
		             false, false ))::
	("caller", Accessor ({getter = Id (p, "[[ThrowTypeError]]");
		              setter = Id (p, "[[ThrowTypeError]]"); },
                             false, false ))::
	  (List.map2 mk_field (iota (List.length arg_list)) arg_list)))
      

(* Used by getters and setters---the function will be known at
runtime *)
let args_thunk p arg_list = 
  Lambda (p, ["func"],
	  args_obj p arg_list (Id (p, "func")))


let rec func_expr_lambda p ids body =
  let folder id ix e = 
    Let (p, 
	  id,
	  GetField (p, 
		    Id (p, "arguments"), 
		    str p (string_of_int ix),
		    args_thunk p []),
	  e) in
  Lambda (p, 
	  ["this"; "arguments"],
	  List.fold_right2 folder ids (iota (List.length ids)) body)

(*let rec func_object p ids lambda_exp =
  Let (p, "$prototype", 
       Object (p,
	       [("proto", Id (p, "Object_prototype"));
		("extensible", true_c p);
		("class", Const (p, S.CString ("Object")))],
	       [("constructor", 
		 [(Value, Const (p, S.CUndefined));
		  (Writable, true_c p);
		  (Enum, false_c p);
		  (Config, true_c p)])]),
       Let (p, "$funobj", 
	      Object (p,
		       [("code", lambda_exp);
			("proto", Id (p, "Function_prototype"));
			("extensible", true_c p);
			("class", str p "Function")],
		       [("length", 
			 [(Value, Const (p, S.CNum
			   (float_of_int
			      (List.length ids))));
			  (Writable, false_c p);
			  (Enum, false_c p);
			  (Config, false_c p)]);
			("prototype",
			 [(Value, Id (p, "$prototype")); 
			  (Writable, true_c p);
			  (Config, false_c p);
			  (Enum, false_c p)])]),
	     Seq (p, UpdateFieldSurface (p, 
					   Id (p, "$prototype"),
					   str p "constructor",
					   Id (p, "$funobj"),
					   args_thunk p [EId (p, "$funobj")]),
		   Id (p, "$funobj"))))
*)


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
  CONFIG VALUE ENUM LT GT PROTO CODE EXTENSIBLE CLASS


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
 | NUM { Num (($startpos, $endpos), $1) }
 | INT {  Num (($startpos, $endpos), (float_of_int $1)) }
 | STRING {  String (($startpos, $endpos), $1) }
 | UNDEFINED { Undefined (($startpos, $endpos)) }
 | NULL { Null ($startpos, $endpos) }
 | BOOL { if $1 then True ($startpos, $endpos) else False ($startpos, $endpos) }

oattrsv :
 | { d_attrs }
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
 | { Generic (false, false) }
 | WRITABLE BOOL COMMA VALUE exp 
     { Data ({ value = $5; writable = $2 }, true, true) }
 | VALUE exp COMMA WRITABLE BOOL
     { Data ({ value = $2; writable = $5 }, true, true) }
 | GETTER exp COMMA SETTER exp 
     { Accessor ({ getter = $2; setter = $5 }, true, true) }

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
   { Lambda (($startpos, $endpos), $3, $7) }

atom :
 | const { $1 }
 | ID { Id (($startpos, $endpos), $1) }
 | LBRACE LBRACK oattrsv RBRACK props RBRACE 
   { Object (($startpos, $endpos), $3, $5 )}
 | LBRACE seq_exp RBRACE
   { $2 }
 | LPAREN seq_exp RPAREN { $2 }
 | func { $1 }
 | FUNCTION LPAREN ids RPAREN LBRACE RETURN seq_exp RBRACE
     {
       let ids = $3 in
       let body = $7 in
       let p = ($startpos, $endpos) in
       String (p, "no functions yet")
(*	 func_object p ids (func_expr_lambda p ids body) *)
     }
 | TYPEOF atom
     { Op1 (($startpos, $endpos), "typeof", $2) }
     
exp :
 | atom { $1 }
 | exp LPAREN exps RPAREN 
   { App (($startpos, $endpos), $1, $3) }
 | PRIM LPAREN STRING COMMA seq_exp COMMA seq_exp RPAREN
   { Op2 (($startpos, $endpos), $3, $5, $7) }
 | PRIM LPAREN STRING COMMA seq_exp RPAREN
   { Op1 (($startpos, $endpos), $3, $5) }
 | ID COLONEQ exp
   { SetBang (($startpos, $endpos), $1, $3) }
 | exp EQEQEQUALS exp
     { Op2 (($startpos, $endpos), "stx=", $1, $3) }
 | exp BANGEQEQUALS exp
     { let p = ($startpos, $endpos) in
         If (p, Op2 (p, "stx=", $1, $3),
             False p, True p) }
 | exp LBRACK seq_exp EQUALS seq_exp RBRACK
   { let p = ($startpos, $endpos) in
       Let (p, "$newVal", $5,
	     SetField (p, $1, $3, 
		       Id (p, "$newVal"), 
		       args_thunk p [Id (p, "$newVal")])) }
 | exp LBRACK seq_exp RBRACK
   { let p = ($startpos, $endpos) in
     GetField (p, $1,  $3, args_thunk p []) }
 | exp LBRACK DELETE seq_exp RBRACK
     { DeleteField (($startpos, $endpos), $1, $4) }
 | exp LBRACK seq_exp LT attr_name GT RBRACK
     { GetAttr (($startpos, $endpos), $5, $1, $3) }
 | exp LBRACK seq_exp LT attr_name GT EQUALS seq_exp RBRACK
     { SetAttr (($startpos, $endpos), $5, $1, $3, $8) }
 | exp AMPAMP exp
     { If (($startpos, $endpos), $1, 
            $3, False ($startpos, $endpos)) }
 | exp PIPEPIPE exp
     { let p = ($startpos, $endpos) in
         Let (p, "%or", $1,
               If (p, Id (p, "%or"), Id (p, "%or"), $3)) }


cexp :
 | exp { $1 }
 | IF LPAREN seq_exp RPAREN seq_exp ELSE seq_exp
     { If (($startpos, $endpos), $3, $5, $7) }
 | IF LPAREN seq_exp RPAREN seq_exp
     { If (($startpos, $endpos), $3, $5, 
	    Undefined ($startpos, $endpos)) }
 | LABEL ID COLON seq_exp
     { Label (($startpos, $endpos), $2, $4) } 
 | BREAK ID cexp
   { Break (($startpos, $endpos), $2, $3) }
 | THROW cexp
   { Throw (($startpos, $endpos), $2) }
 | TRY LBRACE seq_exp RBRACE CATCH LBRACE seq_exp RBRACE
   { TryCatch (($startpos, $endpos), $3, $7) }
 | TRY LBRACE seq_exp RBRACE FINALLY LBRACE seq_exp RBRACE
   { TryFinally (($startpos, $endpos), $3, $7) }

seq_exp :
 | cexp { $1 }
 | LET LPAREN ID EQUALS seq_exp RPAREN seq_exp
   { Let (($startpos, $endpos), $3, $5, $7) }
 | cexp SEMI seq_exp
   { Seq (($startpos, $endpos), $1, $3) }

env :
 | EOF
     { fun x -> x }
 | LET LLBRACK ID RRBRACK EQUALS seq_exp env
     { fun x -> 
         Let (($startpos, $endpos), "[[" ^ $3 ^ "]]", rename_env $6, $7 x) }
 | LBRACE seq_exp RBRACE env
     { fun x -> Seq (($startpos, $endpos), rename_env $2, $4 x) }

prog :
 | seq_exp EOF { $1 }
%%
