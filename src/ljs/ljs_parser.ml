type token =
  | INT of (int)
  | NUM of (float)
  | STRING of (string)
  | HINT of (string)
  | BOOL of (bool)
  | ID of (Prelude.id)
  | UNDEFINED
  | NULL
  | FUNC
  | LET
  | DELETE
  | LBRACE
  | RBRACE
  | LPAREN
  | RPAREN
  | LBRACK
  | RBRACK
  | EQUALS
  | COMMA
  | DEREF
  | REF
  | COLON
  | COLONEQ
  | PRIM
  | IF
  | ELSE
  | SEMI
  | LABEL
  | BREAK
  | TRY
  | CATCH
  | FINALLY
  | THROW
  | EQEQEQUALS
  | TYPEOF
  | AMPAMP
  | PIPEPIPE
  | RETURN
  | BANGEQEQUALS
  | FUNCTION
  | REC
  | WRITABLE
  | GETTER
  | SETTER
  | CONFIG
  | VALUE
  | ENUM
  | LT
  | GT
  | PROTO
  | CODE
  | EXTENSIBLE
  | CLASS
  | EVAL
  | GETFIELDS
  | PRIMVAL
  | EOF

open Parsing;;
# 1 "ljs/ljs_parser.mly"

open Prelude
open Ljs_syntax

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

let with_pos exp pos = match exp with
  | Null _ -> Null pos
  | Undefined _ -> Undefined pos
  | String (_, str) -> String (pos, str)
  | Num (_, num) -> Num (pos, num)
  | True _ -> True pos
  | False _ -> False pos
  | Id (_, id) -> Id (pos, id)
  | Object (_, attrs, props) -> Object (pos, attrs, props)
  | GetAttr (_, pattr, obj, field) -> GetAttr (pos, pattr, obj, field)
  | SetAttr (_, prop, obj, field, value) -> SetAttr (pos, prop, obj, field, value)
  | GetObjAttr (_, oattr, obj) -> GetObjAttr (pos, oattr, obj)
  | SetObjAttr (_, oattr, obj, v) -> SetObjAttr (pos, oattr, obj, v)
  | GetField (_, left, right, args) -> GetField (pos, left, right, args)
  | SetField (_, obj, field, value, args) -> SetField (pos, obj, field, value, args)
  | DeleteField (_, obj, field) -> DeleteField (pos, obj, field)
  | OwnFieldNames (_, obj) -> OwnFieldNames(pos, obj)
  | SetBang (_, id, exp) -> SetBang (pos, id, exp)
  | Op1 (_, op, exp) -> Op1 (pos, op, exp)
  | Op2 (_, op, left, right) -> Op2 (pos, op, left, right)
  | If (_, test, trueBlock, falseBlock) -> If (pos, test, trueBlock, falseBlock)
  | App (_, func, args) -> App (pos, func, args)
  | Seq (_, left, right) -> Seq (pos, left, right)
  | Let (_, id, value, body) -> Let (pos, id, value, body)
  | Rec (_, id, value, body) -> Rec (pos, id, value, body)
  | Label (_, id, exp) -> Label (pos, id, exp)
  | Break (_, id, exp) -> Break (pos, id, exp)
  | TryCatch (_, tryBlock, catchBlock) -> TryCatch (pos, tryBlock, catchBlock)
  | TryFinally (_, tryBlock, finallyBlock) -> TryFinally (pos, tryBlock, finallyBlock)
  | Throw (_, value) -> Throw (pos, value)
  | Lambda (_, ids, body) -> Lambda (pos, ids, body)
  | Eval (_, exp) -> Eval (pos, exp)
  | Hint (_, label, exp) -> Hint (pos, label, exp)

# 120 "ljs/ljs_parser.ml"
let yytransl_const = [|
  263 (* UNDEFINED *);
  264 (* NULL *);
  265 (* FUNC *);
  266 (* LET *);
  267 (* DELETE *);
  268 (* LBRACE *);
  269 (* RBRACE *);
  270 (* LPAREN *);
  271 (* RPAREN *);
  272 (* LBRACK *);
  273 (* RBRACK *);
  274 (* EQUALS *);
  275 (* COMMA *);
  276 (* DEREF *);
  277 (* REF *);
  278 (* COLON *);
  279 (* COLONEQ *);
  280 (* PRIM *);
  281 (* IF *);
  282 (* ELSE *);
  283 (* SEMI *);
  284 (* LABEL *);
  285 (* BREAK *);
  286 (* TRY *);
  287 (* CATCH *);
  288 (* FINALLY *);
  289 (* THROW *);
  290 (* EQEQEQUALS *);
  291 (* TYPEOF *);
  292 (* AMPAMP *);
  293 (* PIPEPIPE *);
  294 (* RETURN *);
  295 (* BANGEQEQUALS *);
  296 (* FUNCTION *);
  297 (* REC *);
  298 (* WRITABLE *);
  299 (* GETTER *);
  300 (* SETTER *);
  301 (* CONFIG *);
  302 (* VALUE *);
  303 (* ENUM *);
  304 (* LT *);
  305 (* GT *);
  306 (* PROTO *);
  307 (* CODE *);
  308 (* EXTENSIBLE *);
  309 (* CLASS *);
  310 (* EVAL *);
  311 (* GETFIELDS *);
  312 (* PRIMVAL *);
    0 (* EOF *);
    0|]

let yytransl_block = [|
  257 (* INT *);
  258 (* NUM *);
  259 (* STRING *);
  260 (* HINT *);
  261 (* BOOL *);
  262 (* ID *);
    0|]

let yylhs = "\255\255\
\003\000\003\000\003\000\003\000\003\000\003\000\004\000\004\000\
\004\000\004\000\004\000\004\000\006\000\006\000\006\000\006\000\
\006\000\007\000\007\000\007\000\007\000\007\000\007\000\008\000\
\008\000\008\000\008\000\009\000\009\000\010\000\010\000\010\000\
\011\000\011\000\011\000\013\000\013\000\013\000\014\000\016\000\
\016\000\016\000\016\000\016\000\016\000\016\000\005\000\005\000\
\005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\
\005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\
\005\000\005\000\017\000\017\000\017\000\017\000\017\000\017\000\
\017\000\017\000\018\000\018\000\018\000\015\000\012\000\012\000\
\019\000\019\000\019\000\002\000\002\000\002\000\002\000\001\000\
\000\000\000\000"

let yylen = "\002\000\
\001\000\001\000\001\000\001\000\001\000\001\000\000\000\005\000\
\005\000\005\000\005\000\005\000\001\000\001\000\001\000\001\000\
\001\000\001\000\001\000\001\000\001\000\001\000\001\000\005\000\
\005\000\008\000\005\000\005\000\005\000\000\000\001\000\003\000\
\000\000\001\000\003\000\000\000\001\000\003\000\005\000\001\000\
\001\000\006\000\001\000\003\000\001\000\002\000\001\000\004\000\
\004\000\004\000\008\000\006\000\003\000\003\000\003\000\006\000\
\008\000\004\000\006\000\005\000\007\000\009\000\006\000\008\000\
\003\000\003\000\001\000\001\000\004\000\004\000\003\000\002\000\
\004\000\004\000\007\000\007\000\005\000\003\000\003\000\001\000\
\001\000\007\000\007\000\001\000\007\000\007\000\002\000\002\000\
\002\000\002\000"

let yydefred = "\000\000\
\000\000\000\000\000\000\002\000\001\000\003\000\006\000\000\000\
\004\000\005\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\089\000\040\000\000\000\000\000\045\000\043\000\047\000\081\000\
\068\000\000\000\000\000\000\000\000\000\084\000\090\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\072\000\041\000\000\000\046\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\088\000\000\000\000\000\000\000\087\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\078\000\000\000\044\000\000\000\000\000\000\000\071\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\079\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\069\000\000\000\000\000\070\000\073\000\074\000\000\000\
\050\000\049\000\048\000\000\000\000\000\014\000\015\000\017\000\
\016\000\013\000\000\000\058\000\000\000\000\000\000\000\000\000\
\000\000\038\000\039\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\035\000\060\000\000\000\000\000\000\000\018\000\022\000\021\000\
\019\000\020\000\023\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\042\000\
\052\000\000\000\000\000\000\000\063\000\000\000\056\000\000\000\
\059\000\000\000\000\000\000\000\082\000\010\000\011\000\009\000\
\012\000\008\000\000\000\000\000\032\000\000\000\076\000\075\000\
\083\000\000\000\000\000\061\000\000\000\085\000\086\000\000\000\
\000\000\000\000\000\000\000\000\051\000\064\000\057\000\000\000\
\000\000\000\000\000\000\028\000\029\000\062\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\026\000"

let yydgoto = "\003\000\
\025\000\039\000\026\000\080\000\027\000\131\000\164\000\211\000\
\148\000\149\000\093\000\045\000\073\000\029\000\030\000\031\000\
\032\000\033\000\034\000"

let yysindex = "\080\000\
\018\001\011\000\000\000\000\000\000\000\000\000\000\000\240\254\
\000\000\000\000\010\255\015\255\182\000\237\000\019\255\033\255\
\014\255\064\255\000\255\055\001\150\255\053\255\059\255\071\255\
\000\000\000\000\091\255\087\000\000\000\000\000\000\000\000\000\
\000\000\069\255\073\255\018\001\082\255\000\000\000\000\011\000\
\029\255\110\255\117\255\062\255\116\255\055\001\118\255\138\255\
\018\001\120\255\055\001\063\255\000\000\000\000\018\001\000\000\
\140\255\029\255\029\255\018\001\192\255\029\255\029\255\029\255\
\029\255\000\000\018\001\143\255\144\255\000\000\091\255\125\255\
\139\255\142\255\141\255\147\255\148\255\149\255\159\255\165\255\
\000\000\151\255\000\000\146\255\172\255\000\255\000\000\000\255\
\000\255\170\255\040\255\085\255\181\255\186\255\018\001\087\255\
\247\254\052\255\026\255\072\255\052\255\000\000\191\255\193\255\
\110\255\000\255\018\001\029\255\029\255\207\255\210\255\029\255\
\055\255\000\000\018\001\000\255\000\000\000\000\000\000\206\255\
\000\000\000\000\000\000\018\001\201\255\000\000\000\000\000\000\
\000\000\000\000\174\255\000\000\018\001\018\001\132\255\208\255\
\212\255\000\000\000\000\204\255\195\255\222\255\205\255\209\255\
\229\255\213\255\215\255\220\255\231\255\254\254\228\255\227\255\
\000\000\000\000\086\255\061\255\238\255\000\000\000\000\000\000\
\000\000\000\000\000\000\211\255\018\001\018\001\018\001\062\255\
\062\255\062\255\062\255\062\255\245\255\250\255\055\255\000\000\
\000\000\018\001\246\254\018\001\000\000\018\001\000\000\018\001\
\000\000\114\255\011\000\011\000\000\000\000\000\000\000\000\000\
\000\000\000\000\006\255\006\255\000\000\249\255\000\000\000\000\
\000\000\005\000\008\000\000\000\018\001\000\000\000\000\025\000\
\029\255\029\255\021\000\023\000\000\000\000\000\000\000\022\000\
\024\000\097\000\185\000\000\000\000\000\000\000\254\255\003\000\
\012\000\029\255\029\255\040\000\091\255\091\255\027\000\015\000\
\052\000\000\000"

let yyrindex = "\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\102\000\000\000\000\000\000\000\000\000\000\000\
\000\000\161\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\051\000\000\000\050\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\053\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\134\000\055\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\060\000\000\000\000\000\
\000\000\014\000\059\000\091\000\046\000\000\000\000\000\000\000\
\051\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\066\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\053\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\068\000\000\000\000\000\145\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\050\000\
\050\000\050\000\050\000\050\000\000\000\000\000\066\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\071\000\075\000\076\000\000\000\
\000\000\000\000"

let yygindex = "\000\000\
\000\000\216\255\000\000\081\000\219\255\000\000\000\000\150\000\
\000\000\172\000\224\000\002\000\244\000\233\000\004\000\077\001\
\255\255\176\000\094\255"

let yytablesize = 622
let yytable = "\070\000\
\041\000\036\000\028\000\071\000\189\000\040\000\041\000\132\000\
\133\000\134\000\038\000\036\000\177\000\054\000\016\000\047\000\
\178\000\201\000\053\000\050\000\091\000\092\000\052\000\042\000\
\098\000\099\000\100\000\101\000\043\000\004\000\005\000\006\000\
\048\000\007\000\008\000\009\000\010\000\011\000\135\000\060\000\
\013\000\061\000\055\000\040\000\082\000\055\000\049\000\208\000\
\209\000\087\000\085\000\210\000\015\000\060\000\121\000\061\000\
\047\000\146\000\065\000\062\000\147\000\094\000\097\000\021\000\
\065\000\060\000\057\000\061\000\102\000\051\000\141\000\142\000\
\058\000\062\000\145\000\063\000\064\000\183\000\065\000\184\000\
\001\000\002\000\023\000\024\000\059\000\060\000\066\000\061\000\
\068\000\117\000\066\000\118\000\119\000\088\000\089\000\067\000\
\125\000\069\000\060\000\122\000\061\000\067\000\181\000\182\000\
\060\000\062\000\061\000\063\000\140\000\139\000\065\000\075\000\
\076\000\077\000\078\000\072\000\150\000\079\000\062\000\151\000\
\063\000\064\000\074\000\065\000\062\000\094\000\063\000\064\000\
\081\000\065\000\204\000\205\000\083\000\053\000\156\000\157\000\
\126\000\127\000\128\000\129\000\084\000\086\000\130\000\105\000\
\077\000\090\000\206\000\207\000\103\000\104\000\004\000\005\000\
\006\000\106\000\007\000\054\000\009\000\010\000\011\000\107\000\
\080\000\013\000\108\000\055\000\115\000\114\000\187\000\188\000\
\109\000\110\000\111\000\218\000\219\000\158\000\159\000\160\000\
\161\000\162\000\163\000\198\000\112\000\113\000\199\000\202\000\
\021\000\203\000\116\000\120\000\229\000\230\000\040\000\040\000\
\004\000\005\000\006\000\123\000\007\000\008\000\009\000\010\000\
\011\000\012\000\095\000\013\000\124\000\014\000\216\000\136\000\
\060\000\137\000\061\000\143\000\144\000\168\000\011\000\015\000\
\016\000\154\000\167\000\017\000\018\000\019\000\155\000\170\000\
\020\000\165\000\021\000\171\000\062\000\166\000\063\000\064\000\
\022\000\065\000\173\000\060\000\174\000\061\000\175\000\096\000\
\169\000\180\000\060\000\176\000\061\000\023\000\024\000\172\000\
\190\000\191\000\192\000\193\000\194\000\179\000\185\000\062\000\
\195\000\063\000\064\000\186\000\065\000\196\000\062\000\213\000\
\063\000\064\000\041\000\065\000\041\000\041\000\041\000\041\000\
\041\000\041\000\041\000\041\000\035\000\214\000\036\000\054\000\
\215\000\054\000\054\000\041\000\054\000\217\000\054\000\054\000\
\054\000\220\000\041\000\221\000\041\000\041\000\222\000\041\000\
\054\000\041\000\223\000\226\000\231\000\232\000\227\000\054\000\
\041\000\054\000\054\000\037\000\054\000\228\000\054\000\055\000\
\234\000\055\000\055\000\233\000\055\000\054\000\055\000\055\000\
\055\000\036\000\007\000\033\000\065\000\037\000\065\000\065\000\
\055\000\065\000\034\000\065\000\065\000\065\000\030\000\055\000\
\031\000\055\000\055\000\024\000\055\000\065\000\055\000\027\000\
\025\000\212\000\197\000\153\000\138\000\055\000\065\000\065\000\
\152\000\056\000\200\000\065\000\066\000\000\000\066\000\066\000\
\000\000\066\000\065\000\066\000\066\000\066\000\060\000\067\000\
\061\000\067\000\067\000\224\000\067\000\066\000\067\000\067\000\
\067\000\000\000\000\000\000\000\000\000\000\000\000\000\066\000\
\067\000\000\000\062\000\066\000\063\000\064\000\000\000\065\000\
\000\000\000\000\066\000\000\000\000\000\000\000\067\000\053\000\
\000\000\053\000\053\000\000\000\053\000\067\000\053\000\053\000\
\053\000\000\000\077\000\000\000\077\000\077\000\000\000\077\000\
\053\000\077\000\077\000\077\000\000\000\000\000\000\000\000\000\
\000\000\000\000\080\000\077\000\080\000\080\000\053\000\080\000\
\000\000\080\000\080\000\080\000\000\000\053\000\004\000\005\000\
\006\000\077\000\007\000\008\000\009\000\010\000\011\000\012\000\
\077\000\013\000\000\000\014\000\000\000\044\000\060\000\000\000\
\061\000\080\000\000\000\225\000\000\000\015\000\016\000\000\000\
\080\000\017\000\018\000\019\000\000\000\000\000\020\000\000\000\
\021\000\000\000\062\000\000\000\063\000\064\000\022\000\065\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\023\000\024\000\004\000\005\000\006\000\
\046\000\007\000\008\000\009\000\010\000\011\000\012\000\000\000\
\013\000\000\000\014\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\015\000\016\000\000\000\000\000\
\017\000\018\000\019\000\000\000\000\000\020\000\000\000\021\000\
\000\000\000\000\004\000\005\000\006\000\022\000\007\000\008\000\
\009\000\010\000\011\000\012\000\000\000\013\000\000\000\014\000\
\000\000\000\000\023\000\024\000\000\000\000\000\000\000\000\000\
\000\000\015\000\016\000\000\000\000\000\017\000\018\000\019\000\
\000\000\000\000\020\000\000\000\021\000\000\000\000\000\004\000\
\005\000\006\000\022\000\007\000\008\000\009\000\010\000\011\000\
\000\000\000\000\013\000\000\000\014\000\000\000\000\000\023\000\
\024\000\000\000\000\000\000\000\000\000\000\000\015\000\016\000\
\000\000\000\000\017\000\018\000\019\000\000\000\000\000\020\000\
\000\000\021\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\023\000\024\000"

let yycheck = "\040\000\
\000\000\012\001\001\000\041\000\167\000\002\000\023\001\017\001\
\018\001\019\001\000\000\012\001\015\001\000\000\025\001\014\000\
\019\001\180\000\020\000\006\001\058\000\059\000\019\000\014\001\
\062\000\063\000\064\000\065\000\014\001\001\001\002\001\003\001\
\014\001\005\001\006\001\007\001\008\001\009\001\048\001\014\001\
\012\001\016\001\014\001\040\000\046\000\000\000\014\001\042\001\
\043\001\051\000\049\000\046\001\024\001\014\001\015\001\016\001\
\055\000\003\001\000\000\034\001\006\001\060\000\061\000\035\001\
\039\001\014\001\014\001\016\001\067\000\006\001\108\000\109\000\
\014\001\034\001\112\000\036\001\037\001\017\001\039\001\019\001\
\001\000\002\000\054\001\055\001\014\001\014\001\000\000\016\001\
\016\001\086\000\000\000\088\000\089\000\031\001\032\001\027\001\
\095\000\016\001\014\001\015\001\016\001\000\000\017\001\018\001\
\014\001\034\001\016\001\036\001\107\000\106\000\039\001\050\001\
\051\001\052\001\053\001\006\001\115\000\056\001\034\001\116\000\
\036\001\037\001\006\001\039\001\034\001\124\000\036\001\037\001\
\013\001\039\001\017\001\018\001\015\001\000\000\133\000\134\000\
\050\001\051\001\052\001\053\001\003\001\022\001\056\001\019\001\
\000\000\006\001\187\000\188\000\006\001\006\001\001\001\002\001\
\003\001\015\001\005\001\006\001\007\001\008\001\009\001\018\001\
\000\000\012\001\022\001\014\001\019\001\015\001\165\000\166\000\
\022\001\022\001\022\001\209\000\210\000\042\001\043\001\044\001\
\045\001\046\001\047\001\178\000\022\001\017\001\179\000\182\000\
\035\001\184\000\015\001\018\001\226\000\227\000\187\000\188\000\
\001\001\002\001\003\001\015\001\005\001\006\001\007\001\008\001\
\009\001\010\001\011\001\012\001\019\001\014\001\205\000\017\001\
\014\001\017\001\016\001\005\001\003\001\019\001\009\001\024\001\
\025\001\017\001\015\001\028\001\029\001\030\001\049\001\019\001\
\033\001\018\001\035\001\019\001\034\001\018\001\036\001\037\001\
\041\001\039\001\022\001\014\001\022\001\016\001\019\001\048\001\
\019\001\015\001\014\001\013\001\016\001\054\001\055\001\019\001\
\168\000\169\000\170\000\171\000\172\000\026\001\017\001\034\001\
\012\001\036\001\037\001\049\001\039\001\012\001\034\001\015\001\
\036\001\037\001\010\001\039\001\012\001\013\001\014\001\015\001\
\016\001\017\001\018\001\019\001\010\001\017\001\012\001\010\001\
\017\001\012\001\013\001\027\001\015\001\005\001\017\001\018\001\
\019\001\013\001\034\001\013\001\036\001\037\001\017\001\039\001\
\027\001\041\001\019\001\046\001\005\001\019\001\044\001\034\001\
\048\001\036\001\037\001\041\001\039\001\042\001\041\001\010\001\
\005\001\012\001\013\001\045\001\015\001\048\001\017\001\018\001\
\019\001\015\001\017\001\015\001\010\001\015\001\012\001\013\001\
\027\001\015\001\015\001\017\001\018\001\019\001\013\001\034\001\
\013\001\036\001\037\001\013\001\039\001\027\001\041\001\013\001\
\013\001\196\000\175\000\124\000\105\000\048\001\036\001\037\001\
\120\000\021\000\179\000\041\001\010\001\255\255\012\001\013\001\
\255\255\015\001\048\001\017\001\018\001\019\001\014\001\010\001\
\016\001\012\001\013\001\019\001\015\001\027\001\017\001\018\001\
\019\001\255\255\255\255\255\255\255\255\255\255\255\255\037\001\
\027\001\255\255\034\001\041\001\036\001\037\001\255\255\039\001\
\255\255\255\255\048\001\255\255\255\255\255\255\041\001\010\001\
\255\255\012\001\013\001\255\255\015\001\048\001\017\001\018\001\
\019\001\255\255\010\001\255\255\012\001\013\001\255\255\015\001\
\027\001\017\001\018\001\019\001\255\255\255\255\255\255\255\255\
\255\255\255\255\010\001\027\001\012\001\013\001\041\001\015\001\
\255\255\017\001\018\001\019\001\255\255\048\001\001\001\002\001\
\003\001\041\001\005\001\006\001\007\001\008\001\009\001\010\001\
\048\001\012\001\255\255\014\001\255\255\016\001\014\001\255\255\
\016\001\041\001\255\255\019\001\255\255\024\001\025\001\255\255\
\048\001\028\001\029\001\030\001\255\255\255\255\033\001\255\255\
\035\001\255\255\034\001\255\255\036\001\037\001\041\001\039\001\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\054\001\055\001\001\001\002\001\003\001\
\004\001\005\001\006\001\007\001\008\001\009\001\010\001\255\255\
\012\001\255\255\014\001\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\024\001\025\001\255\255\255\255\
\028\001\029\001\030\001\255\255\255\255\033\001\255\255\035\001\
\255\255\255\255\001\001\002\001\003\001\041\001\005\001\006\001\
\007\001\008\001\009\001\010\001\255\255\012\001\255\255\014\001\
\255\255\255\255\054\001\055\001\255\255\255\255\255\255\255\255\
\255\255\024\001\025\001\255\255\255\255\028\001\029\001\030\001\
\255\255\255\255\033\001\255\255\035\001\255\255\255\255\001\001\
\002\001\003\001\041\001\005\001\006\001\007\001\008\001\009\001\
\255\255\255\255\012\001\255\255\014\001\255\255\255\255\054\001\
\055\001\255\255\255\255\255\255\255\255\255\255\024\001\025\001\
\255\255\255\255\028\001\029\001\030\001\255\255\255\255\033\001\
\255\255\035\001\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\054\001\055\001"

let yynames_const = "\
  UNDEFINED\000\
  NULL\000\
  FUNC\000\
  LET\000\
  DELETE\000\
  LBRACE\000\
  RBRACE\000\
  LPAREN\000\
  RPAREN\000\
  LBRACK\000\
  RBRACK\000\
  EQUALS\000\
  COMMA\000\
  DEREF\000\
  REF\000\
  COLON\000\
  COLONEQ\000\
  PRIM\000\
  IF\000\
  ELSE\000\
  SEMI\000\
  LABEL\000\
  BREAK\000\
  TRY\000\
  CATCH\000\
  FINALLY\000\
  THROW\000\
  EQEQEQUALS\000\
  TYPEOF\000\
  AMPAMP\000\
  PIPEPIPE\000\
  RETURN\000\
  BANGEQEQUALS\000\
  FUNCTION\000\
  REC\000\
  WRITABLE\000\
  GETTER\000\
  SETTER\000\
  CONFIG\000\
  VALUE\000\
  ENUM\000\
  LT\000\
  GT\000\
  PROTO\000\
  CODE\000\
  EXTENSIBLE\000\
  CLASS\000\
  EVAL\000\
  GETFIELDS\000\
  PRIMVAL\000\
  EOF\000\
  "

let yynames_block = "\
  INT\000\
  NUM\000\
  STRING\000\
  HINT\000\
  BOOL\000\
  ID\000\
  "

let yyact = [|
  (fun _ -> failwith "parser")
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : float) in
    Obj.repr(
# 92 "ljs/ljs_parser.mly"
       ( Num ((Parsing.rhs_start_pos 1, Parsing.rhs_end_pos 1), _1) )
# 549 "ljs/ljs_parser.ml"
               : 'const))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : int) in
    Obj.repr(
# 93 "ljs/ljs_parser.mly"
       (  Num ((Parsing.rhs_start_pos 1, Parsing.rhs_end_pos 1), (float_of_int _1)) )
# 556 "ljs/ljs_parser.ml"
               : 'const))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 94 "ljs/ljs_parser.mly"
          (  String ((Parsing.rhs_start_pos 1, Parsing.rhs_end_pos 1), _1) )
# 563 "ljs/ljs_parser.ml"
               : 'const))
; (fun __caml_parser_env ->
    Obj.repr(
# 95 "ljs/ljs_parser.mly"
             ( Undefined ((Parsing.rhs_start_pos 1, Parsing.rhs_end_pos 1)) )
# 569 "ljs/ljs_parser.ml"
               : 'const))
; (fun __caml_parser_env ->
    Obj.repr(
# 96 "ljs/ljs_parser.mly"
        ( Null (Parsing.rhs_start_pos 1, Parsing.rhs_end_pos 1) )
# 575 "ljs/ljs_parser.ml"
               : 'const))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : bool) in
    Obj.repr(
# 97 "ljs/ljs_parser.mly"
        ( if _1 then True (Parsing.rhs_start_pos 1, Parsing.rhs_end_pos 1) else False (Parsing.rhs_start_pos 1, Parsing.rhs_end_pos 1) )
# 582 "ljs/ljs_parser.ml"
               : 'const))
; (fun __caml_parser_env ->
    Obj.repr(
# 100 "ljs/ljs_parser.mly"
   ( d_attrs )
# 588 "ljs/ljs_parser.ml"
               : 'oattrsv))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 2 : 'exp) in
    let _5 = (Parsing.peek_val __caml_parser_env 0 : 'oattrsv) in
    Obj.repr(
# 101 "ljs/ljs_parser.mly"
                                   ( { _5 with primval = Some _3 } )
# 596 "ljs/ljs_parser.ml"
               : 'oattrsv))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 2 : bool) in
    let _5 = (Parsing.peek_val __caml_parser_env 0 : 'oattrsv) in
    Obj.repr(
# 102 "ljs/ljs_parser.mly"
                                       ( { _5 with extensible = _3 } )
# 604 "ljs/ljs_parser.ml"
               : 'oattrsv))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 2 : 'exp) in
    let _5 = (Parsing.peek_val __caml_parser_env 0 : 'oattrsv) in
    Obj.repr(
# 103 "ljs/ljs_parser.mly"
                                 ( { _5 with proto = Some _3 } )
# 612 "ljs/ljs_parser.ml"
               : 'oattrsv))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 2 : 'exp) in
    let _5 = (Parsing.peek_val __caml_parser_env 0 : 'oattrsv) in
    Obj.repr(
# 104 "ljs/ljs_parser.mly"
                                ( {_5 with code = Some _3 } )
# 620 "ljs/ljs_parser.ml"
               : 'oattrsv))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 2 : string) in
    let _5 = (Parsing.peek_val __caml_parser_env 0 : 'oattrsv) in
    Obj.repr(
# 105 "ljs/ljs_parser.mly"
                                    ( { _5 with klass = _3 } )
# 628 "ljs/ljs_parser.ml"
               : 'oattrsv))
; (fun __caml_parser_env ->
    Obj.repr(
# 108 "ljs/ljs_parser.mly"
           ( Primval )
# 634 "ljs/ljs_parser.ml"
               : 'oattr_name))
; (fun __caml_parser_env ->
    Obj.repr(
# 109 "ljs/ljs_parser.mly"
         ( Proto )
# 640 "ljs/ljs_parser.ml"
               : 'oattr_name))
; (fun __caml_parser_env ->
    Obj.repr(
# 110 "ljs/ljs_parser.mly"
        ( Code )
# 646 "ljs/ljs_parser.ml"
               : 'oattr_name))
; (fun __caml_parser_env ->
    Obj.repr(
# 111 "ljs/ljs_parser.mly"
         ( Klass )
# 652 "ljs/ljs_parser.ml"
               : 'oattr_name))
; (fun __caml_parser_env ->
    Obj.repr(
# 112 "ljs/ljs_parser.mly"
              ( Extensible )
# 658 "ljs/ljs_parser.ml"
               : 'oattr_name))
; (fun __caml_parser_env ->
    Obj.repr(
# 115 "ljs/ljs_parser.mly"
            ( Writable )
# 664 "ljs/ljs_parser.ml"
               : 'attr_name))
; (fun __caml_parser_env ->
    Obj.repr(
# 116 "ljs/ljs_parser.mly"
          ( Config )
# 670 "ljs/ljs_parser.ml"
               : 'attr_name))
; (fun __caml_parser_env ->
    Obj.repr(
# 117 "ljs/ljs_parser.mly"
         ( Value )
# 676 "ljs/ljs_parser.ml"
               : 'attr_name))
; (fun __caml_parser_env ->
    Obj.repr(
# 118 "ljs/ljs_parser.mly"
          ( Setter )
# 682 "ljs/ljs_parser.ml"
               : 'attr_name))
; (fun __caml_parser_env ->
    Obj.repr(
# 119 "ljs/ljs_parser.mly"
          ( Getter )
# 688 "ljs/ljs_parser.ml"
               : 'attr_name))
; (fun __caml_parser_env ->
    Obj.repr(
# 120 "ljs/ljs_parser.mly"
        ( Enum )
# 694 "ljs/ljs_parser.ml"
               : 'attr_name))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 3 : bool) in
    let _5 = (Parsing.peek_val __caml_parser_env 0 : 'exp) in
    Obj.repr(
# 124 "ljs/ljs_parser.mly"
     ( Data ({ value = _5; writable = _2 }, false, true) )
# 702 "ljs/ljs_parser.ml"
               : 'prop_attrs))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 3 : 'exp) in
    let _5 = (Parsing.peek_val __caml_parser_env 0 : bool) in
    Obj.repr(
# 126 "ljs/ljs_parser.mly"
     ( Data ({ value = _2; writable = _5 }, false, false) )
# 710 "ljs/ljs_parser.ml"
               : 'prop_attrs))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 6 : 'exp) in
    let _5 = (Parsing.peek_val __caml_parser_env 3 : bool) in
    let _8 = (Parsing.peek_val __caml_parser_env 0 : bool) in
    Obj.repr(
# 128 "ljs/ljs_parser.mly"
     ( Data ({ value = _2; writable = _5 }, _8, false) )
# 719 "ljs/ljs_parser.ml"
               : 'prop_attrs))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 3 : 'exp) in
    let _5 = (Parsing.peek_val __caml_parser_env 0 : 'exp) in
    Obj.repr(
# 130 "ljs/ljs_parser.mly"
     ( Accessor ({ getter = _2; setter = _5 }, false, true) )
# 727 "ljs/ljs_parser.ml"
               : 'prop_attrs))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : 'prop_attrs) in
    Obj.repr(
# 133 "ljs/ljs_parser.mly"
                                         ( (_1, _4) )
# 735 "ljs/ljs_parser.ml"
               : 'prop))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 4 : Prelude.id) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : 'prop_attrs) in
    Obj.repr(
# 134 "ljs/ljs_parser.mly"
                                     ( (_1, _4) )
# 743 "ljs/ljs_parser.ml"
               : 'prop))
; (fun __caml_parser_env ->
    Obj.repr(
# 137 "ljs/ljs_parser.mly"
   ( [] )
# 749 "ljs/ljs_parser.ml"
               : 'props))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'prop) in
    Obj.repr(
# 138 "ljs/ljs_parser.mly"
        ( [_1] )
# 756 "ljs/ljs_parser.ml"
               : 'props))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'prop) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'props) in
    Obj.repr(
# 139 "ljs/ljs_parser.mly"
                    ( _1 :: _3 )
# 764 "ljs/ljs_parser.ml"
               : 'props))
; (fun __caml_parser_env ->
    Obj.repr(
# 142 "ljs/ljs_parser.mly"
   ( [] )
# 770 "ljs/ljs_parser.ml"
               : 'exps))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'unbraced_seq_exp) in
    Obj.repr(
# 143 "ljs/ljs_parser.mly"
                    ( [_1] )
# 777 "ljs/ljs_parser.ml"
               : 'exps))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'unbraced_seq_exp) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'exps) in
    Obj.repr(
# 144 "ljs/ljs_parser.mly"
                               ( _1 :: _3 )
# 785 "ljs/ljs_parser.ml"
               : 'exps))
; (fun __caml_parser_env ->
    Obj.repr(
# 147 "ljs/ljs_parser.mly"
   ( [] )
# 791 "ljs/ljs_parser.ml"
               : 'ids))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : Prelude.id) in
    Obj.repr(
# 148 "ljs/ljs_parser.mly"
      ( [_1] )
# 798 "ljs/ljs_parser.ml"
               : 'ids))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : Prelude.id) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'ids) in
    Obj.repr(
# 149 "ljs/ljs_parser.mly"
                ( _1 :: _3 )
# 806 "ljs/ljs_parser.ml"
               : 'ids))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 2 : 'ids) in
    let _5 = (Parsing.peek_val __caml_parser_env 0 : 'braced_seq_exp) in
    Obj.repr(
# 153 "ljs/ljs_parser.mly"
   ( Lambda ((Parsing.rhs_start_pos 1, Parsing.rhs_end_pos 5), _3, _5) )
# 814 "ljs/ljs_parser.ml"
               : 'func))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'const) in
    Obj.repr(
# 156 "ljs/ljs_parser.mly"
         ( _1 )
# 821 "ljs/ljs_parser.ml"
               : 'atom))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : Prelude.id) in
    Obj.repr(
# 157 "ljs/ljs_parser.mly"
      ( Id ((Parsing.rhs_start_pos 1, Parsing.rhs_end_pos 1), _1) )
# 828 "ljs/ljs_parser.ml"
               : 'atom))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 3 : 'oattrsv) in
    let _5 = (Parsing.peek_val __caml_parser_env 1 : 'props) in
    Obj.repr(
# 159 "ljs/ljs_parser.mly"
   ( Object ((Parsing.rhs_start_pos 1, Parsing.rhs_end_pos 6), _3, _5 ))
# 836 "ljs/ljs_parser.ml"
               : 'atom))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'braced_seq_exp) in
    Obj.repr(
# 161 "ljs/ljs_parser.mly"
   ( _1 )
# 843 "ljs/ljs_parser.ml"
               : 'atom))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'unbraced_seq_exp) in
    Obj.repr(
# 162 "ljs/ljs_parser.mly"
                                  ( _2 )
# 850 "ljs/ljs_parser.ml"
               : 'atom))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'func) in
    Obj.repr(
# 163 "ljs/ljs_parser.mly"
        ( _1 )
# 857 "ljs/ljs_parser.ml"
               : 'atom))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'atom) in
    Obj.repr(
# 165 "ljs/ljs_parser.mly"
     ( Op1 ((Parsing.rhs_start_pos 1, Parsing.rhs_end_pos 2), "typeof", _2) )
# 864 "ljs/ljs_parser.ml"
               : 'atom))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'atom) in
    Obj.repr(
# 168 "ljs/ljs_parser.mly"
        ( _1 )
# 871 "ljs/ljs_parser.ml"
               : 'exp))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 3 : 'exp) in
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'exps) in
    Obj.repr(
# 170 "ljs/ljs_parser.mly"
   ( App ((Parsing.rhs_start_pos 1, Parsing.rhs_end_pos 4), _1, _3) )
# 879 "ljs/ljs_parser.ml"
               : 'exp))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'exp) in
    Obj.repr(
# 172 "ljs/ljs_parser.mly"
   ( OwnFieldNames ((Parsing.rhs_start_pos 1, Parsing.rhs_end_pos 4), _3) )
# 886 "ljs/ljs_parser.ml"
               : 'exp))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'exp) in
    Obj.repr(
# 174 "ljs/ljs_parser.mly"
     ( Eval ((Parsing.rhs_start_pos 1, Parsing.rhs_end_pos 4), _3) )
# 893 "ljs/ljs_parser.ml"
               : 'exp))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 5 : string) in
    let _5 = (Parsing.peek_val __caml_parser_env 3 : 'unbraced_seq_exp) in
    let _7 = (Parsing.peek_val __caml_parser_env 1 : 'unbraced_seq_exp) in
    Obj.repr(
# 176 "ljs/ljs_parser.mly"
   ( Op2 ((Parsing.rhs_start_pos 1, Parsing.rhs_end_pos 8), _3, _5, _7) )
# 902 "ljs/ljs_parser.ml"
               : 'exp))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 3 : string) in
    let _5 = (Parsing.peek_val __caml_parser_env 1 : 'unbraced_seq_exp) in
    Obj.repr(
# 178 "ljs/ljs_parser.mly"
   ( Op1 ((Parsing.rhs_start_pos 1, Parsing.rhs_end_pos 6), _3, _5) )
# 910 "ljs/ljs_parser.ml"
               : 'exp))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : Prelude.id) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'exp) in
    Obj.repr(
# 180 "ljs/ljs_parser.mly"
   ( SetBang ((Parsing.rhs_start_pos 1, Parsing.rhs_end_pos 3), _1, _3) )
# 918 "ljs/ljs_parser.ml"
               : 'exp))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'exp) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'exp) in
    Obj.repr(
# 182 "ljs/ljs_parser.mly"
     ( Op2 ((Parsing.rhs_start_pos 1, Parsing.rhs_end_pos 3), "stx=", _1, _3) )
# 926 "ljs/ljs_parser.ml"
               : 'exp))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'exp) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'exp) in
    Obj.repr(
# 184 "ljs/ljs_parser.mly"
     ( let p = (Parsing.rhs_start_pos 1, Parsing.rhs_end_pos 3) in
         If (p, Op2 (p, "stx=", _1, _3),
             False p, True p) )
# 936 "ljs/ljs_parser.ml"
               : 'exp))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 5 : 'exp) in
    let _3 = (Parsing.peek_val __caml_parser_env 3 : 'unbraced_seq_exp) in
    let _5 = (Parsing.peek_val __caml_parser_env 1 : 'unbraced_seq_exp) in
    Obj.repr(
# 188 "ljs/ljs_parser.mly"
   ( let p = (Parsing.rhs_start_pos 1, Parsing.rhs_end_pos 6) in
       Let (p, "$newVal", _5,
	     SetField (p, _1, _3, 
		       Id (p, "$newVal"), 
		       Object (p, d_attrs,
            [("0", Data ({ value = Id (p, "$newVal");
                          writable = true },
              true, true))])))
    )
# 953 "ljs/ljs_parser.ml"
               : 'exp))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 7 : 'exp) in
    let _3 = (Parsing.peek_val __caml_parser_env 5 : 'unbraced_seq_exp) in
    let _5 = (Parsing.peek_val __caml_parser_env 3 : 'unbraced_seq_exp) in
    let _7 = (Parsing.peek_val __caml_parser_env 1 : 'unbraced_seq_exp) in
    Obj.repr(
# 198 "ljs/ljs_parser.mly"
   ( SetField ((Parsing.rhs_start_pos 1, Parsing.rhs_end_pos 8), _1, _3, _5, _7) )
# 963 "ljs/ljs_parser.ml"
               : 'exp))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 3 : 'exp) in
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'unbraced_seq_exp) in
    Obj.repr(
# 200 "ljs/ljs_parser.mly"
   ( let p = (Parsing.rhs_start_pos 1, Parsing.rhs_end_pos 4) in
     GetField (p, _1,  _3,
		       Object (p, d_attrs,
            [])) )
# 974 "ljs/ljs_parser.ml"
               : 'exp))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 5 : 'exp) in
    let _3 = (Parsing.peek_val __caml_parser_env 3 : 'unbraced_seq_exp) in
    let _5 = (Parsing.peek_val __caml_parser_env 1 : 'unbraced_seq_exp) in
    Obj.repr(
# 205 "ljs/ljs_parser.mly"
   ( GetField ((Parsing.rhs_start_pos 1, Parsing.rhs_end_pos 6), _1, _3, _5) )
# 983 "ljs/ljs_parser.ml"
               : 'exp))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 4 : 'exp) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : 'unbraced_seq_exp) in
    Obj.repr(
# 207 "ljs/ljs_parser.mly"
     ( DeleteField ((Parsing.rhs_start_pos 1, Parsing.rhs_end_pos 5), _1, _4) )
# 991 "ljs/ljs_parser.ml"
               : 'exp))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 6 : 'exp) in
    let _3 = (Parsing.peek_val __caml_parser_env 4 : 'unbraced_seq_exp) in
    let _5 = (Parsing.peek_val __caml_parser_env 2 : 'attr_name) in
    Obj.repr(
# 209 "ljs/ljs_parser.mly"
     ( GetAttr ((Parsing.rhs_start_pos 1, Parsing.rhs_end_pos 7), _5, _1, _3) )
# 1000 "ljs/ljs_parser.ml"
               : 'exp))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 8 : 'exp) in
    let _3 = (Parsing.peek_val __caml_parser_env 6 : 'unbraced_seq_exp) in
    let _5 = (Parsing.peek_val __caml_parser_env 4 : 'attr_name) in
    let _8 = (Parsing.peek_val __caml_parser_env 1 : 'unbraced_seq_exp) in
    Obj.repr(
# 211 "ljs/ljs_parser.mly"
     ( SetAttr ((Parsing.rhs_start_pos 1, Parsing.rhs_end_pos 9), _5, _1, _3, _8) )
# 1010 "ljs/ljs_parser.ml"
               : 'exp))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 5 : 'exp) in
    let _4 = (Parsing.peek_val __caml_parser_env 2 : 'oattr_name) in
    Obj.repr(
# 213 "ljs/ljs_parser.mly"
     ( GetObjAttr((Parsing.rhs_start_pos 1, Parsing.rhs_end_pos 6),
                  _4, _1) )
# 1019 "ljs/ljs_parser.ml"
               : 'exp))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 7 : 'exp) in
    let _4 = (Parsing.peek_val __caml_parser_env 4 : 'oattr_name) in
    let _7 = (Parsing.peek_val __caml_parser_env 1 : 'unbraced_seq_exp) in
    Obj.repr(
# 216 "ljs/ljs_parser.mly"
     ( SetObjAttr((Parsing.rhs_start_pos 1, Parsing.rhs_end_pos 8),
                  _4, _1, _7) )
# 1029 "ljs/ljs_parser.ml"
               : 'exp))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'exp) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'exp) in
    Obj.repr(
# 219 "ljs/ljs_parser.mly"
     ( If ((Parsing.rhs_start_pos 1, Parsing.rhs_end_pos 3), _1, 
            _3, False (Parsing.rhs_start_pos 1, Parsing.rhs_end_pos 3)) )
# 1038 "ljs/ljs_parser.ml"
               : 'exp))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'exp) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'exp) in
    Obj.repr(
# 222 "ljs/ljs_parser.mly"
     ( let p = (Parsing.rhs_start_pos 1, Parsing.rhs_end_pos 3) in
         Let (p, "%or", _1,
               If (p, Id (p, "%or"), Id (p, "%or"), _3)) )
# 1048 "ljs/ljs_parser.ml"
               : 'exp))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'exp) in
    Obj.repr(
# 228 "ljs/ljs_parser.mly"
       ( _1 )
# 1055 "ljs/ljs_parser.ml"
               : 'cexp))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'ifexp) in
    Obj.repr(
# 229 "ljs/ljs_parser.mly"
         ( _1 )
# 1062 "ljs/ljs_parser.ml"
               : 'cexp))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 2 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'cexp) in
    Obj.repr(
# 231 "ljs/ljs_parser.mly"
     ( Hint ((Parsing.rhs_start_pos 1, Parsing.rhs_end_pos 4), _2, _3) )
# 1070 "ljs/ljs_parser.ml"
               : 'cexp))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 2 : Prelude.id) in
    let _4 = (Parsing.peek_val __caml_parser_env 0 : 'braced_seq_exp) in
    Obj.repr(
# 233 "ljs/ljs_parser.mly"
     ( Label ((Parsing.rhs_start_pos 1, Parsing.rhs_end_pos 4), _2, _4) )
# 1078 "ljs/ljs_parser.ml"
               : 'cexp))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : Prelude.id) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'cexp) in
    Obj.repr(
# 235 "ljs/ljs_parser.mly"
   ( Break ((Parsing.rhs_start_pos 1, Parsing.rhs_end_pos 3), _2, _3) )
# 1086 "ljs/ljs_parser.ml"
               : 'cexp))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'cexp) in
    Obj.repr(
# 237 "ljs/ljs_parser.mly"
   ( Throw ((Parsing.rhs_start_pos 1, Parsing.rhs_end_pos 2), _2) )
# 1093 "ljs/ljs_parser.ml"
               : 'cexp))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 2 : 'braced_seq_exp) in
    let _4 = (Parsing.peek_val __caml_parser_env 0 : 'braced_seq_exp) in
    Obj.repr(
# 239 "ljs/ljs_parser.mly"
   ( TryCatch ((Parsing.rhs_start_pos 1, Parsing.rhs_end_pos 4), _2, _4) )
# 1101 "ljs/ljs_parser.ml"
               : 'cexp))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 2 : 'braced_seq_exp) in
    let _4 = (Parsing.peek_val __caml_parser_env 0 : 'braced_seq_exp) in
    Obj.repr(
# 241 "ljs/ljs_parser.mly"
   ( TryFinally ((Parsing.rhs_start_pos 1, Parsing.rhs_end_pos 4), _2, _4) )
# 1109 "ljs/ljs_parser.ml"
               : 'cexp))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 4 : 'unbraced_seq_exp) in
    let _5 = (Parsing.peek_val __caml_parser_env 2 : 'braced_seq_exp) in
    let _7 = (Parsing.peek_val __caml_parser_env 0 : 'ifexp) in
    Obj.repr(
# 245 "ljs/ljs_parser.mly"
     ( If ((Parsing.rhs_start_pos 1, Parsing.rhs_end_pos 7), _3, _5, _7) )
# 1118 "ljs/ljs_parser.ml"
               : 'ifexp))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 4 : 'unbraced_seq_exp) in
    let _5 = (Parsing.peek_val __caml_parser_env 2 : 'braced_seq_exp) in
    let _7 = (Parsing.peek_val __caml_parser_env 0 : 'braced_seq_exp) in
    Obj.repr(
# 247 "ljs/ljs_parser.mly"
     ( If ((Parsing.rhs_start_pos 1, Parsing.rhs_end_pos 7), _3, _5, _7) )
# 1127 "ljs/ljs_parser.ml"
               : 'ifexp))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 2 : 'unbraced_seq_exp) in
    let _5 = (Parsing.peek_val __caml_parser_env 0 : 'braced_seq_exp) in
    Obj.repr(
# 249 "ljs/ljs_parser.mly"
     ( If ((Parsing.rhs_start_pos 1, Parsing.rhs_end_pos 5), _3, _5, 
	    Undefined (Parsing.rhs_start_pos 1, Parsing.rhs_end_pos 5)) )
# 1136 "ljs/ljs_parser.ml"
               : 'ifexp))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'unbraced_seq_exp) in
    Obj.repr(
# 253 "ljs/ljs_parser.mly"
                                  ( with_pos _2 (Parsing.rhs_start_pos 1, Parsing.rhs_end_pos 3) )
# 1143 "ljs/ljs_parser.ml"
               : 'braced_seq_exp))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'unbraced_seq_item) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'unbraced_seq_exp) in
    Obj.repr(
# 256 "ljs/ljs_parser.mly"
                                           ( Seq ((Parsing.rhs_start_pos 1, Parsing.rhs_end_pos 3), _1, _3) )
# 1151 "ljs/ljs_parser.ml"
               : 'unbraced_seq_exp))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'unbraced_seq_item) in
    Obj.repr(
# 257 "ljs/ljs_parser.mly"
                     ( _1 )
# 1158 "ljs/ljs_parser.ml"
               : 'unbraced_seq_exp))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'cexp) in
    Obj.repr(
# 260 "ljs/ljs_parser.mly"
        ( _1 )
# 1165 "ljs/ljs_parser.ml"
               : 'unbraced_seq_item))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 4 : Prelude.id) in
    let _5 = (Parsing.peek_val __caml_parser_env 2 : 'unbraced_seq_exp) in
    let _7 = (Parsing.peek_val __caml_parser_env 0 : 'unbraced_seq_item) in
    Obj.repr(
# 262 "ljs/ljs_parser.mly"
   ( Let ((Parsing.rhs_start_pos 1, Parsing.rhs_end_pos 7), _3, _5, _7) )
# 1174 "ljs/ljs_parser.ml"
               : 'unbraced_seq_item))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 4 : Prelude.id) in
    let _5 = (Parsing.peek_val __caml_parser_env 2 : 'func) in
    let _7 = (Parsing.peek_val __caml_parser_env 0 : 'unbraced_seq_item) in
    Obj.repr(
# 264 "ljs/ljs_parser.mly"
   ( Rec ((Parsing.rhs_start_pos 1, Parsing.rhs_end_pos 7), _3, _5, _7) )
# 1183 "ljs/ljs_parser.ml"
               : 'unbraced_seq_item))
; (fun __caml_parser_env ->
    Obj.repr(
# 268 "ljs/ljs_parser.mly"
     ( fun x -> x )
# 1189 "ljs/ljs_parser.ml"
               : Ljs_syntax.exp -> Ljs_syntax.exp))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 4 : Prelude.id) in
    let _6 = (Parsing.peek_val __caml_parser_env 1 : 'unbraced_seq_exp) in
    let _7 = (Parsing.peek_val __caml_parser_env 0 : Ljs_syntax.exp -> Ljs_syntax.exp) in
    Obj.repr(
# 270 "ljs/ljs_parser.mly"
     ( let p = (Parsing.rhs_start_pos 1, Parsing.rhs_end_pos 7) in
         fun x -> 
           Let (p, _3, _6, _7 x) )
# 1200 "ljs/ljs_parser.ml"
               : Ljs_syntax.exp -> Ljs_syntax.exp))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 4 : Prelude.id) in
    let _6 = (Parsing.peek_val __caml_parser_env 1 : 'unbraced_seq_exp) in
    let _7 = (Parsing.peek_val __caml_parser_env 0 : Ljs_syntax.exp -> Ljs_syntax.exp) in
    Obj.repr(
# 274 "ljs/ljs_parser.mly"
     ( let p = (Parsing.rhs_start_pos 1, Parsing.rhs_end_pos 7) in
         fun x -> 
           Rec (p, _3, _6, _7 x) )
# 1211 "ljs/ljs_parser.ml"
               : Ljs_syntax.exp -> Ljs_syntax.exp))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'braced_seq_exp) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : Ljs_syntax.exp -> Ljs_syntax.exp) in
    Obj.repr(
# 278 "ljs/ljs_parser.mly"
     ( let p = (Parsing.rhs_start_pos 1, Parsing.rhs_end_pos 2) in
         fun x -> Seq (p, _1, _2 x) )
# 1220 "ljs/ljs_parser.ml"
               : Ljs_syntax.exp -> Ljs_syntax.exp))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'unbraced_seq_exp) in
    Obj.repr(
# 282 "ljs/ljs_parser.mly"
                        ( _1 )
# 1227 "ljs/ljs_parser.ml"
               : Ljs_syntax.exp))
(* Entry prog *)
; (fun __caml_parser_env -> raise (Parsing.YYexit (Parsing.peek_val __caml_parser_env 0)))
(* Entry env *)
; (fun __caml_parser_env -> raise (Parsing.YYexit (Parsing.peek_val __caml_parser_env 0)))
|]
let yytables =
  { Parsing.actions=yyact;
    Parsing.transl_const=yytransl_const;
    Parsing.transl_block=yytransl_block;
    Parsing.lhs=yylhs;
    Parsing.len=yylen;
    Parsing.defred=yydefred;
    Parsing.dgoto=yydgoto;
    Parsing.sindex=yysindex;
    Parsing.rindex=yyrindex;
    Parsing.gindex=yygindex;
    Parsing.tablesize=yytablesize;
    Parsing.table=yytable;
    Parsing.check=yycheck;
    Parsing.error_function=parse_error;
    Parsing.names_const=yynames_const;
    Parsing.names_block=yynames_block }
let prog (lexfun : Lexing.lexbuf -> token) (lexbuf : Lexing.lexbuf) =
   (Parsing.yyparse yytables 1 lexfun lexbuf : Ljs_syntax.exp)
let env (lexfun : Lexing.lexbuf -> token) (lexbuf : Lexing.lexbuf) =
   (Parsing.yyparse yytables 2 lexfun lexbuf : Ljs_syntax.exp -> Ljs_syntax.exp)
;;
# 283 "ljs/ljs_parser.mly"

# 1258 "ljs/ljs_parser.ml"
