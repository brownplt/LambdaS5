open Prelude
open Ljs_syntax
open Lexing
module OU = OUnit2

(* parse a string to produce ljs *)
let parse str =
  let lexbuf = Lexing.from_string str in
  try
    lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with pos_fname = "stdin" };
    Ljs_parser.prog Ljs_lexer.token lexbuf
  with
  |  Failure "lexing: empty token" ->
      failwith (sprintf "lexical error at %s"
                        (Pos.string_of_pos (Pos.real
                                              (lexbuf.lex_curr_p, lexbuf.lex_curr_p))))
  | Failure "utf8_of_point not implemented" ->
     failwith "Parser doesn't do some UTF8 encoding crap"
  | _ ->
     failwith (sprintf "parse error at %s; unexpected token %s in '%s'"
                       (Pos.string_of_pos (Pos.real
                                             (lexbuf.lex_curr_p, lexbuf.lex_curr_p)))
                       (lexeme lexbuf)
                       str)

let ljs_str ljs =
  Ljs_pretty.exp ljs Format.str_formatter; Format.flush_str_formatter()

let rec equal_exp (e1 : exp) (e2 : exp) =
  let equal_exp_option e1 e2 =
    match e1, e2 with
    | Some (e1), Some (e2) -> equal_exp e1 e2
    | None, None -> true
    | _ -> false
  in
  let equal_exp_attr attr1 attr2 =
    let {primval=a1; code=b1; proto=c1; klass=d1; extensible=e1} = attr1 in 
    let{primval=a2; code=b2; proto=c2; klass=d2; extensible=e2} = attr2 in
    equal_exp_option a1 a2 && equal_exp_option b1 b2 && equal_exp_option c1 c2 &&
      d1 = d2 && e1 = e2
  in
  match e1, e2 with
  | Null _, Null _ 
  | Undefined _, Undefined _
  | True _, True _
  | False _, False _ -> true
  | String (_, s1), String (_, s2) -> s1 = s2
  | Id (_, id1), Id (_, id2) -> id1 = id2
  | Num (_, n1), Num(_, n2) -> n1 = n2
  | Let (_, x1, xexp1, body1), Let (_, x2, xexp2, body2) ->
     x1 = x2 && equal_exp xexp1 xexp2 && equal_exp body1 body2
  | Rec (_, x1, xexp1, body1), Rec (_, x2, xexp2, body2) ->
     x1 = x2 && equal_exp xexp1 xexp2 && equal_exp body1 body2

  | Seq (_, e1, e2), Seq (_, e3, e4) -> equal_exp e1 e3 && equal_exp e2 e4
  | Object (_, attrs1, strprop1), Object (_, attrs2, strprop2) ->
     let cmp_prop strprop1 strprop2 : bool = 
       match strprop1, strprop2 with
       | (s1, Data({value=val1; writable=w1}, enum1, config1)), 
         (s2, Data({value=val2; writable=w2}, enum2, config2)) ->
          s1 = s2 && equal_exp val1 val2 && w1 = w2 && enum1 = enum2 && config1 = config2 
       | (str1, Accessor({getter=g1; setter=s1}, enum1, config1)), 
         (str2, Accessor({getter=g2; setter=s2}, enum2, config2)) ->
          str1 = str2 && equal_exp g1 g2 && equal_exp s1 s2 && enum1 = enum2 && config1 = config2 
       | _ -> false
     in
     if not (equal_exp_attr attrs1 attrs2) then false
     else begin
       try List.for_all2 cmp_prop strprop1 strprop2
       with _ -> false
       end
  | GetAttr (_, pattr1, obj1, field1), GetAttr (_, pattr2, obj2, field2) ->
     pattr1 = pattr2 && equal_exp obj1 obj2 && equal_exp field1 field2
  | SetAttr (_, attr1, obj1, field1, newval1), SetAttr (_, attr2, obj2, field2, newval2) ->
     attr1 = attr2 && equal_exp obj1 obj2 && equal_exp field1 field2 && equal_exp newval1 newval2
  | GetObjAttr (_, a1, obj1), GetObjAttr(_, a2, obj2) ->
     a1 = a2 && equal_exp obj1 obj2
  | SetObjAttr (_, a1, obj1, arg1), SetObjAttr(_, a2, obj2, arg2) ->
     a1 = a2 && equal_exp obj1 obj2 && equal_exp arg1 arg2
  | SetField (_, o1, f1, v1, arg1), SetField (_, o2, f2, v2, arg2) ->
     equal_exp o1 o2 && equal_exp f1 f2 && equal_exp v1 v2 && equal_exp arg1 arg2 
  | GetField (_, o1, f1, v1), GetField (_, o2, f2, v2) ->
     equal_exp o1 o2 && equal_exp f1 f2 && equal_exp v1 v2 
  | DeleteField (_, o1, f1), DeleteField(_, o2, f2) ->
     equal_exp o1 o2 && equal_exp f1 f2
  | OwnFieldNames (_, o1), OwnFieldNames (_, o2) ->
     equal_exp o1 o2
  | SetBang (_, x1, e1), SetBang (_, x2, e2) ->
     x1 = x2 && equal_exp e1 e2
  | Op1 (_, op1, e1), Op1 (_, op2, e2) -> 
     op1 = op2 && equal_exp e1 e2
  | Op2 (_, op1, e1, e2), Op2(_, op2, e3, e4) -> 
     op1 = op2 && equal_exp e1 e3 && equal_exp e2 e4
  | If (_, c1, t1, e1), If (_, c2, t2, e2) -> 
     equal_exp c1 c2 && equal_exp t1 t2 && equal_exp e1 e2
  | App (_, f1, arg1), App (_, f2, arg2) -> 
     equal_exp f1 f2 && List.for_all2 equal_exp arg1 arg2
  | Label (_, l1, e1), Label (_, l2, e2) ->
     l1 = l2 && equal_exp e1 e2
  | Break (_, i1, e1), Break (_, i2, e2) ->
     i1 = i2 && equal_exp e1 e2
  | TryCatch (_, b1, c1), TryCatch (_, b2, c2) ->
     equal_exp b1 b2 && equal_exp c1 c2
  | TryFinally (_, b1, f1), TryFinally (_, b2, f2) ->
     equal_exp b1 b2 && equal_exp f1 f2
  | Throw (_, e1), Throw(_, e2) ->
     equal_exp e1 e2
  | Lambda (_, xs1, e1), Lambda (_, xs2, e2) ->
     xs1 = xs2 && equal_exp e1 e2
  | Hint (_, x1, e1), Hint(_, x2, e2) ->
     x1 = x2 && equal_exp e1 e2
  | _ ->  false (*failwith "not implemented"*)

let rec count (e : exp) : int =
  match e with
  | _ -> 1 + (List.fold_left (+) 0 (List.map count (child_exps e)))

(* tips: do everything in function test instead of in cmp *)
let cmp (before : string) (func : exp->exp) (after : string) = 
  let test test_ctx =
    let dest = parse after in
    let opted = func (parse before) in 
    OU.assert_equal 
      ~printer:ljs_str
      ~cmp:equal_exp
      dest opted
  in
  test

let no_change (code : string) (func : exp->exp) =
  cmp code func code
