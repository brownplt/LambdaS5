open Prelude
open Ljs_delta
module S = Ljs_syntax
module V = Ljs_values

exception ExpValError of string

let exp_to_value (e : S.exp) : V.value = 
  match e with 
  | S.Null _ -> V.Null
  | S.Undefined _ -> V.Null
  | S.Num (_, n) -> V.Num n
  | S.String (_, s) -> V.String s
  | S.True _ -> V.True
  | S.False _ -> V.False
  | _ -> raise (ExpValError "exp->value error")


let value_to_exp (v : V.value) (p : Pos.t) : S.exp =
  match v with
  | V.Null -> S.Null p
  | V.Undefined -> S.Undefined p
  | V.Num n -> S.Num (p, n)
  | V.String s -> S.String (p, s)
  | V.True -> S.True p
  | V.False -> S.False p
  | _ -> raise (ExpValError "value->exp error")

let dummy_store = (Store.empty, Store.empty)

let apply_op1 p op e : S.exp option =
  try 
    let v = exp_to_value e in
    let op = op1 dummy_store op in
    let result = op v in
    Some (value_to_exp result p)
  with _ -> None
                          
let apply_op2 p op e1 e2 : S.exp option =
  try
    let v1 = exp_to_value e1 in
    let v2 = exp_to_value e2 in
    let op = op2 dummy_store op in
    let result = op v1 v2 in
    Some (value_to_exp result p)
  with _ -> None
