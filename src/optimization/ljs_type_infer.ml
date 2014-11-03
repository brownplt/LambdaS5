open Prelude
open Ljs_syntax
open Ljs_opt
module EU = Exp_util

type env = exp IdMap.t

(* get_type will return Some (String(_,_)) or None *)
let rec get_type exp env : exp option = 
  let rec typeof exp env =
    match exp with
    | Null _ -> "null"
    | Undefined _ -> "undefined"
    | String (_, _) -> "string"
    | Num (_, _) -> "number"
    | True _ | False _ -> "boolean"
    | Object (_,attr,_) -> begin match attr with
      | { code = Some _ } -> "function"
      | _ -> "object"
      end 
    | Id (_, x) ->
      typeof (IdMap.find x env) env
    | Let (_, x, x_v, body) ->
      let env = IdMap.add x x_v env in
      typeof body env
    | Rec (_, x, x_v, body) ->
      let env = IdMap.add x x_v env in
      typeof body env
    | Seq (_, e1, e2) -> typeof e2 env
    | _ -> failwith "Not Support"
  in 
  try
    Some (String (Pos.dummy, typeof exp env))
  with _ -> None
    
  
let op1 p op arg env : exp = match op with
  | "typeof" ->
    begin match get_type arg env with
    | Some e -> e
    | None -> Op1 (p, op, arg)
    end 
  | _ -> Op1 (p, op, arg)
  
(* this function is mainly for cleaning "prim("typeof", obj)" *)
let type_infer (exp : exp) : exp =
  let rec clean_rec (exp : exp) (env : env) : exp =
    let clean e = clean_rec e env in
    match exp with
    | Op1 (p, op, arg) ->
      let arg = clean_rec arg env in
      op1 p op arg env
    | Let (p, x, x_v, body) ->
      let x_v = clean_rec x_v env in
      if (EU.mutate_var x body) then
        let env = IdMap.remove x env in
        Let (p, x, x_v, clean_rec body env)
      else
        let env = IdMap.add x x_v env in
        let body = clean_rec body env in
        Let (p, x, x_v, body)
    | Lambda (p, xs, body) ->
      let env = IdMap.filter (fun k _->not (List.mem k xs)) env in
      let body = clean_rec body env in
      Lambda (p, xs, body)
    | App (p, f, args) ->
      let f = clean_rec f env in
      begin match f, args with
      | Id (_, "%ToObject"), [Id (p1, id)] ->
        begin match get_type (Id (p1, id)) env with
          | Some (String (_, "function"))
          | Some (String (_, "object")) -> Id (p1, id)
          | _ -> App (p, f, args)
        end 
      | _ -> App (p, f, args)
      end 
    | _ -> optimize clean exp
  in
  clean_rec exp IdMap.empty
