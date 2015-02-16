open Prelude
open Ljs_syntax
open Ljs_opt
module EU = Exp_util

type env = exp IdMap.t

let pretty_env env =
  IdMap.iter (fun k v ->
      printf "%s -> %s\n" k (EU.ljs_str v)) env

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
    | GetField (_, o, String(_, "prototype"), _) ->
      (* function always has an object as prototype *)
      if typeof o env = "function" then "object"
      else failwith (sprintf "cannot decide: %s\n" (EU.ljs_str exp))
    | _ -> failwith (sprintf "Not Support: %s\n" (EU.ljs_str exp))
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
  
(* this function is mainly for cleaning
    1. "prim("typeof", obj)"
    2. IsObject
    3. PropAccessorCheck
    4. ToObject
*)
let infer_types (exp : exp) : exp =
  let rec infer_rec (exp : exp) (env : env) : exp =
    let infer e = infer_rec e env in
    match exp with
    | Op1 (p, op, arg) ->
      let arg = infer_rec arg env in
      op1 p op arg env
    | Let (p, x, x_v, body) ->
      let x_v = infer_rec x_v env in
      if (EU.same_Id x x_v) then
        infer_rec body env
      else if (EU.mutate_var x body) then
        let env = IdMap.remove x env in
        Let (p, x, x_v, infer_rec body env)
      else
        let env = IdMap.add x x_v env in
        Let (p, x, x_v, infer_rec body env)
    | Lambda (p, xs, body) ->
      let env = IdMap.filter (fun k _->not (List.mem k xs)) env in
      let body = infer_rec body env in
      Lambda (p, xs, body)
    | App (p, f, args) ->
      let f = infer_rec f env in
      let args = List.map infer args in
      begin match f, args with
      | Id (_, "%ToObject"), [e] ->
        begin match get_type e env with
          | Some (String (_, "function"))
          | Some (String (_, "object")) -> e
          | _ -> App (p, f, args)
        end 
      | Id (_, "%IsObject"), [e] ->
        begin match get_type e env with
          | Some (String (_, "function"))
          | Some (String (_, "object")) -> True Pos.dummy
          | Some (_) -> False Pos.dummy
          | None -> App (p, f, args)
        end 
      | Id (p0, "%PropAccessorCheck"), [e] ->
        begin match get_type e env with
          | Some (String (_, "Undefined")) -> App(p, f, args)
          | Some (_) -> (* make it a ToObject expression *)
            let new_app = App (p, Id(p0, "%ToObject"), [e]) in
            infer_rec new_app env
          | None -> App (p, f, args)
        end
      | _ -> App (p, f, args)
      end 
    | If (p, tst, thn, els) ->
      let tst = infer_rec tst env in
      begin match tst with
        | True _ -> infer_rec thn env 
        | False _ -> infer_rec els env
        | _ ->
          If (p, tst, infer_rec thn env, infer_rec els env)
      end
    | _ -> optimize infer exp
  in
  infer_rec exp IdMap.empty
