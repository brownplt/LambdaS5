open Prelude
open Ljs_syntax
open Ljs_opt
open Ljs_alpha_rename
module EU = Exp_util

type env = exp IdMap.t


(* given a set of ids, check whether the exp has modified one of them *)
let rec no_def_of_para (ids : IdSet.t) (exp : exp) =
  if IdSet.is_empty ids then true
  else 
    begin match exp with
      | SetBang(_, x, _) when IdSet.mem x ids -> false
      | Let (_, x, x_v, body) ->
        let new_ids = IdSet.diff ids (IdSet.singleton x) in
        no_def_of_para ids x_v && no_def_of_para new_ids body
      | Rec (_, x, x_v, body) ->
        let new_ids = IdSet.diff ids (IdSet.singleton x) in
        (* slightly different with let *)
        no_def_of_para new_ids x_v && no_def_of_para new_ids body
      | Lambda (_, xs, body) ->
          let new_ids = IdSet.diff ids (IdSet.from_list xs) in
          no_def_of_para new_ids body
      | exp ->
        List.for_all (fun e -> no_def_of_para ids e) (child_exps exp)
    end

(* an inlinable lambda whose formal parameters are not assigned in the
   body *)
let is_inlinable_lambda (e : exp) : bool =
  match e with
  | Lambda (_, ids, body) ->
    no_def_of_para (IdSet.from_list ids) body
  | _ -> false


let is_prim_constant (e : exp) : bool = match e with
  | Null _
  | Undefined _
  | Num (_, _)
  | String (_, _)
  | True _
  | False _ -> true
  | _ -> false

(* given a list of expressions, check whether all of them are either an
   id or a primitive constant value. If so, it is an inlinable argument list.
*)
let rec are_inlinable_arguments (e : exp list) : bool =
  let rec is_inlinable_argument exp =
    EU.is_Id exp || is_prim_constant exp
  in
  match e with
  | [] -> true
  | hd :: tl ->
    if is_inlinable_argument hd then
      are_inlinable_arguments tl
    else
      false

let rec get_lambda e : exp option = match e with
  | Lambda (_,_,_) when is_inlinable_lambda e-> Some e
  | _ -> None
  

(*
  inline a function when
   1. the function has been propagated to the call site
   2. the function is inlinable
   3. function application's argument are constants or `id`.
 *)
let rec inline_function (e : exp) : exp =
  let empty_env = IdMap.empty in
  let rec inlining_rec e env =
    match e with
    | App (p, func, args) ->
       let func = inlining_rec func env in
       let args = List.map (fun x->inlining_rec x env) args in
       let f = get_lambda func in
       begin
         match f, are_inlinable_arguments args with
         (*| Some (e), false -> printf "\nget one:"; 
             printf "%s" (ljs_str e); 
             printf "\nargs: "; 
             List.iter (fun(x)->printf "%s," (ljs_str x)) args; App (p, func, args)*)
         | Some (e), true -> inline_lambda p e args
         | _ -> App (p, func, args)
       end 
    | Undefined _
    | Null _ 
    | String (_, _) 
    | Num (_, _) 
    | True _
    | Id (_, _)        
    | False _ -> e
    | Let (_, _, _, _)
    | Rec (_, _, _, _)
    | Object (_, _, _) 
    | GetAttr (_, _, _, _) 
    | SetAttr (_, _, _, _, _)
    | GetObjAttr (_, _, _) 
    | SetObjAttr (_, _, _, _) 
    | GetField (_, _, _, _) 
    | SetField (_, _, _, _, _)
    | DeleteField (_, _, _) 
    | OwnFieldNames (_, _) 
    | Op1 (_, _, _) 
    | Op2 (_, _, _, _) 
    | If (_, _, _, _) 
    | SetBang(_,_,_)
    | Lambda (_, _, _)
    | Seq (_,_,_)
    | Label (_,_,_)
    | Break (_,_,_)
    | TryCatch (_,_,_)
    | TryFinally (_,_,_)
    | Throw (_,_)
    | Hint(_,_,_)
    | Eval(_,_,_)
      -> optimize (fun x->inlining_rec x env) e
  in 
  inlining_rec e empty_env

and inline_lambda p (f : exp) (args : exp list) : exp = 
  let rec build_env keys vals env = match keys, vals with
    | [], [] -> Some env
    | k :: rst_k, v :: rst_v ->
       build_env rst_k rst_v (IdMap.add k v env)
    | _ -> None
  in
  let rec subst_rec e env = 
    let subst e = subst_rec e env in
    match e with
    | Id (_, id) -> 
       begin
         try IdMap.find id env 
         with _ -> e
       end 
    | Lambda (p, xs, body) when List.exists (fun x-> IdMap.mem x env) xs ->
      (* current expression has been alpha renamed, it is impossible
         to be rebound again. *)
      failwith "[Lambda]This should not happen, body has been alpha renamed"
    | SetBang (_,x,_) when IdMap.mem x env ->
      failwith "[SetBang]This should not happen, body has been alpha renamed"
    | Let (_, x, _, _) when IdMap.mem x env ->
      failwith "[Let]This should not happen, body has been alpha renamed"
    | Rec (_, x, _, _) when IdMap.mem x env ->
      failwith "[Rec]This should not happen, body has been alpha renamed"
        
    | _ -> optimize subst e in
  match f with 
  | Lambda (_, xs, _) when (List.length args) = (List.length xs) ->
    (* inline it only when #parameter and #argument agree *)
    (* 1. get the potential conflict ids in args, make them a set *)
    let namespace = IdSet.from_list
        (List.map (fun e->match e with
             | Id (_, id) -> id
             | _ -> failwith "unreachable")
            (List.filter (fun e->EU.is_Id e) args))
    in
    (* alpha rename the body *)
    let new_lambda = alpha_rename f namespace in
    begin match new_lambda with
      | Lambda (p, newxs, newbody) ->
        let env_option = build_env newxs args IdMap.empty in
        begin
          match env_option with
          | Some (env) -> subst_rec newbody env
          | None -> App (p, f, args)
        end
      | _ -> failwith "unreachable"
    end
  | _ -> App (p, f, args)

