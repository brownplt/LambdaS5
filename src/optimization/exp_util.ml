open Prelude
open Ljs_delta
open Ljs_opt
module S = Ljs_syntax
module V = Ljs_values

exception ExpValError of string
type pool = (S.exp * bool * bool) IdMap.t

let print_ljs ljs =
  Ljs_pretty.exp ljs Format.std_formatter; print_newline()

let ljs_str ljs =
  Ljs_pretty.exp ljs Format.str_formatter; Format.flush_str_formatter()

let exp_to_value (e : S.exp) : V.value = 
  match e with 
  | S.Null _ -> V.Null
  | S.Undefined _ -> V.Undefined
  | S.Num (_, n) -> V.Num n
  | S.String (_, s) -> V.String s
  | S.True _ -> V.True
  | S.False _ -> V.False
  | _ -> raise (ExpValError "exp->value error")

let is_ctx_obj (e : S.exp) : bool = match e with
  | S.Id (_, id) ->
    id = "%global" || id = "%globalContext" ||
    id = "%strictContext" || id = "nonstrictContext" ||
    id = "%context"
  | _ -> false
    

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

let op_has_side_effect (op : string) : bool = match op with
  | "print"
  | "pretty"
  | "current-utc-millis" -> true
  | _ -> false 

(*
 * this function will check whether exp `e' has side effect *when it is evaluated*.
 * NOTE(junsong): The subtle point is
 * let (x = func(){ y:=1} ) {x} does not have side effect
 * let (x = func(){ y:=1} ) {x()} has side effect.
 *
 * env contains id that does not have side effect.
 *)
let rec has_side_effect ?(env=IdSet.empty) (e : S.exp) : bool = match e with
  | S.Null _
  | S.Undefined _
  | S.String (_,_)
  | S.Num (_,_)
  | S.True _
  | S.False _
  | S.Id (_,_) 
  | S.Lambda (_, _, _) -> (* lambda always has no side effect *)
    false
  | S.GetAttr (_, _,obj, flds) ->
     has_side_effect ~env obj || has_side_effect ~env flds
  | S.GetObjAttr (_, _, obj) ->
     has_side_effect ~env obj
  | S.OwnFieldNames (_, obj) ->
     has_side_effect ~env obj
  | S.Op2 (_,_,e1,e2) ->
     has_side_effect ~env e1 || has_side_effect ~env e2
  | S.Op1 (_,op,e1) ->
     op_has_side_effect op || has_side_effect ~env e1
  | S.Object (_,_,_) ->
     List.exists (fun (e)->has_side_effect ~env e) (S.child_exps e)
  | S.If (_, cond, thn, els) ->
     List.exists (fun(e)->has_side_effect ~env e) [cond; thn; els]
  | S.Seq (_, e1, e2) ->
     has_side_effect ~env e1|| has_side_effect ~env e2
  | S.Let (_, x, x_v, body) ->
     begin
       match x_v with 
       | S.Lambda (_, xs, lmd_body) -> (* check the body of lambda and return false*)
          let newset = IdSet.filter (fun(x)->not (List.mem x xs)) env in
          let se_lambda = has_side_effect ~env:newset lmd_body in
          let newenv = match se_lambda with 
            | true -> IdSet.remove x env 
            | false -> IdSet.add x env
          in 
          has_side_effect ~env:newenv body
       | _ -> 
          let xv_se = has_side_effect ~env x_v in (* x has new se status *)
          if xv_se then xv_se
          else 
            let newenv = IdSet.remove x env in
            has_side_effect ~env:newenv body
     end 
  | S.Rec (_, x, x_v, body) ->
     (* assume x has no side effect *)
     let env = IdSet.add x env in
     begin
     match x_v with 
     | S.Lambda (_, xs, lmd_body) ->
        let env = IdSet.filter (fun(x)->not (List.mem x xs)) env in
        let se_lambda = has_side_effect ~env:env lmd_body in
        let env = match se_lambda with
          | true -> IdSet.remove x env
          | false -> IdSet.add x env
        in 
        has_side_effect ~env:env body
     | _ -> failwith (sprintf "optimizer gets syntax error: rec (%s=%s)" x (ljs_str x_v))
     end 
  | S.App (_, f, args) ->          (* check if f(x) has side effect *)
     let se_f =  match f with
     | S.Id(_, id) -> 
        not (IdSet.mem id env)
     | S.Lambda (_, xs, lmd_body) -> 
        let env = IdSet.filter (fun(x)->not(List.mem x xs)) env in
        has_side_effect ~env lmd_body
     | S.App (_,_,_) -> 
       (*NOTE(junsong): I don't know what to do with this situation
                        f(){f(){print}}()()
       *)
       true 
     | _ ->
        has_side_effect ~env f
     in
     se_f || List.exists (fun(arg)->has_side_effect ~env arg) args
  | S.Label (_, _, e) -> has_side_effect ~env e
  | S.Break (_, _, _)
  | S.SetAttr (_,_,_,_,_)
  | S.SetObjAttr (_,_,_,_)
  | S.GetField (_,_,_,_)
  | S.SetField (_,_,_,_,_)
  | S.DeleteField (_,_,_)
  | S.SetBang (_,_,_) 
  | S.TryCatch (_, _, _)    (* any try..catch is assumed to throw out uncatched error *)
  | S.TryFinally (_, _, _)  (* any try..finally is assumed to throw out uncached error *)
  | S.Throw (_,_)
  | S.Hint (_,_,_)
    -> true

let apply_op1 p (op : string) e : S.exp option = 
  if (op_has_side_effect op) then
    None
  else
    try 
      let v = exp_to_value e in
      let op = op1 dummy_store op in
      let result = op v in
      Some (value_to_exp result p)
    with _ -> None
                          
let apply_op2 p op e1 e2 : S.exp option =
  if (op_has_side_effect op) then
    None
  else
    try
      let v1 = exp_to_value e1 in
      let v2 = exp_to_value e2 in
      let op = op2 dummy_store op in
      let result = op v1 v2 in
      Some (value_to_exp result p)
    with _ -> None

let rec is_bound (x : S.exp) (body : S.exp) : bool =
  match x, body with 
  | S.Id (_, var1), S.Let (_, var2, xexp, body) -> var1 = var2 || is_bound x xexp || is_bound x body
  | S.Id (_, var1), S.Rec (_, var2, xexp, body) -> var1 = var2 || is_bound x xexp || is_bound x body
  | S.Id (_, var1), S.Lambda (_, xs, body) ->
    List.mem var1 xs || is_bound x body
  | S.Id (_, var1), S.SetBang (_, var2, e) -> var1 = var2 || is_bound x e
  | _ -> List.exists (fun(e)->is_bound x e) (S.child_exps body)

let same_Id (s : string) (e : S.exp) = match e with
  | S.Id (_, id) when id = s -> true
  | _ -> false

let is_Id (x : S.exp) : bool = match x with
  | S.Id (_, _) -> true
  | _ -> false

let is_Num (x : S.exp) : bool = match x with
  | S.Num (_, _) -> true
  | _ -> false

let is_Undef (x : S.exp) : bool = match x with
  | S.Undefined _ -> true
  | _ -> false

let rec is_constant (e : S.exp) pool : bool = match e with
  | S.Object(_,_,_) -> is_object_constant e pool
  | S.Lambda(_,_,_) -> is_lambda_constant e 
  | S.Id (_, _) -> is_const_var e pool
  | _ -> is_prim_constant e
(* an const object requires extensible is false, all fields have configurable
   and writable set to false.

   XXX: it seems that when getter and setter are present, configurable cannot be set from 
        the syntax. So there is no such an object that getter and setter and configurable attr
        are both initially constant.
 *)
and is_object_constant (e : S.exp) pool : bool = match e with
  | S.Object (_, attr, strprop) ->
     let { S.primval=primval;S.proto=proto;S.code=code;S.extensible = ext;S.klass=_ } = attr in
     let const_primval = match primval with
       | Some x -> is_constant x pool
       | None -> true 
     in
     let const_proto = match proto with
       | Some x -> is_constant x pool
       | None -> true
     in
     let const_code = match code with
       | Some x -> is_constant x pool
       | None -> true
     in 
     if (not const_primval || not const_proto || not const_code || ext = true) then
       false 
     else begin 
         let const_prop (p : string * S.prop) = match p with
           | (s, S.Data ({S.value = value; S.writable=false}, _, false)) -> 
              is_constant value pool
           | _ -> false
         in
         let is_const_property = List.for_all const_prop strprop in
         is_const_property
       end
  | _ -> false

(* a lambda is a constant if no free vars and no side effect in the body *)
and is_lambda_constant (e: S.exp) : bool = match e with
  | S.Lambda (_, ids, body) ->
     IdSet.is_empty (S.free_vars e) && not (has_side_effect body)
  | _ -> false

(* NOTE(junsong): this predicate can only be used for non-lambda and non-object non-id exp *)
and is_prim_constant (e : S.exp) : bool = match e with
  | S.Null _
  | S.Undefined _
  | S.Num (_, _)
  | S.String (_, _)
  | S.True _
  | S.False _ -> true
  | _ -> false

and is_const_var (e : S.exp)  (pool : pool) : bool = match e with
  | S.Id (_, id) -> 
     begin
       try let (_, const, subst) = IdMap.find id pool in const 
       with _ -> false
     end
  | _ -> false
       
(* decide if x is mutated in e *)
let rec mutate_var (x : id) (e : S.exp) : bool = match e with
  | S.SetBang (_, var, target) -> x = var || mutate_var x target
  | S.Let (_, var, defn, body) ->
     if (mutate_var x defn) then (* look at the def first *)
       true
     else
       if (var = x) then (* previous scope is over *)
         false
       else (* continue search in body *)
         mutate_var x body
  | S.Rec (_, var, defn, body) ->
     if (mutate_var x defn) then true
     else
       if (var = x) then false
       else mutate_var x body
  | S.Lambda (_, vars, body) ->
     if (List.mem x vars) then (* x is shadowed in lambda *)
       false
     else
       mutate_var x body
  | _ -> List.exists (fun x->x) (map (fun exp-> mutate_var x exp) (S.child_exps e))

let rec valid_for_folding (e : S.exp) : bool = 
  match e with
  | S.Null _ 
  | S.Undefined _
  | S.String (_,_)
  | S.Num (_,_)
  | S.True _
  | S.False _ -> true
  | S.Id (_,_) -> false
  | S.Object (_, attr, strprop) ->
     let { S.primval=primval;
           S.proto=proto;
           S.code=code;
           S.extensible = ext; S.klass=_ } = attr in
     let const_primval = match primval with
       | Some x -> valid_for_folding x && not (has_side_effect x)
       | None -> true 
     in
     let const_proto = match proto with 
       | Some x -> valid_for_folding x && not (has_side_effect x)
       | None -> true
     in
     let const_code = match code with
       | Some x -> valid_for_folding x && not (has_side_effect x) 
       | None -> true
     in 
     if (not const_primval || not const_proto || not const_code || ext = true) then
       begin 
       false 
       end 
     else 
         let const_prop (p : string * S.prop) = match p with
           | (s, S.Data ({S.value = value; S.writable=false}, _, false)) -> 
              valid_for_folding value && not (has_side_effect value)
           (*?*)| (s, S.Accessor ({S.getter=_; S.setter=_},_,_)) -> true
           | _ -> false
         in
         List.for_all const_prop strprop 
  | S.Lambda (_, xs, body) ->
     IdSet.is_empty (S.free_vars e) && not (has_side_effect body)
  | _ -> List.for_all valid_for_folding (S.child_exps e) && not (has_side_effect e)


(* decide if `id` appears more than once.
   NOTE: This function doesn't build control flow graph, so simply
         issue error on SetBang.
*)
let multiple_usages (var_id : id) (e : S.exp) : bool =
  let use = (ref 0) in
  let result() = !use >= 2 in
  let rec multiple_usages_rec (var_id : id) (e : S.exp) : bool = 
    match e with
    | S.Id (p, x) ->
       if (x = var_id) then 
         begin
           use := !use + 1;
           result()
         end
       else false
    | S.Let (_, x, xexp, body) ->
       if (multiple_usages_rec var_id xexp) then true
       else begin
           if (x = var_id) then (* previous x scope is over. *)
             result()
           else
             multiple_usages_rec var_id body
         end
    | S.SetBang (_, x, vexp) ->
      (*ignore when x = id*)
      multiple_usages_rec var_id vexp
    | S.Rec (_, x, xexp, body) ->
       if (multiple_usages_rec var_id xexp) then true
       else begin
           if (x = var_id) then (* previous x scope is over. *)
             result()
           else
             multiple_usages_rec var_id body
         end
    | S.Lambda (_, xs, body) -> 
       if (List.mem var_id xs) then false (* don't search body *)
       else 
         multiple_usages_rec var_id body
    | _ -> List.exists (fun x->x) (map (fun exp->multiple_usages_rec var_id exp) (S.child_exps e))
  in multiple_usages_rec var_id e


(* before any use of x, there is no side effect *)
(* NOTE: the given exp should contains no duplicate bindings of x *)
let rec no_side_effect_prior_use (x : id) (e : S.exp) : bool =
  let rec use_id (id : id) (e : S.exp) : bool =
    match e with
    | S.Id (_, x) -> x = id
    | S.Let (_, x, _, _) when x = id -> false
    | S.Rec (_, x, _, _) when x = id -> false
    | S.Lambda (_, xs, _) when List.mem id xs -> false
    | S.SetBang (_, x, _) when x = id ->
      failwith "[use id] this cannot happen; the name should have been renamed"
    | _ -> List.exists (fun exp-> use_id id exp) (S.child_exps e)
  in
  let apply_to_attr (f : S.exp->bool) (attr : S.attrs) = 
    let apply_to_option (opt : S.exp option) : bool = match opt with
      | Some(e) -> f e
      | None -> false
    in 
    apply_to_option attr.S.primval &&
    apply_to_option attr.S.code &&
    apply_to_option attr.S.proto
  in
  let rec apply_to_props (f : S.exp->bool) (props : (string * S.prop) list) : bool = 
    let handle_prop p = match p with
      | (s, S.Data (data, enum, config)) ->
        f data.S.value
      | (s, S.Accessor (acc, enum, config)) ->
        f acc.S.getter && f acc.S.setter
    in
    List.for_all handle_prop props
  in

  let check_prior_use_x exp : bool = no_side_effect_prior_use x exp in
  (* for every expression, if x is not in it but this expression
     has side effect, the whole expressionn should return false.
  *)
  let x_in_use = use_id x e in
  let e_has_side_effect = has_side_effect e in
  match x_in_use, e_has_side_effect with
  | false, true -> false
  | false, false -> true
  | true, false -> true
  | true, true ->
    (* NOTE: in the following expression, 
       X IS IN USE and e has side effect. break down e and
       do scrutiny *)
    begin match e with
      | S.Undefined _
      | S.Null _
      | S.String (_,_)
      | S.Num (_,_)
      | S.True _
      | S.False _ 
      | S.Id (_, _)
      | S.Hint (_, _, _) ->
        (* in these cases, e should have no side effect *)
        failwith "unreachable"
      | S.Object (_, attrs, props) ->
        (*this says: if attrs has no side effect before x use,
          continue to check attrs; otherwise return false *)
        apply_to_attr check_prior_use_x attrs &&
        apply_to_props check_prior_use_x props

      | S.GetAttr(_, _, obj, field) ->
        check_prior_use_x obj && check_prior_use_x field

      | S.SetAttr (_, _, obj, field, newval) ->
        check_prior_use_x obj &&
        check_prior_use_x field &&
        check_prior_use_x newval

      | S.GetObjAttr (_, _, obj) ->
        check_prior_use_x obj

      | S.SetObjAttr (_, _, obj, attre) ->
        check_prior_use_x obj &&
        check_prior_use_x attre

      | S.GetField (_, obj, fld, args) -> 
        check_prior_use_x obj &&
        check_prior_use_x fld &&
        check_prior_use_x args


      | S.SetField (_, obj, fld, newval, args) ->
        check_prior_use_x obj &&
        check_prior_use_x fld &&
        check_prior_use_x newval &&
        check_prior_use_x args

      | S.DeleteField (_, obj, fld) ->
        check_prior_use_x obj &&
        check_prior_use_x fld

      | S.OwnFieldNames (_, obj) -> 
        check_prior_use_x obj

      | S.SetBang (_, xx, v) ->
        (* x in use and e is SetBang*)
        let _ = assert (xx <> x) in
        check_prior_use_x v


      | S.Op1 (_, _, e) ->
        check_prior_use_x e

      | S.Op2 (_, _, e1, e2) ->
        check_prior_use_x e1 && check_prior_use_x e2

      | S.If (_, cond, thn, els) -> 
        check_prior_use_x cond &&
        check_prior_use_x thn &&
        check_prior_use_x els

      | S.App (_, func, args) ->
        check_prior_use_x func &&
        List.for_all check_prior_use_x args

      | S.Seq (_, e1, e2) ->
        check_prior_use_x e1 &&
        check_prior_use_x e2

      | S.Let (_, xx, exp, body) ->
        let _ = assert (xx <> x) in
        check_prior_use_x exp &&
        check_prior_use_x body 

      | S.Rec (_, xx, exp, body) ->
        let _ = assert (x <> xx) in
        check_prior_use_x exp &&
        check_prior_use_x body

      | S.Label (_, l, e) ->
        check_prior_use_x e

      | S.Break (_, l, e) ->
        check_prior_use_x e

      | S.TryCatch (_, body, catch) ->
        check_prior_use_x body &&
        check_prior_use_x catch

      | S.TryFinally (_, body, fin) ->
        check_prior_use_x body &&
        check_prior_use_x fin

      | S.Throw (_, e) ->
        check_prior_use_x e

      | S.Lambda (_, xs, e) ->
        assert (not (List.mem x xs));
        check_prior_use_x e
    end

let usercode_regexp = Str.regexp ".*USER CODE BELOW.*"

let is_env_delimiter str =
  Str.string_match usercode_regexp str 0

(* reach the delimiter of environment and user code *)
let rec get_code_after_delimiter e : S.exp option =
  match e with
  | S.Seq (_, S.Hint (p, id, _), e2) when is_env_delimiter id ->
    Some e2
  | S.Seq (_, _, e2) ->
    get_code_after_delimiter e2
  | S.Let (_, _, _, body) ->
    get_code_after_delimiter body
  | S.Rec (_, _, _, body) ->
    get_code_after_delimiter body
  | _ ->
    None

(* only apply function f to user code. This function will totally
   ignore the environment code. Note: USER CODE BELOW hint might occur
   multiple times.
*)
let apply_to_user_code (e : S.exp) (f : (S.exp -> 'a)) : 'a =
  let rec get_user_code_rec e : S.exp =
    match get_code_after_delimiter e with
    | None -> e
    | Some (code) ->
      get_user_code_rec code
  in
  f (get_user_code_rec e)

(*TOO slow to be useful*)
let rec keep_env_apply_to_user_code (e : S.exp) (f : (S.exp -> S.exp)) : S.exp =
  let apply e f =
    match e with
    | S.Seq (p, S.Hint (p1, id, e), e2) when is_env_delimiter id ->
      begin match get_code_after_delimiter e2 with
        | None ->
          S.Seq (p, S.Hint (p1, id, e), f e2)
        | Some (_) ->
          S.Seq (p, S.Hint (p1, id, e), keep_env_apply_to_user_code e2 f)
      end
    | _ ->
      optimize (fun e -> keep_env_apply_to_user_code e f) e
  in
  match get_code_after_delimiter e with
  | None ->
    (* there is not environment *)
    f e
  | _ ->
    (* otherwise, start apply f to user code *)
    apply e f

