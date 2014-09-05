open Prelude
open Ljs_syntax
open Ljs_const_folding
module EV = Exp_val


(* Optimization phase.
 *
 * partial evaluation by substitution.
 *
 * This function accepts an exp(see ljs_syntax.ml) and performs
 * subsitution to give out partial evaluation result
 *
 *)


type env = exp IdMap.t

(* partially evaluate GetAttr exp *)

let eval_getattr_exp pos pattr obj field : exp = 
  (* helper function for extracting property of one field *)
  let rec find_field name obj_fields= 
    match obj_fields with 
    | (fld_name, prop) :: rest -> 
       if (fld_name = name) 
       then Some prop
       else find_field name rest  
    | [] -> None in
  let exp_bool (b : bool) : exp = match b with
    | true -> True pos
    | false -> False pos in
  match obj, field with 
  | Object (_, attrs, strprop), String (_, name) -> 
     (* get field and its property *)
     begin match find_field name strprop with
     | Some prop -> 
        begin
          match pattr, prop with 
          | Value, Data ({value = v; writable=_}, _, _) -> v
          (*| Getter, Accessor ({getter = gv; setter=_}, _, _) -> gv*)
          (*| Setter, Accessor ({getter = _; setter=sv}, _, _) -> sv*)
          | Config, Data (_, _, config) -> exp_bool config
          (*| Config, Accessor (_, _, config) -> exp_bool config*)
          | Writable, Data({value=_; writable=w}, _, _) -> exp_bool w
          | Enum, Data(_, enum, _) -> exp_bool enum
          (*| Enum, Accessor (_, enum, _) -> exp_bool enum *)
          | _ -> GetAttr(pos, pattr, obj, field) (* no optimization in other situations *)
        end
     | None -> GetAttr(pos, pattr, obj, field) (* if field is not in the object. don't optimize. *)
     end
  | _ -> GetAttr(pos, pattr, obj, field)
 
(* partially evaluate exp GetObjAttr *)
let eval_getobjattr_exp pos (oattr : oattr) o : exp =
  match oattr, o with 
  | Klass, Object (_, {klass=klass}, _) -> String(pos, klass)
  | Code, Object (_, {code=None}, _) -> Null(pos)
  | Code, Object (_, {code=Some code}, _) -> code
  | _ -> GetObjAttr(pos, oattr, o)

(* decide if `id` appears more than once.
   NOTE: This function doesn't build control flow graph, so simply
         issue error on SetBang.
*)
let multiple_usages (var_id : id) (e : exp) : bool =
  let use = (ref 0) in
  let result() = !use >= 2 in
  let rec multiple_usages_rec (var_id : id) (e : exp) : bool = 
    match e with
    | Id (p, x) ->
       if (x = var_id) then 
         begin
           use := !use + 1;
           result()
         end
       else false
    | Let (_, x, xexp, body) ->
       if (multiple_usages_rec var_id xexp) then true
       else begin
           if (x = var_id) then (* previous x scope is over. *)
             result()
           else
             multiple_usages_rec var_id body
         end
    | SetBang (_, x, vexp) -> 
       if (x = var_id) then failwith "should not reach here"
       else multiple_usages_rec var_id vexp
    | Rec (_, x, xexp, body) ->
       if (multiple_usages_rec var_id xexp) then true
       else begin
           if (x = var_id) then (* previous x scope is over. *)
             result()
           else
             multiple_usages_rec var_id body
         end
    | Lambda (_, xs, body) -> 
       if (List.mem var_id xs) then false (* don't search body *)
       else 
         multiple_usages_rec var_id body
    | _ -> List.exists (fun x->x) (map (fun exp->multiple_usages_rec var_id exp) (child_exps e))
  in multiple_usages_rec var_id e

(* decide if x is mutated in e *)
let rec mutate_var (x : id) (e : exp) : bool = match e with
  | SetBang (_, var, target) -> x = var || mutate_var x target
  | Let (_, var, defn, body) ->
     if (mutate_var x defn) then (* look at the def first *)
       true
     else
       if (var = x) then (* previous scope is over *)
         false
       else (* continue search in body *)
         mutate_var x body
  | Rec (_, var, defn, body) ->
     if (mutate_var x defn) then true
     else
       if (var = x) then false
       else mutate_var x body
  | Lambda (_, vars, body) ->
     if (List.mem x vars) then (* x is shadowed in lambda *)
       false
     else
       mutate_var x body
  | _ -> List.exists (fun x->x) (map (fun exp-> mutate_var x exp) (child_exps e))

(* NOTE: xexp should be an optimized one

To drop a let(or rec binding), 
 - var will not be mutated.
 - either var is used only once if var is object constant or lambda constant, 
   or var is other constants, e.g. integer *)
let can_substitute x xexp body : bool = 
  if mutate_var x body then false
  else 
    if (EV.is_scalar_constant xexp) then true
    else
      if (EV.is_object_constant xexp || EV.is_lambda_constant xexp) then
        not (multiple_usages x body)
      else false
  
  
let rec substitute_const (e : exp) : (exp * bool) =
  let empty_env = IdMap.empty in
  let modified = (ref false) in
  let rec substitute_eval e env =
    let rec substitute_eval_option opt env = match opt with
      | Some (e) -> Some (substitute_eval e env)
      | None -> None in
    match e with
    | Undefined _ -> e
    | Null _ -> e
    | String (_, _) -> e
    | Num (_, n) -> e
    | True _ -> e
    | False _ -> e
    | Id (p, x) ->
       begin
         try IdMap.find x env
         with Not_found -> e end
    | Object (p, attrs, strprop) ->
       let new_attrs = {
         primval = substitute_eval_option attrs.primval env;
         code = substitute_eval_option attrs.code env;
         proto = substitute_eval_option attrs.proto env;
         klass = attrs.klass;
         extensible = attrs.extensible } in
       let handle_prop p = match p with
         | (s, Data (data, enum, config)) ->
            s, Data ({value = substitute_eval data.value env;
                      writable = data.writable}, enum, config)
         | (s, Accessor (acc, enum, config)) ->
            s, Accessor ({getter = substitute_eval acc.getter env; setter = substitute_eval acc.setter env},
                         enum, config) in
       let prop_list = List.map handle_prop strprop in
       Object (p, new_attrs, prop_list)

    | GetAttr (p, pattr, obj, field) -> 
       (* if object is a const object and field name is a const, 
          try to get the field and then its attr *)
       let o = substitute_eval obj env in
       let f = substitute_eval field env in
       eval_getattr_exp p pattr o f

    | SetAttr (p, attr, obj, field, newval) ->
       let o = substitute_eval obj env in
       let f = substitute_eval field env in
       let v = substitute_eval newval env in
       SetAttr (p, attr, o, f, v)

    | GetObjAttr (p, oattr, obj) ->
       let o = substitute_eval obj env in
       eval_getobjattr_exp p oattr o

    | SetObjAttr (p, oattr, obj, attre) ->
       let o = substitute_eval obj env in
       let attr = substitute_eval attre env in
       SetObjAttr (p, oattr, o, attr)

    | GetField (p, obj, fld, args) -> 
       let o = substitute_eval obj env in
       let f = substitute_eval fld env in
       let a = substitute_eval args env in
       GetField (p, o, f, a)

    | SetField (p, obj, fld, newval, args) ->
       let o = substitute_eval obj env in
       let f = substitute_eval fld env in
       let v = substitute_eval newval env in
       let a = substitute_eval args env in
       SetField (p, o, f, v, a)

    | DeleteField (p, obj, fld) ->
       let o = substitute_eval obj env in
       let f = substitute_eval fld env in
       DeleteField (p, o, f)

    | OwnFieldNames (p, obj) -> 
       OwnFieldNames (p, (substitute_eval obj env))

    | SetBang (p, x, e) ->
       SetBang (p, x, (substitute_eval e env))

    | Op1 (p, op, e) ->
       Op1 (p, op, (substitute_eval e env))

    | Op2 (p, op, e1, e2) ->
       Op2 (p, op, (substitute_eval e1 env), (substitute_eval e2 env))

    | If (p, cond, thn, els) -> (* more optimization in constant folding *)
       If (p, (substitute_eval cond env), (substitute_eval thn env), (substitute_eval els env))

    | App (p, func, args) ->
       let f = substitute_eval func env in
       let a = List.map (fun x->substitute_eval x env) args in
       App (p, f, a)

    | Seq (p, e1, e2) ->
       let new_e1 = substitute_eval e1 env in
       let new_e2 = substitute_eval e2 env in
       Seq (p, new_e1, new_e2)

    (* TODO: write a predicate drop_binding *)
    | Let (p, x, exp, body) ->
       let new_exp = substitute_eval exp env in
       let no_mutation = not (mutate_var x body) in
       let is_obj_const = EV.is_object_constant new_exp in
       let is_lambda_const = EV.is_lambda_constant new_exp in
       (* obj constant should only be used once *)
       if (no_mutation &&
           (((is_obj_const || is_lambda_const) && not (multiple_usages x body)) || 
            EV.is_scalar_constant new_exp))
       then
         let new_env = IdMap.add x new_exp env in
         begin modified := true;
               substitute_eval body new_env
         end
       else 
         let new_env = IdMap.remove x env in
         let new_body = substitute_eval body new_env in
         Let (p, x, new_exp, new_body)
             
    | Rec (p, x, exp, body) -> 
       let new_exp = substitute_eval exp env in
       let no_mutation = not (mutate_var x body) in
       let is_lambda_const = EV.is_lambda_constant new_exp in 
       if (no_mutation && is_lambda_const && not (multiple_usages x body))
       then
         let new_env = IdMap.add x new_exp env in
         begin modified := true;
               substitute_eval body new_env
         end
       else
         let new_env = IdMap.remove x env in
         let new_body = substitute_eval body new_env in
         Rec (p, x, new_exp, new_body)

    | Label (p, l, e) ->
       let new_e = substitute_eval e env in
       Label (p, l, new_e)

    | Break (p, l, e) ->
       let new_e = substitute_eval e env in
       Break (p, l, new_e)

    | TryCatch (p, body, catch) ->
       let b = substitute_eval body env in
       let c = substitute_eval catch env in
       TryCatch (p, b, c)

    | TryFinally (p, body, fin) ->
       let b = substitute_eval body env in
       let f = substitute_eval fin env in
       TryFinally (p, b, f)
    | Throw (p, e) ->
       Throw (p, (substitute_eval e env))

    | Lambda (p, xs, e) -> (* lambda needs a modified env *) (* TODO: see lambda in ljs_eval.ml *)
       let rec get_new_env ids env =  match ids with
         | [] -> env
         | id :: rest ->
            let new_env = IdMap.remove id env in
            get_new_env rest new_env 
       in 
       let new_env = get_new_env xs env in
       Lambda (p, xs, (substitute_eval e new_env))

    | Eval (p, e, bindings) ->
       let new_e = substitute_eval e env in
       let new_bindings = substitute_eval bindings env in
       Eval (p, new_e, new_bindings)
    | Hint (p, id, e) ->
       Hint (p, id, (substitute_eval e env)) 
  in
  let result = substitute_eval e empty_env in
  result, !modified

