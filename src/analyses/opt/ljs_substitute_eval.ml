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

(* pool is maps from id to `exp` and `is constant?` `can be substituted?`, which
   indicates if the `exp` can replace id.
 *)
type pool = (exp * bool * bool) IdMap.t

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

let rec substitute_const (e : exp) : (exp * bool) =
  let empty_pool = IdMap.empty in
  let modified = (ref false) in
  let rec substitute_eval e pool =
    let rec substitute_eval_option opt pool = match opt with
      | Some (e) -> Some (substitute_eval e pool)
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
         try 
           match IdMap.find x pool with
           | (x_v, _, true) -> x_v
           | (x_v, _, false) -> e
         with Not_found -> e 
       end
    | Object (p, attrs, strprop) ->
       let new_attrs = {
         primval = substitute_eval_option attrs.primval pool;
         code = substitute_eval_option attrs.code pool;
         proto = substitute_eval_option attrs.proto pool;
         klass = attrs.klass;
         extensible = attrs.extensible } in
       let handle_prop p = match p with
         | (s, Data (data, enum, config)) ->
            s, Data ({value = substitute_eval data.value pool;
                      writable = data.writable}, enum, config)
         | (s, Accessor (acc, enum, config)) ->
            s, Accessor ({getter = substitute_eval acc.getter pool; setter = substitute_eval acc.setter pool},
                         enum, config) in
       let prop_list = List.map handle_prop strprop in
       Object (p, new_attrs, prop_list)

    | GetAttr (p, pattr, obj, field) -> 
       let o = substitute_eval obj pool in
       let f = substitute_eval field pool in
       GetAttr(p, pattr, o, f)

    | SetAttr (p, attr, obj, field, newval) ->
       let o = substitute_eval obj pool in
       let f = substitute_eval field pool in
       let v = substitute_eval newval pool in
       SetAttr (p, attr, o, f, v)

    | GetObjAttr (p, oattr, obj) ->
       let o = substitute_eval obj pool in
       GetObjAttr(p, oattr, o)

    | SetObjAttr (p, oattr, obj, attre) ->
       let o = substitute_eval obj pool in
       let attr = substitute_eval attre pool in
       SetObjAttr (p, oattr, o, attr)

    | GetField (p, obj, fld, args) -> 
       let o = substitute_eval obj pool in
       let f = substitute_eval fld pool in
       let a = substitute_eval args pool in
       GetField (p, o, f, a)

    | SetField (p, obj, fld, newval, args) ->
       let o = substitute_eval obj pool in
       let f = substitute_eval fld pool in
       let v = substitute_eval newval pool in
       let a = substitute_eval args pool in
       SetField (p, o, f, v, a)

    | DeleteField (p, obj, fld) ->
       let o = substitute_eval obj pool in
       let f = substitute_eval fld pool in
       DeleteField (p, o, f)

    | OwnFieldNames (p, obj) -> 
       OwnFieldNames (p, (substitute_eval obj pool))

    | SetBang (p, x, e) ->
       SetBang (p, x, (substitute_eval e pool))

    | Op1 (p, op, e) ->
       Op1 (p, op, (substitute_eval e pool))

    | Op2 (p, op, e1, e2) ->
       Op2 (p, op, (substitute_eval e1 pool), (substitute_eval e2 pool))

    | If (p, cond, thn, els) -> (* more optimization in constant folding *)
       If (p, (substitute_eval cond pool), (substitute_eval thn pool), (substitute_eval els pool))

    | App (p, func, args) ->
       let f = substitute_eval func pool in
       let a = List.map (fun x->substitute_eval x pool) args in
       App (p, f, a)

    | Seq (p, e1, e2) ->
       let new_e1 = substitute_eval e1 pool in
       let new_e2 = substitute_eval e2 pool in
       Seq (p, new_e1, new_e2)

    | Let (p, x, exp, body) ->
       let x_v = substitute_eval exp pool in
       let del_x_from_pool_continue currentpool =
         let new_pool = IdMap.remove x currentpool in
         let new_body = substitute_eval body new_pool in 
         Let (p, x, x_v, new_body) 
       in 
       if mutate_var x body then 
         del_x_from_pool_continue pool
       else
         (* no mutation, decide if it is constant *)
         let is_const = EV.is_constant x_v pool in
         if not is_const then 
           begin 
             (* if x_v is not constant, decide if x_v is an id and that id is not bound
                again in body. If so, x->(x_v, not constant, can be substituted) should  
                be added to pool *)
             if (EV.is_Id x_v && not (EV.is_bound x_v body)) then
               let newpool = IdMap.add x (x_v, false, true) pool in
               begin
                 modified := true;
                 substitute_eval body newpool
               end 
             else  (* if it is not a constant and not an id, remove x from pool *)
               del_x_from_pool_continue pool
           end 
         else
           (* is constant, decide the substitute *)
           let substitute = 
             EV.is_scalar_constant x_v || EV.is_const_var x_v pool ||
               ((EV.is_object_constant x_v pool || EV.is_lambda_constant x_v) && 
                  not (multiple_usages x body)) 
           in
           let new_pool = IdMap.add x (x_v, true, substitute) pool in
           (* get the substitution, decide if let should be dropped *)
           if substitute then
             begin 
               if (EV.is_bound x_v body) then 
                 (* if x_v is Id and is bound later. let (x=x_v) should be kept, and 
                      x should be substituted *)
                 let new_pool = IdMap.add x (x_v, true, false) pool in
                 Let (p, x, x_v, (substitute_eval body new_pool))
               else
                 begin
                   modified := true;
                   substitute_eval body new_pool
                 end
             end
           else
             let new_body = substitute_eval body new_pool in
             Let (p, x, x_v, new_body)
             
    | Rec (p, x, exp, body) ->  
       let x_v = substitute_eval exp pool in
       let del_x_from_pool_continue() =
         let new_pool = IdMap.remove x pool in
         let new_body = substitute_eval body new_pool in 
         Rec (p, x, x_v, new_body) in

       if mutate_var x body then del_x_from_pool_continue()
       else
         (* no mutation *)
         let is_const = EV.is_constant x_v pool in
         if not is_const then del_x_from_pool_continue()
         else
           (* is constant, decide the substitute, const lambda exp can be substitute
              if the lambda is used once *)
           let substitute =  not (multiple_usages x body) in
           let new_pool = IdMap.add x (x_v, true, substitute) pool in
           if substitute then
             begin
               modified := true;
               substitute_eval body new_pool
             end
           else
             let new_body = substitute_eval body new_pool in
             Rec (p, x, x_v, new_body)

    | Label (p, l, e) ->
       let new_e = substitute_eval e pool in
       Label (p, l, new_e)

    | Break (p, l, e) ->
       let new_e = substitute_eval e pool in
       Break (p, l, new_e)

    | TryCatch (p, body, catch) ->
       let b = substitute_eval body pool in
       let c = substitute_eval catch pool in
       TryCatch (p, b, c)

    | TryFinally (p, body, fin) ->
       let b = substitute_eval body pool in
       let f = substitute_eval fin pool in
       TryFinally (p, b, f)
    | Throw (p, e) ->
       Throw (p, (substitute_eval e pool))

    | Lambda (p, xs, e) -> (* lambda needs a modified pool *) (* TODO: see lambda in ljs_eval.ml *)
       let rec get_new_pool ids pool =  match ids with
         | [] -> pool
         | id :: rest ->
            let new_pool = IdMap.remove id pool in
            get_new_pool rest new_pool 
       in 
       let new_pool = get_new_pool xs pool in
       Lambda (p, xs, (substitute_eval e new_pool))

    | Eval (p, e, bindings) ->
       let new_e = substitute_eval e pool in
       let new_bindings = substitute_eval bindings pool in
       Eval (p, new_e, new_bindings)
    | Hint (p, id, e) ->
       Hint (p, id, (substitute_eval e pool)) 
  in
  let result = substitute_eval e empty_pool in
  result, !modified

