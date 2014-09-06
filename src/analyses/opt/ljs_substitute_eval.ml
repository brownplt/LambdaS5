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

(* constpool is constant pool. It maps from id to constant `exp` and `substitute`, which
   indicates if the constant `exp` can substitute id later
 *)
type constpool = (exp * bool) IdMap.t

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
  let empty_constpool = IdMap.empty in
  let modified = (ref false) in
  let rec substitute_eval e constpool =
    let rec substitute_eval_option opt constpool = match opt with
      | Some (e) -> Some (substitute_eval e constpool)
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
           match IdMap.find x constpool with
           | (x_v, true) -> 
              begin 
                Printf.printf "replace %s with " x; Ljs_pretty.exp x_v Format.std_formatter; print_newline();
                x_v
              end
           | (x_v, false) -> e
         with Not_found -> e 
       end
    | Object (p, attrs, strprop) ->
       let new_attrs = {
         primval = substitute_eval_option attrs.primval constpool;
         code = substitute_eval_option attrs.code constpool;
         proto = substitute_eval_option attrs.proto constpool;
         klass = attrs.klass;
         extensible = attrs.extensible } in
       let handle_prop p = match p with
         | (s, Data (data, enum, config)) ->
            s, Data ({value = substitute_eval data.value constpool;
                      writable = data.writable}, enum, config)
         | (s, Accessor (acc, enum, config)) ->
            s, Accessor ({getter = substitute_eval acc.getter constpool; setter = substitute_eval acc.setter constpool},
                         enum, config) in
       let prop_list = List.map handle_prop strprop in
       Object (p, new_attrs, prop_list)

    | GetAttr (p, pattr, obj, field) -> 
       let o = substitute_eval obj constpool in
       let f = substitute_eval field constpool in
       GetAttr(p, pattr, o, f)

    | SetAttr (p, attr, obj, field, newval) ->
       let o = substitute_eval obj constpool in
       let f = substitute_eval field constpool in
       let v = substitute_eval newval constpool in
       SetAttr (p, attr, o, f, v)

    | GetObjAttr (p, oattr, obj) ->
       let o = substitute_eval obj constpool in
       GetObjAttr(p, oattr, o)

    | SetObjAttr (p, oattr, obj, attre) ->
       let o = substitute_eval obj constpool in
       let attr = substitute_eval attre constpool in
       SetObjAttr (p, oattr, o, attr)

    | GetField (p, obj, fld, args) -> 
       let o = substitute_eval obj constpool in
       let f = substitute_eval fld constpool in
       let a = substitute_eval args constpool in
       GetField (p, o, f, a)

    | SetField (p, obj, fld, newval, args) ->
       let o = substitute_eval obj constpool in
       let f = substitute_eval fld constpool in
       let v = substitute_eval newval constpool in
       let a = substitute_eval args constpool in
       SetField (p, o, f, v, a)

    | DeleteField (p, obj, fld) ->
       let o = substitute_eval obj constpool in
       let f = substitute_eval fld constpool in
       DeleteField (p, o, f)

    | OwnFieldNames (p, obj) -> 
       OwnFieldNames (p, (substitute_eval obj constpool))

    | SetBang (p, x, e) ->
       SetBang (p, x, (substitute_eval e constpool))

    | Op1 (p, op, e) ->
       Op1 (p, op, (substitute_eval e constpool))

    | Op2 (p, op, e1, e2) ->
       Op2 (p, op, (substitute_eval e1 constpool), (substitute_eval e2 constpool))

    | If (p, cond, thn, els) -> (* more optimization in constant folding *)
       If (p, (substitute_eval cond constpool), (substitute_eval thn constpool), (substitute_eval els constpool))

    | App (p, func, args) ->
       let f = substitute_eval func constpool in
       let a = List.map (fun x->substitute_eval x constpool) args in
       App (p, f, a)

    | Seq (p, e1, e2) ->
       let new_e1 = substitute_eval e1 constpool in
       let new_e2 = substitute_eval e2 constpool in
       Seq (p, new_e1, new_e2)

    | Let (p, x, exp, body) ->
       let x_v = substitute_eval exp constpool in
       let nonconst_bound() =
         let new_constpool = IdMap.remove x constpool in
         let new_body = substitute_eval body new_constpool in 
         Let (p, x, x_v, new_body) in

       if mutate_var x body then nonconst_bound()
       else
         (* no mutation *)
         let is_const = EV.is_constant x_v constpool in
         if not is_const then nonconst_bound()
         else
           (* is constant, decide the substitute *)
           let substitute = 
             EV.is_scalar_constant x_v || EV.is_const_var x_v constpool ||
               ((EV.is_object_constant x_v constpool || EV.is_lambda_constant x_v) && 
                  not (multiple_usages x body)) 
           in
           let new_constpool = IdMap.add x (x_v, substitute) constpool in
           if substitute then
             begin
               modified := true;
               substitute_eval body new_constpool
             end
           else
             let new_body = substitute_eval body new_constpool in
             Let (p, x, x_v, new_body)
             
    | Rec (p, x, exp, body) ->  
       let x_v = substitute_eval exp constpool in
       let nonconst_bound() =
         let new_constpool = IdMap.remove x constpool in
         let new_body = substitute_eval body new_constpool in 
         Rec (p, x, x_v, new_body) in

       if mutate_var x body then nonconst_bound()
       else
         (* no mutation *)
         let is_const = EV.is_constant x_v constpool in
         if not is_const then nonconst_bound()
         else
           (* is constant, decide the substitute, const lambda exp can be substitute
              if the lambda is used once *)
           let substitute =  not (multiple_usages x body) in
           let new_constpool = IdMap.add x (x_v, substitute) constpool in
           if substitute then
             begin
               modified := true;
               substitute_eval body new_constpool
             end
           else
             let new_body = substitute_eval body new_constpool in
             Rec (p, x, x_v, new_body)

    | Label (p, l, e) ->
       let new_e = substitute_eval e constpool in
       Label (p, l, new_e)

    | Break (p, l, e) ->
       let new_e = substitute_eval e constpool in
       Break (p, l, new_e)

    | TryCatch (p, body, catch) ->
       let b = substitute_eval body constpool in
       let c = substitute_eval catch constpool in
       TryCatch (p, b, c)

    | TryFinally (p, body, fin) ->
       let b = substitute_eval body constpool in
       let f = substitute_eval fin constpool in
       TryFinally (p, b, f)
    | Throw (p, e) ->
       Throw (p, (substitute_eval e constpool))

    | Lambda (p, xs, e) -> (* lambda needs a modified constpool *) (* TODO: see lambda in ljs_eval.ml *)
       let rec get_new_constpool ids constpool =  match ids with
         | [] -> constpool
         | id :: rest ->
            let new_constpool = IdMap.remove id constpool in
            get_new_constpool rest new_constpool 
       in 
       let new_constpool = get_new_constpool xs constpool in
       Lambda (p, xs, (substitute_eval e new_constpool))

    | Eval (p, e, bindings) ->
       let new_e = substitute_eval e constpool in
       let new_bindings = substitute_eval bindings constpool in
       Eval (p, new_e, new_bindings)
    | Hint (p, id, e) ->
       Hint (p, id, (substitute_eval e constpool)) 
  in
  let result = substitute_eval e empty_constpool in
  result, !modified

