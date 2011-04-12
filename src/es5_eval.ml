open Prelude
open Es5_syntax
open JavaScript_syntax
open Es5_values
open Es5_delta

let rec interp_error pos message =
  "[interp] (" ^ string_of_position pos ^ ") " ^ message

let rec apply func args = match func with
  | Closure c -> c args
  | _ -> failwith ("[interp] Applied non-function, was actually " ^ 
		     pretty_value func)

(* args is the "arguments" object *)
let rec apply_obj o this args = match o with
  | ObjCell c -> 
      let (attrs, props) = !c in
	begin
	  try
	    let code_attr = IdMap.find "code" attrs in
	      apply code_attr [this; args]
	  with Not_found ->
	    Fail "Applying inapplicable object!"
	end
  | _ -> Fail "Applying non-object!"
	  

let rec get_field p obj1 obj2 field args = match obj1 with
  | Const (CNull) -> Const (CUndefined) (* nothing found *)
  | ObjCell c ->
      let (attrs, props) = !c in begin
	  try
	    let prop_attrs = IdMap.find field props in
	      try 
		let value = AttrMap.find Value prop_attrs in
		  value
	      with Not_found ->
		try
		  let getter = AttrMap.find Getter prop_attrs in
		    apply_obj getter obj2 (apply args [getter])
		with Not_found -> Const (CUndefined) (* Nothing to get *)
	  with Not_found ->
	    try
	      get_field p (IdMap.find "proto" attrs) obj2 field args
	    with Not_found ->
	      Const (CUndefined) (* No prototype found *)
	end
  | _ -> failwith (interp_error p 
		     "get_field received (or reached) a non-object.  The expression was (get-field " 
		   ^ pretty_value obj1 
		   ^ " " ^ pretty_value obj2 
		   ^ " " ^ field ^ ")")


(* EUpdateField-Add *)
(* ES5 8.12.5, step 6 *)
let rec add_field obj field newval = match obj with
  | ObjCell c -> let (attrs, props) = !c in
      if IdMap.mem "extensible" attrs &&
	((IdMap.find "extensible" attrs) = (Const (CBool true))) then begin
	  c := (attrs, IdMap.add field 
		  (AttrMap.add Value newval
		     (AttrMap.add Config (Const (CBool true))
			(AttrMap.add Writable (Const (CBool true))
			   (AttrMap.add Enum (Const (CBool true))
			      AttrMap.empty))))
		  props);
	  newval
	end
      else Const CUndefined	
  | _ -> failwith ("[interp] add_field given non-object.")

(* Both functions (because a property can satisfy writable and not_writable) *)
let rec writable prop = 
  (AttrMap.mem Writable prop) &&
    ((AttrMap.find Writable prop) = Const (CBool true))

let rec not_writable prop = 
  (AttrMap.mem Writable prop) &&
    ((AttrMap.find Writable prop) = Const (CBool false))

(* EUpdateField *)
(* ES5 8.12.4, 8.12.5 *)
let rec update_field obj1 obj2 field newval args = match obj1 with
    (* 8.12.4, step 4 *)
  | Const (CNull) -> add_field obj2 field newval
  | ObjCell c -> let (attrs, props) = !c in
      if (not (IdMap.mem field props)) then
	if (IdMap.mem "proto" attrs) then
	  (* EUpdateField-Proto *)
	  update_field (IdMap.find "proto" attrs) obj2 field newval args
	else
	  (* 8.12.4, step 4, sort of.  Handles if proto doesn't exist *)
	  add_field obj2 field newval
      else
	let prop = (IdMap.find field props) in
	  if writable prop then 
	    if (not (obj1 == obj2)) then
	      (* 8.12.4, last step where inherited.[[writable]] is true *)
	      add_field obj2 field newval
	    else begin
	      (* 8.12.5, step 3 *)
	      c := (attrs, IdMap.add field
		      (AttrMap.add Value newval prop)
		      props);
	      newval
	    end
	  else begin try
	    (* 8.12.5, step 5 *)
	    let setter = AttrMap.find Setter prop in
	      apply_obj setter obj2 (apply args [setter])
	  with Not_found -> 
	    Fail "Field not writable!"
	  end
  | _ -> failwith ("[interp] set_field received (or found) a non-object.  The call was (set-field " ^ pretty_value obj1 ^ " " ^ pretty_value obj2 ^ " " ^ field ^ " " ^ pretty_value newval ^ ")" )

let rec get_attr attr obj field = match obj, field with
  | ObjCell c, Const (CString s) -> let (attrs, props) = !c in
      if (not (IdMap.mem s props)) then
	undef
      else
	let prop = (IdMap.find s props) in
	if (not (AttrMap.mem attr prop)) then
	  undef
	else
	  AttrMap.find attr prop
  | _ -> failwith ("[interp] get-attr didn't get an object and a string.")

let attr_or_false attr prop = 
  if (AttrMap.mem attr prop) then
    match AttrMap.find attr prop with
      | Const (CBool b) -> b
      | _ -> failwith ("[interp] Bad error --- writable or configurable wasn't a boolean")
  else
    false

let to_acc prop = 
  AttrMap.remove Value (AttrMap.remove Writable prop)

let to_data prop = 
  AttrMap.remove Setter (AttrMap.remove Getter prop)

let is_data prop =
  AttrMap.mem Writable prop || AttrMap.mem Value prop &&
    not (AttrMap.mem Setter prop || AttrMap.mem Getter prop)

(* 
   The goal here is to maintain a few invariants (implied by 8.12.9
   and 8.10.5), while keeping things simple from a semantic
   standpoint.  The errors from 8.12.9 and 8.10.5 can be defined in
   the environment and enforced that way.  The invariants here make it
   more obvious that the semantics can't go wrong.  In particular, a
   property

   1.  Has to be either an accessor or a data property, and;

   2.  Can't change attributes when Config is false, except for 
       a. Value, which checks Writable
       b. Writable, which can change true->false
*)
let rec set_attr attr obj field newval = match obj, field with
  | ObjCell c, Const (CString f_str) -> let (attrs, props) = !c in
      if (not (IdMap.mem f_str props)) then
	if (IdMap.mem "extensible" attrs) then
	  match IdMap.find "extensible" attrs with
	    | Const (CBool true) -> 
		let new_prop = AttrMap.add attr newval AttrMap.empty in begin
		    c := (attrs, IdMap.add f_str new_prop props);
		    newval
		  end
	    | _ -> failwith ("[interp] Extensible not true on object to extend with an attr")								  
	else
	  failwith ("[interp] No extensible property on object to extend with an attr")
      else
	let prop = (IdMap.find f_str props) in
	  (* 8.12.9: "If a field is absent, then its value is considered to be false" *)
	let config = attr_or_false Config prop in
	let writable = attr_or_false Writable prop in
	let new_prop = match attr, newval, config, writable with
	  | Enum, Const (CBool true), true, _
	  | Enum, Const (CBool false), true, _ -> 
	      AttrMap.add Enum newval prop
	  | Config, Const (CBool true) , true, _
	  | Config, Const (CBool false), true, _ -> 
	      AttrMap.add Config newval prop
	  | Writable, Const (CBool true), true, _
	  | Writable, Const (CBool false), true, _ ->
	      AttrMap.add Writable newval (to_data prop)
	  | Writable, Const (CBool false), _, true ->
	      if is_data prop then AttrMap.add Writable newval prop else prop
	  | Value, v, _, true -> 
	      AttrMap.add Value v (to_data prop)
	  | Setter, value, true, _ -> 
	      if fun_obj value then 
		AttrMap.add Setter newval (to_acc prop) 
	      else prop
	  | Getter, value, true, _ -> 
	      if fun_obj value then 
		AttrMap.add Getter newval (to_acc prop) 
	      else prop
	  | _ -> prop
	in begin
	    c := (attrs, IdMap.add f_str new_prop props);
	    newval
	  end
  | _ -> failwith ("[interp] set-attr didn't get an object and a string")

(* 8.10.5, steps 7/8 "If iscallable(getter) is false and getter is not
   undefined..." *)

and fun_obj value = match value with
  | ObjCell c -> let (props, _) = !c in
      if IdMap.mem "code" props then
	match IdMap.find "code" props with
	  | Closure _ -> true
	  | _ -> false
      else
	false
  | Const CUndefined -> true
  | _ -> false
	  

let rec eval exp env = match exp with
  | EConst (p, c) -> Const (c)
  | EId (p, x) -> begin
      try
	match IdMap.find x env with
	  | VarCell v -> !v
	  | _ -> failwith ("[interp] (EId) Expected a VarCell for variable " ^ x ^ 
			     " at " ^ (string_of_position p) ^ 
			     ", but found something else: " ^ pretty_value (IdMap.find x env))
      with Not_found ->
	failwith ("[interp] Unbound identifier: " ^ x ^ " in identifier lookup at " ^
		    (string_of_position p))
    end
  | ESet (p, x, e) -> begin
      try
	match IdMap.find x env with
	  | VarCell v -> v := eval e env; !v
	  | _ -> failwith ("[interp] (ESet) Expected a VarCell for variable " ^ x ^ 
			     " at " ^ (string_of_position p) ^ 
			     ", but found something else.")
      with Not_found ->
	failwith ("[interp] Unbound identifier: " ^ x ^ " in set! at " ^
		    (string_of_position p))
    end
  | EObject (p, attrs, props) ->
      let eval_obj_attr m (name, e) = IdMap.add name (eval e env) m in
      let eval_prop_attr m (name, e) = AttrMap.add name (eval e env) m in
      let eval_prop m (name, attrs) = 
	IdMap.add name (fold_left eval_prop_attr AttrMap.empty attrs) m in
	ObjCell (ref (fold_left eval_obj_attr IdMap.empty attrs,
		      fold_left eval_prop IdMap.empty props))
  | EUpdateFieldSurface (p, obj, f, v, args) ->
      let obj_value = eval obj env in
      let f_value = eval f env in
      let v_value = eval v env in
      let args_value = eval args env in begin
	match (obj_value, f_value) with
	  | (ObjCell o, Const (CString s)) ->
	      update_field obj_value 
		obj_value 
		s
		v_value
		args_value
	  | _ -> failwith ("[interp] Update field didn't get an object and a string" 
			   ^ string_of_position p)
	end
  | EGetFieldSurface (p, obj, f, args) ->
      let obj_value = eval obj env in
      let f_value = eval f env in 
      let args_value = eval args env in begin
	match (obj_value, f_value) with
	  | (ObjCell o, Const (CString s)) ->
	      get_field p obj_value obj_value s args_value
	  | _ -> failwith ("[interp] Get field didn't get an object and a string at " 
			   ^ string_of_position p 
			   ^ ". Instead, it got " 
			   ^ pretty_value obj_value 
			   ^ " and " 
			   ^ pretty_value f_value)
	end
  | EDeleteField (p, obj, f) ->
      let obj_val = eval obj env in
      let f_val = eval f env in begin
	match (obj_val, f_val) with
	  | (ObjCell c, Const (CString s)) ->
	      let (attrs,props) = !c in
		if IdMap.mem s props 
		  && IdMap.mem "configurable" attrs
		  && (IdMap.find "configurable" attrs) == Const (CBool true)
		then begin
		  c := (attrs, IdMap.remove s props);
		  Const (CBool true)
		end
		else Const (CBool false)
	  | _ -> failwith ("[interp] EDeleteField didn't get an object and string at " ^
			     string_of_position p)
	end
  | EAttr (p, attr, obj, field) ->
      let obj_val = eval obj env in
      let f_val = eval field env in
	get_attr attr obj_val f_val
  | ESetAttr (p, attr, obj, field, newval) ->
      let obj_val = eval obj env in
      let f_val = eval field env in
      let v_val = eval newval env in
	set_attr attr obj_val f_val v_val
  | EOp1 (p, op, e) ->
      let e_val = eval e env in
	begin match op with
	  | Prim1 str -> op1 str e_val
	  | _ -> failwith ("[interp] Invalid EOp1 form")
	end
  | EOp2 (p, op, e1, e2) -> 
      let e1_val = eval e1 env in
      let e2_val = eval e2 env in
	begin match op with
	  | Prim2 str -> op2 str e1_val e2_val
	  | _ -> failwith ("[interp] Invalid EOp2 form")
	end
  | EOp3 (p, op, e1, e2, e3) -> 
      let e1_val = eval e1 env in
      let e2_val = eval e2 env in
      let e3_val = eval e3 env in
	begin match op with
	  | Prim3 str -> op3 str e1_val e2_val e3_val
	  | _ -> failwith ("[interp] Invalid EOp3 form")
	end
  | EIf (p, c, t, e) ->
      let c_val = eval c env in
	if (c_val = Const (CBool true))
	then eval t env
	else eval e env
  | EApp (p, func, args) -> 
      let func_value = eval func env in
      let args_values = map (fun e -> eval e env) args in begin
	match func_value, args_values with
	  | ObjCell o, [this; args] -> 
	      apply_obj func_value this args
	  | Closure c, _ -> apply func_value args_values
	  | ObjCell o, _ ->
	      failwith ("[interp] Need to provide this and args for a call to a function object at " ^ string_of_position p)
	  | _, _ -> failwith ("[interp] Inapplicable value: " ^ pretty_value func_value ^ ", applied to " ^ pretty_value_list args_values ^ ", at " ^ string_of_position p)
	end
  | ESeq (p, e1, e2) -> 
      eval e1 env;
      eval e2 env
  | ELet (p, x, e, body) ->
      let e_val = eval e env in
	eval body (IdMap.add x (VarCell (ref e_val)) env)
  | EFix (p, x, e) ->
      let x_var = ref (Const CUndefined) in
      let e_val = eval e (IdMap.add x (VarCell x_var) env) in begin
	  x_var := e_val;
	  e_val
	end
  | ELabel (p, l, e) -> begin
      try
	eval e env
      with Break (l', v) ->
	if l = l' then v
	else raise (Break (l', v))
    end
  | EBreak (p, l, e) ->
      raise (Break (l, eval e env))
  | ETryCatch (p, body, catch) -> begin
      try
	eval body env
      with Throw v -> apply (eval catch env) [v]
    end
  | ETryFinally (p, body, fin) -> begin
      try
	ignore (eval body env)
      with
	| Throw v -> ignore (eval fin env); raise (Throw v)
	| Break (l, v) -> ignore (eval fin env); raise (Break (l, v))
    end;
      eval fin env
  | EThrow (p, e) -> raise (Throw (eval e env))
  | ELambda (p, xs, e) -> 
      let set_arg arg x m = IdMap.add x (VarCell (ref arg)) m in
	Closure (fun args -> 
		     if (List.length args) != (List.length xs) then
		       arity_mismatch_err p xs args
		     else
		       eval e (List.fold_right2 set_arg args xs env))
  | EUpdateField (_,_,_,_,_,_) -> failwith ("Use EUpdateFieldSurface")
  | EGetField (_,_,_,_,_) -> failwith ("Use EGetFieldSurface")

and arity_mismatch_err p xs args = failwith ("Arity mismatch, supplied " ^ string_of_int (List.length args) ^ " arguments and expected " ^ string_of_int (List.length xs) ^ " at " ^ string_of_position p ^ ". Arg names were: " ^ (List.fold_right (^) (map (fun s -> " " ^ s ^ " ") xs) "") ^ ". Values were: " ^ (List.fold_right (^) (map (fun v -> " " ^ pretty_value v ^ " ") args) ""))

let rec eval_expr expr = try 
  eval expr IdMap.empty
with
  | Throw v ->
      let err_msg = 
	match v with
	  | ObjCell c ->
	      let (attrs, props) = !c in
		begin try
		  let msg = IdMap.find "message" props in
		  let msg_val = AttrMap.find Value msg in
		    (pretty_value msg_val)
		with Not_found -> (pretty_value v)
		end
	  | v -> (pretty_value v) in
	failwith ("Uncaught exception: " ^ err_msg)
  | Break (l, v) -> failwith ("Broke to top of execution, missed label: " ^ l)
