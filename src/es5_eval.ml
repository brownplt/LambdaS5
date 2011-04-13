open Prelude
module S = Es5_syntax
open Es5_values
open Es5_delta

let bool b = match b with
  | true -> True
  | false -> False

let rec interp_error pos message =
  "[interp] (" ^ string_of_position pos ^ ") " ^ message

let rec apply func args = match func with
  | Closure c -> c args
  | _ -> failwith ("[interp] Applied non-function, was actually " ^ 
		     pretty_value func)

(* args is the "arguments" object *)
let rec apply_obj o this args = match o with
  | ObjCell c -> begin match !c with
      | ({ code = Some cvalue }, _) ->
	  apply cvalue [this; args]
      | _ -> Fail "Applying inapplicable object!"
  end
  | _ -> Fail "Applying non-object!"
	  

let rec get_field p obj1 obj2 field args = match obj1 with
  | Null -> Undefined (* nothing found *)
  | ObjCell c -> begin match !c with
      | { proto = pvalue; }, props ->
	 try
	   match IdMap.find field props with
             | Data ({ value = v; }, _, _) -> v
             | Accessor ({ getter = g; }, _, _) ->
	       apply_obj g obj2 (apply args [g])
             | Generic _ -> Undefined (* TODO: Check this! *)
        (* Not_found means prototype lookup is necessary *)
	 with Not_found ->
	   get_field p pvalue obj2 field args
  end
  | _ -> failwith (interp_error p 
		     "get_field received (or reached) a non-object.  The expression was (get-field " 
		   ^ pretty_value obj1 
		   ^ " " ^ pretty_value obj2 
		   ^ " " ^ field ^ ")")


(* EUpdateField-Add *)
(* ES5 8.12.5, step 6 *)
let rec add_field obj field newval = match obj with
  | ObjCell c -> begin match !c with
      | { extensible = true; } as attrs, props ->
        begin
	  c := (attrs, IdMap.add field 
            (Data ({ value = newval; writable = true; }, true, true))
	    props);
	  newval
        end
      | _ -> Undefined(* TODO: Check error in case of non-extensible *)
  end
  | _ -> failwith ("[interp] add_field given non-object.")

(* Both functions (because a property can satisfy writable and not_writable) *)
let rec writable prop = match prop with
  | Data ({ writable = true; }, _, _) -> true
  | _ -> false

let rec not_writable prop = match prop with
  | Data ({ writable = false; }, _, _) -> true
  | _ -> false

(* EUpdateField *)
(* ES5 8.12.4, 8.12.5 *)
let rec update_field obj1 obj2 field newval args = match obj1 with
    (* 8.12.4, step 4 *)
  | Null -> add_field obj2 field newval
  | ObjCell c -> begin match !c with
      | { proto = pvalue; } as attrs, props ->
        if (not (IdMap.mem field props)) then
	  (* EUpdateField-Proto *)
	  update_field pvalue obj2 field newval args
        else
	  match (IdMap.find field props) with
            | Data ({ writable = true; }, enum, config) ->
            (* This check asks how far down we are in searching *)
	      if (not (obj1 == obj2)) then
	      (* 8.12.4, last step where inherited.[[writable]] is true *)
	        add_field obj2 field newval
	      else begin
	      (* 8.12.5, step 3, changing the value of a field *)
	        c := (attrs, IdMap.add field
                  (Data ({ value = newval; writable = true }, enum, config))
		  props);
	        newval
	      end
            | Accessor ({ setter = setterv; }, enum, config) ->
	      (* 8.12.5, step 5 *)
	      apply_obj setterv obj2 (apply args [setterv])
            | _ -> Fail "Field not writable!"
  end
  | _ -> failwith ("[interp] set_field received (or found) a non-object.  The call was (set-field " ^ pretty_value obj1 ^ " " ^ pretty_value obj2 ^ " " ^ field ^ " " ^ pretty_value newval ^ ")" )

let rec get_attr attr obj field = match obj, field with
  | ObjCell c, String s -> let (attrs, props) = !c in
      if (not (IdMap.mem s props)) then
	undef
      else
	begin match (IdMap.find s props), attr with 
          | Data (_, _, config), S.Config
          | Generic (_, config), S.Config
          | Accessor (_, _, config), S.Config -> bool config
          | Data (_, enum, _), S.Enum
          | Generic (enum, _), S.Enum
          | Accessor (_, enum, _), S.Enum -> bool enum
          | Data ({ writable = b; }, _, _), S.Writable -> bool b
          | Data ({ value = v; }, _, _), S.Value -> v
          | Accessor ({ getter = gv; }, _, _), S.Getter -> gv
          | Accessor ({ setter = sv; }, _, _), S.Setter -> sv
          | _ -> failwith "bad access of attribute"
        end
  | _ -> failwith ("[interp] get-attr didn't get an object and a string.")

(*  let attr_or_false attr prop = 
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
*)
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
(* let rec set_attr attr obj field newval = match obj, field with
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
  | _ -> failwith ("[interp] set-attr didn't get an object and a string") *)

(* 8.10.5, steps 7/8 "If iscallable(getter) is false and getter is not
   undefined..." *)

and fun_obj value = match value with
  | ObjCell c -> begin match !c with
      | { code = Some (Closure cv) }, _ -> true
      | _ -> false
  end
  | Undefined -> false
  | _ -> false
	  

let rec eval exp env = match exp with
  | S.Undefined _ -> Undefined
  | S.Null _ -> Null
  | S.String (_, s) -> String s
  | S.Num (_, n) -> Num n
  | S.True _ -> True
  | S.False _ -> False
  | S.Id (p, x) -> begin
      try
	match IdMap.find x env with
	  | VarCell v -> !v
	  | _ -> failwith ("[interp] (EId) xpected a VarCell for variable " ^ x ^ 
			     " at " ^ (string_of_position p) ^ 
			     ", but found something else: " ^ pretty_value (IdMap.find x env))
      with Not_found ->
	failwith ("[interp] Unbound identifier: " ^ x ^ " in identifier lookup at " ^
		    (string_of_position p))
    end
  | S.SetBang (p, x, e) -> begin
      try
	match IdMap.find x env with
	  | VarCell v -> v := eval e env; !v
	  | _ -> failwith ("[interp] (ESet) xpected a VarCell for variable " ^ x ^ 
			     " at " ^ (string_of_position p) ^ 
			     ", but found something else.")
      with Not_found ->
	failwith ("[interp] Unbound identifier: " ^ x ^ " in set! at " ^
		    (string_of_position p))
    end
  | S.Object (p, attrs, props) -> 
    let attrsv = match attrs with
      | { S.proto = protoexp;
          S.code = codexp;
          S.extensible = ext;
          S.klass = kls; } ->
        { proto = (match protoexp with 
          | Some pexp -> eval pexp env 
          | None -> Undefined);
          code = (match codexp with
            | Some cexp -> Some (eval cexp env)
            | None -> None);
          extensible = ext;
          klass = kls} 
    in
    let eval_prop prop = match prop with
      | S.Data ({ S.value = vexp; S.writable = w; }, enum, config) ->
        Data ({ value = eval vexp env; writable = w; }, enum, config)
      | S.Accessor ({ S.getter = ge; S.setter = se; }, enum, config) ->
        Accessor ({ getter = eval ge env; setter = eval se env}, enum, config)
      | S.Generic (enum, config) -> Generic (enum, config)
    in
      let eval_prop m (name, prop) = 
	IdMap.add name (eval_prop prop) m in
	ObjCell (ref (attrsv,
		      fold_left eval_prop IdMap.empty props))
  | S.SetField (p, obj, f, v, args) ->
      let obj_value = eval obj env in
      let f_value = eval f env in
      let v_value = eval v env in
      let args_value = eval args env in begin
	match (obj_value, f_value) with
	  | (ObjCell o, String s) ->
	      update_field obj_value 
		obj_value 
		s
		v_value
		args_value
	  | _ -> failwith ("[interp] Update field didn't get an object and a string" 
			   ^ string_of_position p)
	end
  | S.GetField (p, obj, f, args) ->
      let obj_value = eval obj env in
      let f_value = eval f env in 
      let args_value = eval args env in begin
	match (obj_value, f_value) with
	  | (ObjCell o, String s) ->
	      get_field p obj_value obj_value s args_value
	  | _ -> failwith ("[interp] Get field didn't get an object and a string at " 
			   ^ string_of_position p 
			   ^ ". Instead, it got " 
			   ^ pretty_value obj_value 
			   ^ " and " 
			   ^ pretty_value f_value)
	end
  | S.DeleteField (p, obj, f) ->
      let obj_val = eval obj env in
      let f_val = eval f env in begin
	match (obj_val, f_val) with
	  | (ObjCell c, String s) -> 
(*	      let (attrs,props) = !c in
		if IdMap.mem s props 
		  && IdMap.mem "configurable" attrs
		  && (IdMap.find "configurable" attrs) == Const (CBool true)
		then begin
		  c := (attrs, IdMap.remove s props);
		  Const (CBool true)
		end
		else *) failwith "delete nyi"
	  | _ -> failwith ("[interp] DeleteField didn't get an object and string at " ^
			     string_of_position p)
	end
  | S.GetAttr (p, attr, obj, field) ->
      let obj_val = eval obj env in
      let f_val = eval field env in
	get_attr attr obj_val f_val
  | S.SetAttr (p, attr, obj, field, newval) ->
      let obj_val = eval obj env in
      let f_val = eval field env in
      let v_val = eval newval env in
(*	set_attr attr obj_val f_val v_val *)
      failwith "set_attr nyi"
  | S.Op1 (p, op, e) ->
      let e_val = eval e env in
	begin match op with
	  | _ -> failwith ("[interp] Invalid Op1 form")
	end
  | S.Op2 (p, op, e1, e2) -> 
      let e1_val = eval e1 env in
      let e2_val = eval e2 env in
	begin match op with
	  | _ -> failwith ("[interp] Invalid Op2 form")
	end
  | S.If (p, c, t, e) ->
      let c_val = eval c env in
	if (c_val = True)
	then eval t env
	else eval e env
  | S.App (p, func, args) -> 
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
  | S.Seq (p, e1, e2) -> 
      eval e1 env;
      eval e2 env
  | S.Let (p, x, e, body) ->
      let e_val = eval e env in
	eval body (IdMap.add x (VarCell (ref e_val)) env)
  | S.Rec (p, x, e, body) ->
    let x' = ref Undefined in
    let ev_val = eval e (IdMap.add x (VarCell x') env) in
    x' := ev_val;
    eval body (IdMap.add x (VarCell (ref ev_val)) env)
  | S.Label (p, l, e) -> begin
      try
	eval e env
      with Break (l', v) ->
	if l = l' then v
	else raise (Break (l', v))
    end
  | S.Break (p, l, e) ->
      raise (Break (l, eval e env))
  | S.TryCatch (p, body, catch) -> begin
      try
	eval body env
      with Throw v -> apply (eval catch env) [v]
    end
  | S.TryFinally (p, body, fin) -> begin
      try
	ignore (eval body env)
      with
	| Throw v -> ignore (eval fin env); raise (Throw v)
	| Break (l, v) -> ignore (eval fin env); raise (Break (l, v))
    end;
      eval fin env
  | S.Throw (p, e) -> raise (Throw (eval e env))
  | S.Lambda (p, xs, e) -> 
      let set_arg arg x m = IdMap.add x (VarCell (ref arg)) m in
	Closure (fun args -> 
		     if (List.length args) != (List.length xs) then
		       arity_mismatch_err p xs args
		     else
		       eval e (List.fold_right2 set_arg args xs env))

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
		  match IdMap.find "message" props with
                    | Data ({ value = msg_val; }, _, _) ->
		      (pretty_value msg_val)
                    | _ -> (pretty_value v)
		  with Not_found -> (pretty_value v)
		end
	  | v -> (pretty_value v) in
      failwith ("Uncaught exception: " ^ err_msg)
  | Break (l, v) -> failwith ("Broke to top of execution, missed label: " ^ l)
