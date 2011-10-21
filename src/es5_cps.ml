open Prelude
module E = Es5_syntax

type cps_value =
  | Null of pos
  | Undefined of pos
  | String of pos * string
  | Num of pos * float
  | True of pos
  | False of pos
  | Id of pos * id
  | Object of pos * cps_attrs * (string * cps_prop) list
      (* GetAttr (pos, property, object, field name) *)
  | Lambda of pos * id * id * id list * cps_exp


and cps_prim =
  | GetAttr of pos * E.pattr * id * id
      (* SetAttr (pos, property, object, field name, new value) *)
  | SetAttr of pos * E.pattr * id * id * id
  | Op1 of pos * string * id
  | Op2 of pos * string * id * id
  | DeleteField of pos * id * id (* pos, obj, field *)
  | SetBang of pos * id * id


and cps_exp =
  | LetValue of pos * id * cps_value * cps_exp (* let binding of values to variables *)
  | LetPrim of pos * id * cps_prim * cps_exp (* let binding with only primitive steps in binding *)
  | LetRetCont of id * id * cps_exp * cps_exp (* contName * argName * contBody * exp *)
  | LetExnCont of id * id * id * cps_exp * cps_exp (* contName * argName * labelName * contBody * exp *)
  | GetField of pos * id * id * id * id * id (*pos, obj, field, args, sk, fk *)
  | SetField of pos * id * id * id * id * id * id (* pos, obj, field, new val, args, sk, fk *)
  | If of pos * id * cps_exp * cps_exp
  | AppFun of pos * id * id * id * id list
  | AppRetCont of id  * id (* contName * argName *)
  | AppExnCont of id * id * id (* contName * argName * labelName *)
  | Rec of pos * id * id * cps_exp
  | Eval of pos * cps_exp

and data_cps_value =       
    {value : id;
     writable : bool; }
and accessor_cps_value =       
    {getter : id;
     setter : id; }
and cps_prop =
  | Data of data_cps_value * bool * bool
  | Accessor of accessor_cps_value * bool * bool
and cps_attrs =
    { primval : id option;
      code : id option;
      proto : id option;
      klass : string;
      extensible : bool; }



let pos_of_val (value : cps_value) = match value with
| Null pos -> pos
| Undefined pos -> pos
| String (pos, _) -> pos
| Num (pos, _) -> pos
| True pos -> pos
| False pos -> pos
| Id (pos, _) -> pos
| Object (pos, _, _) -> pos
| Lambda (pos, _, _, _, _) -> pos
let pos_of_exp (exp : cps_exp) = match exp with
| LetValue (pos, _, _, _) -> pos
| LetPrim (pos, _, _, _) -> pos
| LetRetCont _ -> dummy_pos
| LetExnCont _ -> dummy_pos
| GetField (pos, _, _, _, _, _) -> pos
| SetField (pos, _, _, _, _, _, _) -> pos
| If (pos, _, _, _) -> pos
| AppFun (pos, _, _, _, _) -> pos
| AppRetCont _ -> dummy_pos
| AppExnCont _ -> dummy_pos
| Rec (pos, _, _, _) -> pos
| Eval (pos, _) -> pos
let pos_of_prim (prim : cps_prim) = match prim with
| GetAttr (pos, _, _, _) -> pos
| SetAttr (pos, _, _, _, _) -> pos
| Op1 (pos, _, _) -> pos
| Op2 (pos, _, _, _) -> pos
| DeleteField (pos, _, _) -> pos
| SetBang (pos, _, _) -> pos

let newVar = 
  let varIdx = ref 0 in
  (fun prefix ->
    incr varIdx;
    "@_" ^ prefix ^ (string_of_int !varIdx))
let rec cps (exp : E.exp) 
    (exnName : id) 
    (ret : id -> cps_exp) : cps_exp =

  match exp with
    (* most of the CPS Value forms *)
    | E.Null pos -> 
	let var = newVar "null" in LetValue (pos, var, Null pos, ret var)
    | E.Undefined pos -> 
	let var = newVar "undef" in LetValue (pos, var, Undefined pos, ret var)
    | E.String (pos, str) -> 
	let var = newVar "string" in LetValue (pos, var, String (pos, str), ret var)
    | E.Num (pos, value) -> 
	let var = newVar "num" in LetValue (pos, var, Num (pos, value), ret var)
    | E.True pos -> 
	let var = newVar "true" in LetValue (pos, var, True pos, ret var)
    | E.False pos -> 
	let var = newVar "false" in LetValue (pos, var, False pos, ret var)
    | E.Id (pos, id) -> ret id

    | E.App (pos, func, args) -> 
	(* because we're using n-ary functions, building the innermostRet
	 * isn't a simple matter: we have to store the variable names from the
	 * previous return continuations until we're ready...
	 *)
	let retName = newVar "ret" in
	let funNameRef = ref "" in
	let argNamesRef = ref [] in
	let innermostRet : unit -> cps_exp =
	  (fun () ->
	    LetRetCont (retName, "x", (ret "x"), 
			AppFun (pos, !funNameRef, retName, exnName, (List.rev !argNamesRef)))) in
	cps func exnName (fun funName -> 
	  funNameRef := funName;
          (List.fold_right (fun arg (ret' : unit -> cps_exp) -> 
	    (fun () -> cps arg exnName (fun name ->
	      argNamesRef := name :: !argNamesRef;
	      ret' ()))) args innermostRet) ())
    | E.Lambda (pos, args, body) -> 
	let lamName = newVar "lam" in
	let retName = newVar "ret" in
	let exnName = newVar "exn" in
	LetValue (pos, lamName, 
                  Lambda (pos, retName, exnName, args, (cps_tail body exnName retName)),
		  ret lamName)



    (* CPS Primitive forms *)
    | E.SetBang (pos, id, value) ->
	let temp = newVar "set!Temp" in
	let retExp = ret temp in
	cps exp exnName (fun var -> LetPrim (pos, temp, SetBang (pos, id, var), retExp))
    | E.Op1 (pos, op, exp) -> 
	let temp = newVar "op1Temp" in
	let retExp = ret temp in
	cps exp exnName (fun var -> LetPrim (pos, temp, Op1 (pos, op, var), retExp))
    | E.Op2 (pos, op, left, right) -> 
	let temp = newVar "op2Temp" in
	let retExp = ret temp in
	cps left exnName (fun leftVar -> 
	  cps right exnName (fun rightVar ->
	    LetPrim (pos, temp, Op2 (pos, op, leftVar, rightVar), retExp)))
    | E.DeleteField (pos, obj, field) -> 
	let temp = newVar "delTemp" in
	let retExp = ret temp in
	cps obj exnName (fun objVar -> 
	  cps field exnName (fun fieldVar ->
	    LetPrim (pos, temp, DeleteField (pos, objVar, fieldVar), retExp)))
    | E.GetAttr (pos, prop_meta, obj, pname) -> 
	let temp = newVar "getTemp" in
	let retExp = ret temp in
	cps obj exnName (fun objVar -> 
	  cps pname exnName (fun pnameVar ->
	    LetPrim (pos, temp, GetAttr (pos, prop_meta, objVar, pnameVar), retExp)))
    | E.SetAttr (pos, prop_meta, obj, pname, value) -> 
	let temp = newVar "setTemp" in
	let retExp = ret temp in
	cps obj exnName (fun objVar -> 
	  cps pname exnName (fun pnameVar ->
	    cps value exnName (fun valueVar ->
	      LetPrim (pos, temp, SetAttr (pos, prop_meta, objVar, pnameVar, valueVar), retExp))))

    (* CPS Expression forms *)
    | E.Hint (pos, label, exp) -> cps exp exnName ret
    | E.Seq (pos, first, second) -> 
      cps first exnName (fun ignored -> cps second exnName ret)
(* cps (E.Let (pos, newVar "nonce", first, second)) exnName ret *)
    | E.Let (pos, id, value, body) -> 
      let contName = newVar "cont" in
      LetRetCont (contName, id, cps body exnName ret, 
		  cps_tail value exnName contName)
    | E.Rec (pos, id, value, body) -> (* TODO: This seems wrong *)
	cps value exnName (fun value' ->
	  Rec (pos, id, value', cps body exnName ret))

    | E.If (pos, cond, trueBranch, falseBranch) -> 
	let retName = newVar "ret" in
        cps cond exnName (fun var -> 
          LetRetCont (retName, "x", ret "x",
                      If (pos, var, 
                          cps_tail trueBranch exnName retName, 
                          cps_tail falseBranch exnName retName)))


    | E.Object (pos, meta, props) ->
      let make_wrapper exp = match exp with
        | Some exp ->
            fun fbody -> (cps exp exnName (fun exp' -> (fbody (Some exp'))))
        | None ->
            fun fbody -> fbody None in
      let primval_wrapper = make_wrapper meta.E.primval in
      let code_wrapper = make_wrapper meta.E.code in
      let proto_wrapper = make_wrapper meta.E.proto in
      let cps_data { E.value= exp; E.writable= b } =
        fun fbody -> 
          cps exp exnName (fun exp' -> fbody { value=exp'; writable=b }) in
      let cps_accessor { E.getter=gexp; E.setter=sexp } =
        fun fbody ->
          cps gexp exnName (fun gexp' ->
            cps sexp exnName (fun sexp' -> fbody { getter=gexp'; setter=sexp' })) in
      let add_prop e prop' = 
        match e with
          | LetValue (pos', var, (Object (pos'', meta', props')), e) ->
              LetValue (pos', var, (Object (pos'', meta', prop'::props')), e)
          | _ -> failwith "CPS: add_prop called incorrectly (shouldn't happen)"
      in
      let prop_wrapper obj (s, prop) = 
        match prop with
          | E.Data (d, c, e) -> 
            cps_data d (fun d' -> add_prop obj (s, (Data (d', c, e))))
          | E.Accessor (a, c, e) ->
            cps_accessor a (fun a' -> add_prop obj (s, (Accessor (a', c, e))))
      in
      let temp = newVar "objVar" in
      primval_wrapper (fun primval' ->
        code_wrapper (fun code' ->
          proto_wrapper (fun proto' ->
            let attrs' = { primval=primval';
                           code=code';
                           proto=proto';
                           klass=meta.E.klass;
                           extensible=meta.E.extensible; } in
            let objExp = LetValue (pos, temp, Object (pos, attrs', []), ret temp) in
            List.fold_left prop_wrapper objExp props)))

    | E.GetField (pos, obj, field, args) ->
      let retName = newVar "ret" in
      LetRetCont (retName, "x", ret "x",
                  cps obj exnName (fun obj' ->
                    cps field exnName (fun field' ->
                      cps args exnName (fun args' ->
                        GetField (pos, obj', field', args', exnName, retName)))))
    | E.SetField (pos, obj, field, value, args) ->
      let retName = newVar "ret" in
      LetRetCont (retName, "x", ret "x",
                  cps obj exnName (fun obj' ->
                    cps field exnName (fun field' ->
                      cps value exnName (fun value' ->
                        cps args exnName (fun args' ->
                          SetField (pos, obj', field', value', args', exnName, retName))))))

    | E.Label (pos, label, body) -> 
	let catchmeName = newVar "label" in
	let temp = newVar "labelEqTemp" in
        let newExnName = newVar "exn" in
        let argName = newVar "argX" in
        let labelArgName = newVar "labelArg" in
        LetExnCont (newExnName, argName, labelArgName,
	            LetValue (pos, catchmeName, String(pos, label),
		              LetPrim (pos, temp, Op2(pos, "stx=", catchmeName, labelArgName),
			               If (pos, temp,
				           ret argName,
				           AppExnCont(exnName, argName, labelArgName)))),
	            cps body newExnName ret)
    | E.Break (pos, label, value) -> 
	let labelName = newVar "label" in
	LetValue(pos, labelName, String(pos, label),
		 cps value exnName (fun var -> AppExnCont(exnName, var, labelName)))
	  

    | E.TryCatch (pos, body, handler_lam) -> 
      let handler_app (var : id) : E.exp =
	E.App (E.pos_of handler_lam, handler_lam, [E.Id (pos, var)]) in
      let catchmeName = newVar "catchLabel" in
      let temp = newVar "catchEqTemp" in
      let newExnName = newVar "exn" in
      let retName = newVar "ret" in
      let argName = newVar "argX" in
      let labelArgName = newVar "labelArg" in
      LetRetCont (retName, argName, ret argName,
                  LetExnCont (newExnName, argName, labelArgName,
	                      LetValue (pos, catchmeName, String(pos, "##catchMe##"),
		                        LetPrim (pos, temp, Op2(pos, "stx=", catchmeName, labelArgName),
			                         If (pos, temp,
				                     cps (handler_app argName) exnName ret,
				                     AppExnCont(exnName, argName, labelArgName)
				                 ))),
                              cps_tail body newExnName retName))
    | E.TryFinally (pos, body, exp) -> 
      let finallyRet = newVar "finallyRet" in
      let finallyExn = newVar "finallyExn" in
      let argX = newVar "argX" in
      let labelArg = newVar "label" in
      LetRetCont (finallyRet, argX, 
                  cps exp exnName (fun ignored -> ret argX),
                  LetExnCont(finallyExn, argX, labelArg, 
                             cps exp exnName (fun ignored -> AppExnCont(exnName, argX, labelArg)),
	                     cps_tail body finallyExn finallyRet))
    | E.Throw (pos, value) -> cps value exnName (fun var -> AppExnCont(exnName, var, "##catchMe##"))
	  (* make the exception continuation become the return continuation *)

    | E.Eval (pos, broken) -> 
      let var = newVar "dummy" in 
      LetValue (dummy_pos, var, Null dummy_pos, ret var) 




and cps_tail (exp : E.exp) (exnName : id) (retName : id) : cps_exp =
  match exp with
    (* most of the CPS Value forms *)
    | E.Null pos -> 
	let var = newVar "null" in LetValue (pos, var, Null pos, AppRetCont(retName, var))
    | E.Undefined pos -> 
	let var = newVar "undef" in LetValue (pos, var, Undefined pos, AppRetCont(retName, var))
    | E.String (pos, str) -> 
	let var = newVar "string" in LetValue (pos, var, String (pos, str), AppRetCont(retName, var))
    | E.Num (pos, value) -> 
	let var = newVar "num" in LetValue (pos, var, Num (pos, value), AppRetCont(retName, var))
    | E.True pos -> 
	let var = newVar "true" in LetValue (pos, var, True pos, AppRetCont(retName, var))
    | E.False pos -> 
	let var = newVar "false" in LetValue (pos, var, False pos, AppRetCont(retName, var))
    | E.Id (pos, id) -> AppRetCont(retName, id)

    | E.App (pos, func, args) -> 
	(* because we're using n-ary functions, building the innermostRet
	 * isn't a simple matter: we have to store the variable names from the
	 * previous return continuations until we're ready...
	 *)
	let funNameRef = ref "" in
	let argNamesRef = ref [] in
	let innermostRet () : cps_exp = AppFun (pos, !funNameRef, retName, exnName, (List.rev !argNamesRef)) in
	cps func exnName (fun funName -> 
	  funNameRef := funName;
          (List.fold_right (fun arg (ret' : unit -> cps_exp) -> 
	    (fun () -> cps arg exnName (fun name ->
	      argNamesRef := name :: !argNamesRef;
	      ret' ()))) args innermostRet) ())
    | E.Lambda (pos, args, body) -> 
	let lamName = newVar "lam" in
	let retName = newVar "ret" in
	let exnName = newVar "exn" in
	LetValue (pos, lamName, Lambda (pos, retName, exnName, args, 
					(cps_tail body exnName retName)),
		  AppRetCont(retName, lamName))



    (* CPS Primitive forms *)
    | E.SetBang (pos, id, value) ->
	let temp = newVar "set!Temp" in
	cps exp exnName (fun var -> LetPrim (pos, temp, SetBang (pos, id, var), AppRetCont(retName, temp)))
    | E.Op1 (pos, op, exp) -> 
	let temp = newVar "op1Temp" in
	cps exp exnName (fun var -> LetPrim (pos, temp, Op1 (pos, op, var), AppRetCont(retName, temp)))
    | E.Op2 (pos, op, left, right) -> 
	let temp = newVar "op2Temp" in
	cps left exnName (fun leftVar -> 
	  cps right exnName (fun rightVar ->
	    LetPrim (pos, temp, Op2 (pos, op, leftVar, rightVar), AppRetCont(retName, temp))))
    | E.DeleteField (pos, obj, field) -> 
	let temp = newVar "delTemp" in
	cps obj exnName (fun objVar -> 
	  cps field exnName (fun fieldVar ->
	    LetPrim (pos, temp, DeleteField (pos, objVar, fieldVar), AppRetCont(retName, temp))))
    | E.GetAttr (pos, prop_meta, obj, pname) -> 
	let temp = newVar "getTemp" in
	cps obj exnName (fun objVar -> 
	  cps pname exnName (fun pnameVar ->
	    LetPrim (pos, temp, GetAttr (pos, prop_meta, objVar, pnameVar), AppRetCont(retName, temp))))
    | E.SetAttr (pos, prop_meta, obj, pname, value) -> 
	let temp = newVar "setTemp" in
	cps obj exnName (fun objVar -> 
	  cps pname exnName (fun pnameVar ->
	    cps value exnName (fun valueVar ->
	      LetPrim (pos, temp, SetAttr (pos, prop_meta, objVar, pnameVar, valueVar), AppRetCont(retName, temp)))))

    (* CPS Expression forms *)
    | E.Hint (pos, label, exp) -> cps_tail exp exnName retName
    | E.Seq (pos, first, second) -> 
      cps first exnName (fun ignored -> cps_tail second exnName retName)
    | E.Let (pos, id, value, body) -> 
      let contName = newVar "cont" in
      LetRetCont (contName, id, cps_tail body exnName retName, 
		  cps_tail value exnName contName)
    | E.Rec (pos, id, value, body) -> (* TODO: This seems wrong *)
	cps value exnName (fun value' ->
	  Rec (pos, id, value', cps_tail body exnName retName))

    | E.If (pos, cond, trueBranch, falseBranch) -> 
      cps cond exnName
        (fun var -> (If (pos, var, 
                         cps_tail trueBranch exnName retName, 
                         cps_tail falseBranch exnName retName)))

    | E.Object (pos, meta, props) ->
      let make_wrapper exp = match exp with
        | Some exp ->
            fun fbody -> (cps exp exnName (fun exp' -> (fbody (Some exp'))))
        | None ->
            fun fbody -> fbody None in
      let primval_wrapper = make_wrapper meta.E.primval in
      let code_wrapper = make_wrapper meta.E.code in
      let proto_wrapper = make_wrapper meta.E.proto in
      let cps_data { E.value= exp; E.writable= b } =
        fun fbody -> 
          cps exp exnName (fun exp' -> fbody { value=exp'; writable=b }) in
      let cps_accessor { E.getter=gexp; E.setter=sexp } =
        fun fbody ->
          cps gexp exnName (fun gexp' ->
            cps sexp exnName (fun sexp' -> fbody { getter=gexp'; setter=sexp' })) in
      let add_prop e prop' = 
        match e with
          | LetValue (pos', var, (Object (pos'', meta', props')), e) ->
              LetValue (pos', var, (Object (pos'', meta', prop'::props')), e)
          | _ -> failwith "CPS: add_prop called incorrectly (shouldn't happen)"
      in
      let prop_wrapper obj (s, prop) = 
        match prop with
          | E.Data (d, c, e) -> 
            cps_data d (fun d' -> add_prop obj (s, (Data (d', c, e))))
          | E.Accessor (a, c, e) ->
            cps_accessor a (fun a' -> add_prop obj (s, (Accessor (a', c, e))))
      in
      let temp = newVar "objVar" in
      primval_wrapper (fun primval' ->
        code_wrapper (fun code' ->
          proto_wrapper (fun proto' ->
            let attrs' = { primval=primval';
                           code=code';
                           proto=proto';
                           klass=meta.E.klass;
                           extensible=meta.E.extensible; } in
            let objExp = LetValue (pos, temp, Object (pos, attrs', []), AppRetCont(retName, temp)) in
            List.fold_left prop_wrapper objExp props)))

    | E.GetField (pos, obj, field, args) ->
      cps obj exnName (fun obj' ->
        cps field exnName (fun field' ->
          cps args exnName (fun args' ->
            GetField (pos, obj', field', args', exnName, retName))))
    | E.SetField (pos, obj, field, value, args) ->
      cps obj exnName (fun obj' ->
        cps field exnName (fun field' ->
          cps value exnName (fun value' ->
            cps args exnName (fun args' ->
              SetField (pos, obj', field', value', args', exnName, retName)))))

    | E.Label (pos, label, body) -> 
      let catchmeName = newVar "label" in
      let temp = newVar "labelEqTemp" in
      let newExnName = newVar "exn" in
      let argName = newVar "argX" in
      let labelArgName = newVar "labelArg" in
      LetExnCont (newExnName, argName, labelArgName,
	          LetValue (pos, catchmeName, String(pos, label),
		            LetPrim (pos, temp, Op2(pos, "stx=", catchmeName, labelArgName),
			             If (pos, temp,
				         AppRetCont(retName, argName),
				         AppExnCont(exnName, argName, labelArgName)))),
	          cps_tail body newExnName retName)
    | E.Break (pos, label, value) -> 
      let labelName = newVar "label" in
      LetValue(pos, labelName, String(pos, label),
	       cps value exnName (fun var -> AppExnCont(exnName, var, labelName)))
	  

    | E.TryCatch (pos, body, handler_lam) -> 
      let handler_app (var : id) : E.exp =
	E.App (E.pos_of handler_lam, handler_lam, [E.Id (pos, var)]) in
      let catchmeName = newVar "catchLabel" in
      let temp = newVar "catchEqTemp" in
      let newExnName = newVar "exn" in
      let retName = newVar "ret" in
      let argName = newVar "argX" in
      let labelArgName = newVar "labelArg" in
      LetExnCont (newExnName, argName, labelArgName,
	          LetValue (pos, catchmeName, String(pos, "##catchMe##"),
		            LetPrim (pos, temp, Op2(pos, "stx=", catchmeName, labelArgName),
			             If (pos, temp,
				         cps_tail (handler_app argName) exnName retName,
				         AppExnCont(exnName, argName, labelArgName)
				     ))),
                  cps_tail body newExnName retName)
    | E.TryFinally (pos, body, exp) -> 
      let finallyRet = newVar "finallyRet" in
      let finallyExn = newVar "finallyExn" in
      let argX = newVar "argX" in
      let labelArg = newVar "label" in
      LetRetCont (finallyRet, argX, 
                  cps exp exnName (fun ignored -> AppRetCont(retName, argX)),
                  LetExnCont(finallyExn, argX, labelArg, 
                             cps exp exnName (fun ignored -> AppExnCont(exnName, argX, labelArg)),
	                     cps_tail body finallyExn finallyRet))
    | E.Throw (pos, value) -> cps value exnName (fun var -> AppExnCont(exnName, var, "##catchMe##"))
	  (* make the exception continuation become the return continuation *)

    | E.Eval (pos, broken) -> 
      let var = newVar "dummy" in 
      LetValue (dummy_pos, var, Null dummy_pos, AppRetCont(retName, var)) 






let rec de_cps (exp : cps_exp) : E.exp =
  match exp with
  | LetValue (pos, id, value, body) -> E.Let (pos, id, de_cps_val value, de_cps body)
  | LetPrim (pos, id, prim, body) -> E.Let(pos, id, de_cps_prim prim, de_cps body)
  | LetRetCont (contId, argId, contBody, body) -> 
    E.Let (dummy_pos, contId, E.Lambda(dummy_pos, [argId], de_cps contBody), de_cps body)
  | LetExnCont (contId, argId, labelId, contBody, body) ->
    E.Let (dummy_pos, contId, E.Lambda(dummy_pos, [argId; labelId], de_cps contBody), de_cps body)
  | GetField (pos, objId, fieldId, argsId, retId, exnId) -> 
    let id_exp id = E.Id(pos, id) in
    E.GetField(pos, id_exp objId, id_exp fieldId, id_exp argsId)
  | SetField (pos, objId, fieldId, valueId, argsId, retId, exnId) -> 
    let id_exp id = E.Id(pos, id) in
    E.SetField(pos, id_exp objId, id_exp fieldId, id_exp valueId, id_exp argsId)
  | If (pos, condId, trueBranch, falseBranch) -> 
    E.If(pos, E.Id(pos, condId), de_cps trueBranch, de_cps falseBranch)
  | AppFun (pos, funId, retId, exnId, argsIds) -> E.App(pos, E.Id(pos, funId),
                                                        List.map (fun id -> E.Id(pos, id)) (retId::exnId::argsIds))
  | AppRetCont (contName, argName) -> E.App(dummy_pos, E.Id(dummy_pos, contName), [E.Id(dummy_pos, argName)])
  | AppExnCont (contName, argName, labelName) -> E.App(dummy_pos, E.Id(dummy_pos, contName), 
                                                       [E.Id(dummy_pos, argName); E.Id(dummy_pos, labelName)])
  | Rec(pos, id, valId, body) -> E.Rec(pos, id, E.Id(pos, valId), de_cps body)
  | Eval (pos, body) -> E.Eval(pos, de_cps body)
and de_cps_val (value : cps_value) : E.exp =
  match value with
  | Null pos -> E.Null pos
  | Undefined pos -> E.Undefined pos
  | String (pos, str) -> E.String (pos, str)
  | Num (pos, num) -> E.Num (pos, num)
  | True pos -> E.True pos
  | False pos -> E.False pos
  | Id (pos, id) -> E.Id (pos, id)
  | Lambda (pos, retName, exnName, argNames, body) -> E.Lambda (pos, retName::exnName::argNames, de_cps body)
  | Object (pos, attrs, props) -> 
    let id_exp id = E.Id(pos, id) in
    let id_exp_opt id = match id with None -> None | Some id -> Some(E.Id(pos, id)) in
    let attrs' = {E.primval = id_exp_opt attrs.primval;
                  E.code = id_exp_opt attrs.code;
                  E.proto = id_exp_opt attrs.proto;
                  E.klass = attrs.klass;
                  E.extensible = attrs.extensible} in
    let prop_wrapper (name, prop) = match prop with
      | Data(value, b1, b2) -> (name, E.Data ({E.value = id_exp value.value; E.writable = value.writable}, b1, b2))
      | Accessor(acc, b1, b2) -> 
        (name, E.Accessor ({E.getter = id_exp acc.getter; E.setter = id_exp acc.setter}, b1, b2)) in
    E.Object(pos, attrs', List.map prop_wrapper props)
and de_cps_prim (prim : cps_prim) : E.exp =
  match prim with
  | GetAttr (pos, prop, obj, field) -> E.GetAttr(pos, prop, E.Id(pos, obj), E.Id(pos, field))
  | SetAttr (pos, prop, obj, field, value) -> E.SetAttr(pos, prop, E.Id(pos, obj), E.Id(pos, field), E.Id(pos, value))
  | Op1 (pos, op, id) -> E.Op1 (pos, op, E.Id(pos, id))
  | Op2 (pos, op, left, right) -> E.Op2 (pos, op, E.Id(pos, left), E.Id(pos, right))
  | DeleteField (pos, obj, field) -> E.DeleteField (pos, E.Id(pos, obj), E.Id(pos, field))
  | SetBang (pos, var, value) -> E.SetBang (pos, var, E.Id(pos, value))

