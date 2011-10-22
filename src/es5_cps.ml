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
  | GetAttr of pos * E.pattr * cps_value * cps_value
      (* SetAttr (pos, property, object, field name, new value) *)
  | SetAttr of pos * E.pattr * cps_value * cps_value * cps_value
  | Op1 of pos * string * cps_value
  | Op2 of pos * string * cps_value * cps_value
  | DeleteField of pos * cps_value * cps_value (* pos, obj, field *)
  | SetBang of pos * id * cps_value


and cps_exp =
  | LetValue of pos * id * cps_value * cps_exp (* let binding of values to variables *)
  | RecValue of pos * id * cps_value * cps_exp (* letrec binding of values to lambdas *)
  | LetPrim of pos * id * cps_prim * cps_exp (* let binding with only primitive steps in binding *)
  | LetRetCont of id * id * cps_exp * cps_exp (* contName * argName * contBody * exp *)
  | LetExnCont of id * id * id * cps_exp * cps_exp (* contName * argName * labelName * contBody * exp *)
  | GetField of pos * cps_value * cps_value * cps_value * id * id (*pos, obj, field, args, sk, fk *)
  | SetField of pos * cps_value * cps_value * cps_value * cps_value * id * id (* pos, obj, field, new val, args, sk, fk *)
  | If of pos * cps_value * cps_exp * cps_exp
  | AppFun of pos * cps_value * id * id * cps_value list
  | AppRetCont of id  * cps_value (* contName * argName *)
  | AppExnCont of id * cps_value * id (* contName * argName * labelName *)
  | Eval of pos * cps_exp

and data_cps_value =       
    {value : cps_value;
     writable : bool; }
and accessor_cps_value =       
    {getter : cps_value;
     setter : cps_value; }
and cps_prop =
  | Data of data_cps_value * bool * bool
  | Accessor of accessor_cps_value * bool * bool
and cps_attrs =
    { primval : cps_value option;
      code : cps_value option;
      proto : cps_value option;
      klass : string;
      extensible : bool; }


let idName value = match value with
  | Id (_, id) -> id
  | _ -> failwith "expected an Id"

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
| RecValue (pos, _, _, _) -> pos
| LetPrim (pos, _, _, _) -> pos
| LetRetCont _ -> dummy_pos
| LetExnCont _ -> dummy_pos
| GetField (pos, _, _, _, _, _) -> pos
| SetField (pos, _, _, _, _, _, _) -> pos
| If (pos, _, _, _) -> pos
| AppFun (pos, _, _, _, _) -> pos
| AppRetCont _ -> dummy_pos
| AppExnCont _ -> dummy_pos
| Eval (pos, _) -> pos
let pos_of_prim (prim : cps_prim) = match prim with
| GetAttr (pos, _, _, _) -> pos
| SetAttr (pos, _, _, _, _) -> pos
| Op1 (pos, _, _) -> pos
| Op2 (pos, _, _, _) -> pos
| DeleteField (pos, _, _) -> pos
| SetBang (pos, _, _) -> pos

let pretty_print : (cps_exp -> Format.formatter -> unit) ref = ref (fun _ _ -> ())

let newVar = 
  let varIdx = ref 0 in
  (fun prefix ->
    incr varIdx;
    "@_" ^ prefix ^ (string_of_int !varIdx))
type optBinding = Nonce | LetVar of id | RecVar of id
let rec cps (exp : E.exp) 
    (letName : optBinding)
    (exnName : id) 
    (ret : cps_value -> cps_exp) : cps_exp =

  let let_or_newVar prefix = match letName with
    | Nonce -> newVar prefix 
    | LetVar id -> id 
    | RecVar id -> id in
  let let_or_recValue (pos, id, value, body) = match letName with
    | RecVar _ -> RecValue (pos, id, value, body)
    | _ -> LetValue (pos, id, value, body) in
  match exp with
    (* most of the CPS Value forms *)
    | E.Null pos -> ret (Null pos)
    | E.Undefined pos -> ret (Undefined pos)
    | E.String (pos, str) -> ret (String(pos,str))
    | E.Num (pos, value) -> ret (Num(pos,value))
    | E.True pos -> ret (True pos)
    | E.False pos -> ret (False pos)
    | E.Id (pos, id) -> ret (Id(pos,id))

    | E.App (pos, func, args) -> 
        (* because we're using n-ary functions, building the innermostRet
         * isn't a simple matter: we have to store the variable names from the
         * previous return continuations until we're ready...
         *)
        let retName = newVar "ret" in
        let retArg = newVar "x" in
        let funNameRef = ref (Id(dummy_pos,"")) in
        let argNamesRef = ref [] in
        let innermostRet : unit -> cps_exp =
          (fun () ->
            LetRetCont (retName, retArg, (ret (Id(pos,retArg))), 
                        AppFun (pos, !funNameRef, retName, exnName, (List.rev !argNamesRef)))) in
        cps func Nonce exnName (fun funName ->
          funNameRef := funName;
          (List.fold_right (fun arg (ret' : unit -> cps_exp) -> 
            (fun () -> cps arg Nonce exnName (fun name -> 
              argNamesRef := name :: !argNamesRef;
              ret' () 
             ))) args innermostRet) ())
    | E.Lambda (pos, args, body) -> 
        let lamName = let_or_newVar "lam" in
        let retName = newVar "ret" in
        let exnName = newVar "exn" in
        let_or_recValue (pos, lamName, 
                         Lambda (pos, retName, exnName, args, (cps_tail body Nonce exnName retName)),
                         ret (Id(pos,lamName)))



    (* CPS Primitive forms *)
    | E.SetBang (pos, id, value) ->
        let temp = let_or_newVar "set!Temp" in
        let retExp = ret (Id(pos,temp)) in
        cps exp Nonce exnName (fun var -> LetPrim (pos, temp, SetBang (pos, id, var), retExp))
    | E.Op1 (pos, op, exp) -> 
        let temp = let_or_newVar "op1Temp" in
        let retExp = ret (Id(pos,temp)) in
        cps exp Nonce exnName (fun var -> LetPrim (pos, temp, Op1 (pos, op, var), retExp))
    | E.Op2 (pos, op, left, right) -> 
        let temp = let_or_newVar "op2Temp" in
        let retExp = ret (Id(pos,temp)) in
        cps left Nonce exnName (fun leftVar -> 
          cps right Nonce exnName (fun rightVar ->
            LetPrim (pos, temp, Op2 (pos, op, leftVar, rightVar), retExp)))
    | E.DeleteField (pos, obj, field) -> 
        let temp = let_or_newVar "delTemp" in
        let retExp = ret (Id(pos,temp)) in
        cps obj Nonce exnName (fun objVar -> 
          cps field Nonce exnName (fun fieldVar ->
            LetPrim (pos, temp, DeleteField (pos, objVar, fieldVar), retExp)))
    | E.GetAttr (pos, prop_meta, obj, pname) -> 
        let temp = let_or_newVar "getTemp" in
        let retExp = ret (Id(pos,temp)) in
        cps obj Nonce exnName (fun objVar -> 
          cps pname Nonce exnName (fun pnameVar ->
            LetPrim (pos, temp, GetAttr (pos, prop_meta, objVar, pnameVar), retExp)))
    | E.SetAttr (pos, prop_meta, obj, pname, value) -> 
        let temp = let_or_newVar "setTemp" in
        let retExp = ret (Id(pos,temp)) in
        cps obj Nonce exnName (fun objVar -> 
          cps pname Nonce exnName (fun pnameVar ->
            cps value Nonce exnName (fun valueVar ->
              LetPrim (pos, temp, SetAttr (pos, prop_meta, objVar, pnameVar, valueVar), retExp))))

    (* CPS Expression forms *)
    | E.Hint (pos, label, exp) -> cps exp letName exnName ret
    | E.Seq (pos, first, second) -> 
      cps first Nonce exnName (fun ignored -> cps second letName exnName ret)
    | E.Let (pos, id, value, body) -> 
      cps value (LetVar id) exnName (fun ignored -> cps body letName exnName ret)
    | E.Rec (pos, id, value, body) -> 
      cps value (RecVar id) exnName (fun ignored -> cps body letName exnName ret)

    | E.If (pos, cond, trueBranch, falseBranch) -> 
        let retName = newVar "ret" in
        let retArg = newVar "x" in
        cps cond Nonce exnName (fun var -> 
          LetRetCont (retName, retArg, ret (Id(pos,retArg)),
                      If (pos, var, 
                          cps_tail trueBranch letName exnName retName, 
                          cps_tail falseBranch letName exnName retName)))


    | E.Object (pos, meta, props) ->
      let make_wrapper exp = match exp with
        | Some exp ->
            fun fbody -> (cps exp Nonce exnName (fun exp' -> (fbody (Some exp'))))
        | None ->
            fun fbody -> fbody None in
      let primval_wrapper = make_wrapper meta.E.primval in
      let code_wrapper = make_wrapper meta.E.code in
      let proto_wrapper = make_wrapper meta.E.proto in
      let cps_data { E.value= exp; E.writable= b } =
        fun fbody -> 
          cps exp Nonce exnName (fun exp' -> fbody { value=exp'; writable=b }) in
      let cps_accessor { E.getter=gexp; E.setter=sexp } =
        fun fbody ->
          cps gexp Nonce exnName (fun gexp' ->
            cps sexp Nonce exnName (fun sexp' -> fbody { getter=gexp'; setter=sexp' })) in
      let add_prop e prop' = 
        match e with
          | LetValue (pos', var, (Object (pos'', meta', props')), e) ->
              LetValue (pos', var, (Object (pos'', meta', prop'::props')), e)
          | _ -> 
            Es5_pretty.exp exp Format.std_formatter; Format.print_newline();
            (!pretty_print) e Format.std_formatter; Format.print_newline();
            failwith "CPS: add_prop called incorrectly (shouldn't happen)"
      in
      let prop_wrapper obj (s, prop) = 
        match prop with
          | E.Data (d, c, e) -> 
            cps_data d (fun d' -> add_prop obj (s, (Data (d', c, e))))
          | E.Accessor (a, c, e) ->
            cps_accessor a (fun a' -> add_prop obj (s, (Accessor (a', c, e))))
      in
      let temp = let_or_newVar "objVar" in
      primval_wrapper (fun primval' ->
        code_wrapper (fun code' ->
          proto_wrapper (fun proto' ->
            let attrs' = { primval=primval';
                           code=code';
                           proto=proto';
                           klass=meta.E.klass;
                           extensible=meta.E.extensible; } in
            let objExp = let_or_recValue (pos, temp, Object (pos, attrs', []), ret (Id(pos,temp))) in
            List.fold_left prop_wrapper objExp props)))

    | E.GetField (pos, obj, field, args) ->
      let retName = newVar "ret" in
      let retArg = newVar "x" in
      LetRetCont (retName, retArg, ret (Id(pos,retArg)),
                  cps obj Nonce exnName (fun obj' ->
                    cps field Nonce exnName (fun field' ->
                      cps args Nonce exnName (fun args' ->
                        GetField (pos, obj', field', args', exnName, retName)))))
    | E.SetField (pos, obj, field, value, args) ->
      let retName = newVar "ret" in
      let retArg = newVar "x" in
      LetRetCont (retName, retArg, ret (Id(pos,retArg)),
                  cps obj Nonce exnName (fun obj' ->
                    cps field Nonce exnName (fun field' ->
                      cps value Nonce exnName (fun value' ->
                        cps args Nonce exnName (fun args' ->
                          SetField (pos, obj', field', value', args', exnName, retName))))))

    | E.Label (pos, label, body) -> 
        let catchmeName = newVar "label" in
        let temp = newVar "labelEqTemp" in
        let newExnName = newVar "exn" in
        let argName = newVar "argX" in
        let labelArgName = newVar "labelArg" in
        LetExnCont (newExnName, argName, labelArgName,
                    LetValue (pos, catchmeName, String(pos, label),
                              LetPrim (pos, temp, Op2(pos, "stx=", Id(pos,catchmeName), Id(pos,labelArgName)),
                                       If (pos, Id(pos,temp),
                                           ret (Id(pos,argName)),
                                           AppExnCont(exnName, Id(pos,argName), labelArgName)))),
                    cps body letName newExnName ret)
    | E.Break (pos, label, value) -> 
        let labelName = newVar "label" in
        LetValue(pos, labelName, String(pos, label),
                 cps value Nonce exnName (fun var -> AppExnCont(exnName, var, labelName)))
          

    | E.TryCatch (pos, body, handler_lam) -> 
      let handler_app (var : id) : E.exp =
        E.App (E.pos_of handler_lam, handler_lam, [E.Id (pos, var)]) in
      let catchmeName = newVar "catchLabel" in
      let temp = newVar "catchEqTemp" in
      let newExnName = newVar "exn" in
      let retName = newVar "ret" in
      let argName = newVar "argX" in
      let labelArgName = newVar "labelArg" in
      LetRetCont (retName, argName, ret (Id(pos,argName)),
                  LetExnCont (newExnName, argName, labelArgName,
                              LetValue (pos, catchmeName, String(pos, "##catchMe##"),
                                        LetPrim (pos, temp, Op2(pos, "stx=", 
                                                                Id(pos,catchmeName), Id(pos,labelArgName)),
                                                 If (pos, Id(pos,temp),
                                                     cps (handler_app argName) Nonce exnName ret,
                                                     AppExnCont(exnName, Id(pos,argName), labelArgName)
                                                 ))),
                              cps_tail body letName newExnName retName))
    | E.TryFinally (pos, body, exp) -> 
      let finallyRet = newVar "finallyRet" in
      let finallyExn = newVar "finallyExn" in
      let argX = newVar "argX" in
      let labelArg = newVar "label" in
      LetRetCont (finallyRet, argX, 
                  cps exp Nonce exnName (fun ignored -> ret (Id(pos,argX))),
                  LetExnCont(finallyExn, argX, labelArg, 
                             cps exp Nonce exnName (fun ignored -> AppExnCont(exnName, Id(pos,argX), labelArg)),
                             cps_tail body letName finallyExn finallyRet))
    | E.Throw (pos, value) -> cps value Nonce exnName (fun var -> AppExnCont(exnName, var, "##catchMe##"))
          (* make the exception continuation become the return continuation *)

    | E.Eval (pos, broken) -> 
      let var = newVar "dummy" in 
      LetValue (dummy_pos, var, Null dummy_pos, ret (Id(pos,var))) 




and cps_tail (exp : E.exp) (letName : optBinding) (exnName : id) (retName : id) : cps_exp =
  let let_or_newVar prefix = match letName with
    | Nonce -> newVar prefix 
    | LetVar id -> id 
    | RecVar id -> id in
  let let_or_recValue (pos, id, value, body) = match letName with
    | RecVar _ -> RecValue (pos, id, value, body)
    | _ -> LetValue (pos, id, value, body) in
  match exp with
    (* most of the CPS Value forms *)
    | E.Null pos -> AppRetCont(retName, Null pos)
    | E.Undefined pos -> AppRetCont(retName, Undefined pos)
    | E.String (pos, str) -> AppRetCont(retName, String(pos, str))
    | E.Num (pos, value) -> AppRetCont(retName, Num(pos,value))
    | E.True pos -> AppRetCont(retName, True pos)
    | E.False pos -> AppRetCont(retName, False pos)
    | E.Id (pos, id) -> AppRetCont(retName, Id(pos,id))

    | E.App (pos, func, args) -> 
        (* because we're using n-ary functions, building the innermostRet
         * isn't a simple matter: we have to store the variable names from the
         * previous return continuations until we're ready...
         *)
        let funNameRef = ref (Id(dummy_pos,"")) in
        let argNamesRef = ref [] in
        let innermostRet () : cps_exp = AppFun (pos, !funNameRef, retName, exnName, (List.rev !argNamesRef)) in
        cps func Nonce exnName (fun funName -> 
          funNameRef := funName;
          (List.fold_right (fun arg (ret' : unit -> cps_exp) -> 
            (fun () -> cps arg Nonce exnName (fun name ->
              argNamesRef := name :: !argNamesRef;
              ret' ()))) args innermostRet) ())
    | E.Lambda (pos, args, body) -> 
        let lamName = let_or_newVar "lam" in
        let retName = newVar "ret" in
        let exnName = newVar "exn" in
        let_or_recValue (pos, lamName, Lambda (pos, retName, exnName, args, 
                                               (cps_tail body Nonce exnName retName)),
                         AppRetCont(retName, Id(pos,lamName)))



    (* CPS Primitive forms *)
    | E.SetBang (pos, id, value) ->
        let temp = let_or_newVar "set!Temp" in
        cps exp Nonce exnName (fun var -> LetPrim (pos, temp, SetBang (pos, id, var), AppRetCont(retName, Id(pos,temp))))
    | E.Op1 (pos, op, exp) -> 
        let temp = let_or_newVar "op1Temp" in
        cps exp Nonce exnName (fun var -> LetPrim (pos, temp, Op1 (pos, op, var), AppRetCont(retName, Id(pos,temp))))
    | E.Op2 (pos, op, left, right) -> 
        let temp = let_or_newVar "op2Temp" in
        cps left Nonce exnName (fun leftVar -> 
          cps right Nonce exnName (fun rightVar ->
            LetPrim (pos, temp, Op2 (pos, op, leftVar, rightVar), AppRetCont(retName, Id(pos,temp)))))
    | E.DeleteField (pos, obj, field) -> 
        let temp = let_or_newVar "delTemp" in
        cps obj Nonce exnName (fun objVar -> 
          cps field Nonce exnName (fun fieldVar ->
            LetPrim (pos, temp, DeleteField (pos, objVar, fieldVar), AppRetCont(retName, Id(pos,temp)))))
    | E.GetAttr (pos, prop_meta, obj, pname) -> 
        let temp = let_or_newVar "getTemp" in
        cps obj Nonce exnName (fun objVar -> 
          cps pname Nonce exnName (fun pnameVar ->
            LetPrim (pos, temp, GetAttr (pos, prop_meta, objVar, pnameVar), AppRetCont(retName, Id(pos,temp)))))
    | E.SetAttr (pos, prop_meta, obj, pname, value) -> 
        let temp = let_or_newVar "setTemp" in
        cps obj Nonce exnName (fun objVar -> 
          cps pname Nonce exnName (fun pnameVar ->
            cps value Nonce exnName (fun valueVar ->
              LetPrim (pos, temp, SetAttr (pos, prop_meta, objVar, pnameVar, valueVar), 
                       AppRetCont(retName, Id(pos,temp))))))

    (* CPS Expression forms *)
    | E.Hint (pos, label, exp) -> cps_tail exp letName exnName retName
    | E.Seq (pos, first, second) -> 
      cps first Nonce exnName (fun ignored -> cps_tail second letName exnName retName)
    | E.Let (pos, id, value, body) -> 
      cps value (LetVar id) exnName (fun ignored -> cps_tail body letName exnName retName)
    | E.Rec (pos, id, value, body) -> 
      cps value (RecVar id) exnName (fun ignored -> cps_tail body letName exnName retName)

    | E.If (pos, cond, trueBranch, falseBranch) -> 
      cps cond Nonce exnName
        (fun var -> (If (pos, var, 
                         cps_tail trueBranch letName exnName retName, 
                         cps_tail falseBranch letName exnName retName)))

    | E.Object (pos, meta, props) ->
      let make_wrapper exp = match exp with
        | Some exp ->
            fun fbody -> (cps exp Nonce exnName (fun exp' -> (fbody (Some exp'))))
        | None ->
            fun fbody -> fbody None in
      let primval_wrapper = make_wrapper meta.E.primval in
      let code_wrapper = make_wrapper meta.E.code in
      let proto_wrapper = make_wrapper meta.E.proto in
      let cps_data { E.value= exp; E.writable= b } =
        fun fbody -> 
          cps exp Nonce exnName (fun exp' -> fbody { value=exp'; writable=b }) in
      let cps_accessor { E.getter=gexp; E.setter=sexp } =
        fun fbody ->
          cps gexp Nonce exnName (fun gexp' ->
            cps sexp Nonce exnName (fun sexp' -> fbody { getter=gexp'; setter=sexp' })) in
      let add_prop e prop' = 
        match e with
          | LetValue (pos', var, (Object (pos'', meta', props')), e) ->
              LetValue (pos', var, (Object (pos'', meta', prop'::props')), e)
          | _ -> 
            Es5_pretty.exp exp Format.std_formatter; Format.print_newline();
            (!pretty_print) e Format.std_formatter; Format.print_newline();
            failwith "CPS: add_prop called incorrectly (shouldn't happen)"
      in
      let prop_wrapper obj (s, prop) = 
        match prop with
          | E.Data (d, c, e) -> 
            cps_data d (fun d' -> add_prop obj (s, (Data (d', c, e))))
          | E.Accessor (a, c, e) ->
            cps_accessor a (fun a' -> add_prop obj (s, (Accessor (a', c, e))))
      in
      let temp = let_or_newVar "objVar" in
      primval_wrapper (fun primval' ->
        code_wrapper (fun code' ->
          proto_wrapper (fun proto' ->
            let attrs' = { primval=primval';
                           code=code';
                           proto=proto';
                           klass=meta.E.klass;
                           extensible=meta.E.extensible; } in
            let objExp = let_or_recValue (pos, temp, Object (pos, attrs', []), AppRetCont(retName, Id(pos,temp))) in
            List.fold_left prop_wrapper objExp props)))

    | E.GetField (pos, obj, field, args) ->
      cps obj Nonce exnName (fun obj' ->
        cps field Nonce exnName (fun field' ->
          cps args Nonce exnName (fun args' ->
            GetField (pos, obj', field', args', exnName, retName))))
    | E.SetField (pos, obj, field, value, args) ->
      cps obj Nonce exnName (fun obj' ->
        cps field Nonce exnName (fun field' ->
          cps value Nonce exnName (fun value' ->
            cps args Nonce exnName (fun args' ->
              SetField (pos, obj', field', value', args', exnName, retName)))))

    | E.Label (pos, label, body) -> 
      let catchmeName = newVar "label" in
      let temp = newVar "labelEqTemp" in
      let newExnName = newVar "exn" in
      let argName = newVar "argX" in
      let labelArgName = newVar "labelArg" in
      LetExnCont (newExnName, argName, labelArgName,
                  LetValue (pos, catchmeName, String(pos, label),
                            LetPrim (pos, temp, Op2(pos, "stx=", Id(pos,catchmeName), Id(pos,labelArgName)),
                                     If (pos, Id(pos,temp),
                                         AppRetCont(retName, Id(pos,argName)),
                                         AppExnCont(exnName, Id(pos,argName), labelArgName)))),
                  cps_tail body letName newExnName retName)
    | E.Break (pos, label, value) -> 
      let labelName = newVar "label" in
      LetValue(pos, labelName, String(pos, label),
               cps value Nonce exnName (fun var -> AppExnCont(exnName, var, labelName)))
          

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
                            LetPrim (pos, temp, Op2(pos, "stx=", Id(pos,catchmeName), Id(pos,labelArgName)),
                                     If (pos, Id(pos,temp),
                                         cps_tail (handler_app argName) Nonce exnName retName,
                                         AppExnCont(exnName, Id(pos,argName), labelArgName)
                                     ))),
                  cps_tail body letName newExnName retName)
    | E.TryFinally (pos, body, exp) -> 
      let finallyRet = newVar "finallyRet" in
      let finallyExn = newVar "finallyExn" in
      let argX = newVar "argX" in
      let labelArg = newVar "label" in
      LetRetCont (finallyRet, argX, 
                  cps exp Nonce exnName (fun ignored -> AppRetCont(retName, Id(pos,argX))),
                  LetExnCont(finallyExn, argX, labelArg, 
                             cps exp Nonce exnName (fun ignored -> AppExnCont(exnName, Id(pos,argX), labelArg)),
                             cps_tail body letName finallyExn finallyRet))
    | E.Throw (pos, value) -> cps value Nonce exnName (fun var -> AppExnCont(exnName, var, "##catchMe##"))
          (* make the exception continuation become the return continuation *)

    | E.Eval (pos, broken) -> 
      let var = newVar "dummy" in 
      LetValue (dummy_pos, var, Null dummy_pos, AppRetCont(retName, Id(pos,var))) 






let rec de_cps (exp : cps_exp) : E.exp =
  match exp with
  | LetValue (pos, id, value, body) -> E.Let (pos, id, de_cps_val value, de_cps body)
  | RecValue (pos, id, value, body) -> E.Rec (pos, id, de_cps_val value, de_cps body)
  | LetPrim (pos, id, prim, body) -> E.Let(pos, id, de_cps_prim prim, de_cps body)
  | LetRetCont (contId, argId, contBody, body) -> 
    E.Let (dummy_pos, contId, E.Lambda(dummy_pos, [argId], de_cps contBody), de_cps body)
  | LetExnCont (contId, argId, labelId, contBody, body) ->
    E.Let (dummy_pos, contId, E.Lambda(dummy_pos, [argId; labelId], de_cps contBody), de_cps body)
  | GetField (pos, objId, fieldId, argsId, retId, exnId) -> 
    E.GetField(pos, de_cps_val objId, de_cps_val fieldId, de_cps_val argsId)
  | SetField (pos, objId, fieldId, valueId, argsId, retId, exnId) -> 
    E.SetField(pos, de_cps_val objId, de_cps_val fieldId, de_cps_val valueId, de_cps_val argsId)
  | If (pos, condId, trueBranch, falseBranch) -> 
    E.If(pos, de_cps_val condId, de_cps trueBranch, de_cps falseBranch)
  | AppFun (pos, funId, retId, exnId, argsIds) -> E.App(pos, de_cps_val funId,
                                                        E.Id(pos,retId) :: E.Id(pos, exnId) ::
                                                          (List.map de_cps_val argsIds))
  | AppRetCont (contName, argName) -> E.App(dummy_pos, E.Id(dummy_pos, contName), [de_cps_val argName])
  | AppExnCont (contName, argName, labelName) -> E.App(dummy_pos, E.Id(dummy_pos, contName), 
                                                       [de_cps_val argName; E.Id(dummy_pos, labelName)])
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
    let id_exp_opt id = match id with None -> None | Some id -> Some (de_cps_val id) in
    let attrs' = {E.primval = id_exp_opt attrs.primval;
                  E.code = id_exp_opt attrs.code;
                  E.proto = id_exp_opt attrs.proto;
                  E.klass = attrs.klass;
                  E.extensible = attrs.extensible} in
    let prop_wrapper (name, prop) = match prop with
      | Data(value, b1, b2) -> (name, E.Data ({E.value = de_cps_val value.value; E.writable = value.writable}, b1, b2))
      | Accessor(acc, b1, b2) -> 
        (name, E.Accessor ({E.getter = de_cps_val acc.getter; E.setter = de_cps_val acc.setter}, b1, b2)) in
    E.Object(pos, attrs', List.map prop_wrapper props)
and de_cps_prim (prim : cps_prim) : E.exp =
  match prim with
  | GetAttr (pos, prop, obj, field) -> E.GetAttr(pos, prop, de_cps_val obj, de_cps_val field)
  | SetAttr (pos, prop, obj, field, value) -> E.SetAttr(pos, prop, de_cps_val obj, de_cps_val field, de_cps_val value)
  | Op1 (pos, op, id) -> E.Op1 (pos, op, de_cps_val id)
  | Op2 (pos, op, left, right) -> E.Op2 (pos, op, de_cps_val left, de_cps_val right)
  | DeleteField (pos, obj, field) -> E.DeleteField (pos, de_cps_val obj, de_cps_val field)
  | SetBang (pos, var, value) -> E.SetBang (pos, var, de_cps_val value)

