open Prelude
module E = Es5_syntax

module Label : sig 
  type t
  val compare : t -> t -> int
  val hash : t -> int
  val equal : t -> t -> bool
  val newLabel : unit -> t
  val dummy : t
  val pretty : t -> FormatExt.printer
  val toString : t -> string
end = struct
  type t = int
  let compare = Pervasives.compare
  let hash = Hashtbl.hash
  let equal = (=)
  let newLabel =
    let labelIdx = ref 0 in
    (fun () -> incr labelIdx; !labelIdx)
  let dummy = 0
  let pretty = FormatExt.int
  let toString = string_of_int
end
module LabelMap = Map.Make(Label)

type cps_value =
  | Null of pos * Label.t
  | Undefined of pos * Label.t
  | String of pos * Label.t * string
  | Num of pos * Label.t * float
  | True of pos * Label.t
  | False of pos * Label.t
  | Id of pos * Label.t * id
  | Object of pos * Label.t * cps_attrs * (string * cps_prop) list
  | Lambda of pos * Label.t * id * id * id list * cps_exp

and cps_prim =
  | GetAttr of pos * Label.t * E.pattr * cps_value * cps_value
  | SetAttr of pos * Label.t * E.pattr * cps_value * cps_value * cps_value
  | Op1 of pos * Label.t * string * cps_value
  | Op2 of pos * Label.t * string * cps_value * cps_value
  | MutableOp1 of pos * Label.t * string * cps_value
  | DeleteField of pos * Label.t * cps_value * cps_value (* pos, obj, field *)
  | SetBang of pos * Label.t * id * cps_value

and cps_exp =
  | LetValue of pos * Label.t * id * cps_value * cps_exp (* let binding of values to variables *)
  | RecValue of pos * Label.t * id * cps_value * cps_exp (* letrec binding of values to lambdas *)
  | LetPrim of pos * Label.t * id * cps_prim * cps_exp (* let binding with only primitive steps in binding *)
  | LetRetCont of Label.t * id * id * cps_exp * cps_exp (* contName * argName * contBody * exp *)
  | LetExnCont of Label.t * id * id * id * cps_exp * cps_exp (* contName * argName * labelName * contBody * exp *)
  | If of pos * Label.t * cps_value * cps_exp * cps_exp
  | AppFun of pos * Label.t * cps_value * id * id * cps_value list
  | AppRetCont of Label.t * id * cps_value (* contName * argName *)
  | AppExnCont of Label.t * id * cps_value * cps_value (* contName * argName * labelName *)
  | Eval of pos * Label.t * cps_exp

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
    { primval : cps_value option;
      code : cps_value option;
      proto : cps_value option;
      klass : string;
      extensible : bool; }


let idName value = match value with
  | Id (_, _, id) -> id
  | _ -> failwith "expected an Id"

let pos_of_val (value : cps_value) = match value with
| Null (pos, _) -> pos
| Undefined (pos, _) -> pos
| String (pos, _, _) -> pos
| Num (pos, _, _) -> pos
| True (pos, _) -> pos
| False (pos, _) -> pos
| Id (pos, _, _) -> pos
| Object (pos, _, _, _) -> pos
| Lambda (pos, _, _, _, _, _) -> pos
let pos_of_exp (exp : cps_exp) = match exp with
| LetValue (pos, _, _, _, _) -> pos
| RecValue (pos, _, _, _, _) -> pos
| LetPrim (pos, _, _, _, _) -> pos
| LetRetCont _ -> dummy_pos
| LetExnCont _ -> dummy_pos
| If (pos, _, _, _, _) -> pos
| AppFun (pos, _, _, _, _, _) -> pos
| AppRetCont _ -> dummy_pos
| AppExnCont _ -> dummy_pos
| Eval (pos, _, _) -> pos
let pos_of_prim (prim : cps_prim) = match prim with
| GetAttr (pos, _, _, _, _) -> pos
| SetAttr (pos, _, _, _, _, _) -> pos
| Op1 (pos, _, _, _) -> pos
| Op2 (pos, _, _, _, _) -> pos
| MutableOp1 (pos, _, _, _) -> pos
| DeleteField (pos, _, _, _) -> pos
| SetBang (pos, _, _, _) -> pos

let label_of_val (value : cps_value) = match value with
| Null (_, label) -> label
| Undefined (_, label) -> label
| String (_, label, _) -> label
| Num (_, label, _) -> label
| True (_, label) -> label
| False (_, label) -> label
| Id (_, label, _) -> label
| Object (_, label, _, _) -> label
| Lambda (_, label, _, _, _, _) -> label
let label_of_exp (exp : cps_exp) = match exp with
| LetValue (_, label, _, _, _) -> label
| RecValue (_, label, _, _, _) -> label
| LetPrim (_, label, _, _, _) -> label
| LetRetCont (label, _, _, _, _) -> label
| LetExnCont (label, _, _, _, _, _) -> label
| If (_, label, _, _, _) -> label
| AppFun (_, label, _, _, _, _) -> label
| AppRetCont (label, _, _) -> label
| AppExnCont (label, _, _, _) -> label
| Eval (_, label, _) -> label
let label_of_prim (prim : cps_prim) = match prim with
| GetAttr (_, label, _, _, _) -> label
| SetAttr (_, label, _, _, _, _) -> label
| Op1 (_, label, _, _) -> label
| Op2 (_, label, _, _, _) -> label
| MutableOp1 (_, label, _, _) -> label
| DeleteField (_, label, _, _) -> label
| SetBang (_, label, _, _) -> label


let pretty_print : (cps_exp -> Format.formatter -> unit) ref = ref (fun _ _ -> ())

let newVar = 
  let varIdx = ref 0 in
  (fun prefix ->
    incr varIdx;
    "@_" ^ prefix ^ (string_of_int !varIdx))


(* let get_field pos getField : cps_value = *)
(*   (\* *)
(*    * fun getField o field params = *)
(*    *   if (o == Null) *)
(*    * 1   return Undefined *)
(*    *   else if HasOwnProperty(o, field) then *)
(*    *     if IsGetterSetter(o,field) then *)
(*    * 2     return AppFun(GetGetter(o,field), params) *)
(*    *     else *)
(*    * 3     return GetValue(o,field) *)
(*    *   else *)
(*    * 4   return get_field(GetProto(o), field, params) *)
(*    *\) *)
(*   let retName = newVar "ret" in *)
(*   let exnName = newVar "exn" in *)
(*   let objName = newVar "obj" in *)
(*   let fieldName = newVar "field" in *)
(*   let paramsName = newVar "params" in *)
(*   let id id = Id(pos, id) in *)
(*   Lambda(pos,retName, exnName, [objName; fieldName; paramsName], *)
(*          let nullName = newVar "isNull" in *)
(*          LetPrim(pos, nullName, Op2(pos, "stx=", id objName, Null pos), *)
(*                  If(pos, id nullName, *)
(*                     AppRetCont(retName, Undefined pos), (\* 1 *\) *)
(*                     let hasPropName = newVar "hasProp" in *)
(*                     LetPrim(pos, hasPropName, Op2(pos, "hasOwnProperty", id objName, id fieldName), *)
(*                             If(pos, id hasPropName, *)
(*                                (let isGetter = newVar "isGetter" in *)
(*                                 LetPrim(pos, isGetter, Op2(pos, "isAccessor", id objName, id fieldName), *)
(*                                         If(pos, id isGetter, *)
(*                                            (let getter = newVar "getter" in (\* 2 *\) *)
(*                                             LetPrim(pos, getter, GetAttr(pos, E.Getter, id objName, id fieldName), *)
(*                                                     AppFun(pos, id getter, retName, exnName, [id paramsName]))), *)
(*                                            (let value = newVar "value" in (\* 3 *\) *)
(*                                             LetPrim(pos, value, GetAttr(pos, E.Value, id objName, id fieldName), *)
(*                                               AppRetCont(retName, id value)))))), *)
(*                                (let proto = newVar "proto" in (\* 4 *\) *)
(*                                 LetPrim(pos, proto, Op1(pos, "get-proto", id objName), *)
(*                                         AppFun(pos,  *)
(*                                                id getField,  *)
(*                                                retName, exnName, *)
(*                                                [id proto;id fieldName;id paramsName])))))))) *)

(* let update_field pos updateField : cps_value = *)
(*   (\* *)
(*    * fun setField obj1 obj2 field value params = *)
(*    * if (obj1 == Null) then *)
(*    * 1 return AddField(obj2, field, value) *)
(*    * else *)
(*    *   if (!HasOwnField(obj1, field)) then *)
(*    * 2   return updateField(GetProto(obj1), obj2, field, value, params) *)
(*    *   else *)
(*    *     if (!IsGetterSetter(obj1, field)) && IsWritable(obj1, field) then *)
(*    *       if (!(obj1 == obj2)) then (!IsGetterSetter, IsWritable, !isEqual) *)
(*    * 3       return AddField(obj2, field, value) *)
(*    *       else (!IsGetterSetter, IsWritable, isEqual) *)
(*    * 4       return SetField(obj1, field, value) *)
(*    *     else  *)
(*    *       if IsGetterSetter(obj1, field) then (IsGetterSetter) *)
(*    * 5       return AppFun(GetSetter(obj1, field), params) *)
(*    *       else (!IsWritable) *)
(*    * 6       throw "Field not writable" *)
(*    *  *)
(*    * same as *)
(*    *  *)
(*    * if (obj1 == Null) then  *)
(*    *   case1 *)
(*    * else  *)
(*    *   if HasOwnField(obj1, field) then *)
(*    *     if IsGetterSetter(obj1, field) then *)
(*    *       case5 *)
(*    *     else  *)
(*    *       if IsWritable(obj1, field) then *)
(*    *         if (obj1 == obj2) then *)
(*    *           case4 *)
(*    *         else *)
(*    *           case3 *)
(*    *       else  *)
(*    *         case6 *)
(*    *   else *)
(*    *     case2 *)
(*    *\) *)
(*   let retName = newVar "ret" in *)
(*   let exnName = newVar "exn" in *)
(*   let obj1Name = newVar "obj1_" in *)
(*   let obj2Name = newVar "obj2_" in *)
(*   let fieldName = newVar "field" in *)
(*   let valueName = newVar "value" in *)
(*   let paramsName = newVar "params" in *)
(*   let id id = Id(pos, id) in *)


(*   let case1 () =  *)
(*     let addFieldName = newVar "addField" in *)
(*     LetPrim(pos, addFieldName, SetAttr(pos, E.Value, id obj2Name, id fieldName, id valueName), *)
(*             AppRetCont(retName, id addFieldName)) in *)
(*   let case2 () =  *)
(*     let proto = newVar "proto" in *)
(*     LetPrim(pos, proto, Op1(pos, "get-proto", id obj1Name), *)
(*             AppFun(pos, id updateField, *)
(*                    retName, exnName, *)
(*                    [id proto; id obj2Name; id fieldName; id valueName; id paramsName])) in *)
(*   let case3 () = case1 () in *)
(*   let case4 () = *)
(*     let addName = newVar "addField" in *)
(*     LetPrim(pos, addName,  *)
(*             SetAttr(pos, E.Value, id obj1Name, id fieldName, id valueName), *)
(*             AppRetCont(retName, id addName)) in *)
(*   let case5 () = *)
(*     let setter = newVar "setter" in *)
(*     LetPrim(pos, setter, GetAttr(pos, E.Setter, id obj1Name, id fieldName), *)
(*             AppFun(pos, id setter, retName, exnName, [id paramsName])) in *)
(*   let case6 () = *)
(*     AppExnCont(exnName, String(pos, "Field not writable"), String(pos, "##catchMe##")) in *)
(*   Lambda(pos, retName, exnName, [obj1Name; obj2Name; fieldName; valueName; paramsName], *)
(*          let nullName = newVar "isNull" in *)
(*          LetPrim(pos, nullName, Op2(pos, "stx=", id obj1Name, Null pos), *)
(*                  If(pos, id nullName, *)
(*                     case1 (), *)
(*                     let hasPropName = newVar "hasProp" in *)
(*                     let isSetter = newVar "isSetter" in *)
(*                     let isWritable = newVar "isWritable" in *)
(*                     let objEqual = newVar "areObjsEqual" in *)
(*                     LetPrim(pos, hasPropName, Op2(pos, "hasOwnProperty", id obj1Name, id fieldName), *)
(*                             If(pos, id hasPropName, *)
(*                                LetPrim(pos, isSetter, Op2(pos, "isAccessor", id obj1Name, id fieldName), *)
(*                                        If(pos, id isSetter, *)
(*                                           case5 (), *)
(*                                           LetPrim(pos, isWritable,  *)
(*                                                   GetAttr(pos, E.Writable, id obj1Name, id fieldName), *)
(*                                                   If (pos, id isWritable, *)
(*                                                       LetPrim(pos, objEqual,  *)
(*                                                               Op2(pos, "stx=", id obj1Name, id obj2Name), *)
(*                                                               If(pos, id objEqual, *)
(*                                                                  case4 (), *)
(*                                                                  case3 ())), *)
(*                                                       case6 ())))), *)
(*                                case2 ()))))) *)
    
                                  


  
let rec cps (exp : E.exp) 
    (exnName : id) 
    (ret : cps_value -> cps_exp) : cps_exp =

  (* debugging in case we hang infinitely... *)
  (* (match exp with *)
  (* | E.Null pos -> printf "Nul %s\n" (string_of_position pos) *)
  (* | E.Undefined pos -> printf "Undef %s\n" (string_of_position pos) *)
  (* | E.String (pos, _) -> printf "String %s\n" (string_of_position pos) *)
  (* | E.Num (pos, _) -> printf "Num %s\n" (string_of_position pos) *)
  (* | E.True pos -> printf "True %s\n" (string_of_position pos) *)
  (* | E.False pos -> printf "False %s\n" (string_of_position pos) *)
  (* | E.Id (pos, _) -> printf "Id %s\n" (string_of_position pos) *)
  (* | E.Object (pos, _, _) -> printf "Object %s\n" (string_of_position pos) *)
  (* | E.GetAttr (pos, _, _, _) -> printf "GetAttr %s\n" (string_of_position pos) *)
  (* | E.SetAttr (pos, _, _, _, _) -> printf "SetAttr %s\n" (string_of_position pos) *)
  (* | E.DeleteField (pos, _, _) -> printf "Delete %s\n" (string_of_position pos) *)
  (* | E.SetBang (pos, _, _) -> printf "Set! %s\n" (string_of_position pos) *)
  (* | E.Op1 (pos, _, _) -> printf "Op1 %s\n" (string_of_position pos) *)
  (* | E.Op2 (pos, _, _, _) -> printf "Op2 %s\n" (string_of_position pos) *)
  (* | E.MutableOp1 (pos, _, _) -> printf "MutableOp1 %s\n" (string_of_position pos) *)
  (* | E.If (pos, _, _, _) -> printf "If %s\n" (string_of_position pos) *)
  (* | E.App (pos, _, _) -> printf "App %s\n" (string_of_position pos) *)
  (* | E.Seq (pos, _, _) -> printf "Seq %s\n" (string_of_position pos) *)
  (* | E.Let (pos, _, _, _) -> printf "Let %s\n" (string_of_position pos) *)
  (* | E.Rec (pos, _, _, _) -> printf "Rec %s\n" (string_of_position pos) *)
  (* | E.Label (pos, _, _) -> printf "Label %s\n" (string_of_position pos) *)
  (* | E.Break (pos, _, _) -> printf "Break %s\n" (string_of_position pos) *)
  (* | E.TryCatch (pos, _, _) -> printf "TryCatch %s\n" (string_of_position pos) *)
  (* | E.TryFinally (pos, _, _) -> printf "TryFinally %s\n" (string_of_position pos) *)
  (* | E.Throw (pos, _) -> printf "Throw %s\n" (string_of_position pos) *)
  (* | E.Lambda (pos, _, _) -> printf "Lambda %s\n" (string_of_position pos) *)
  (* | E.Eval (pos, _) -> printf "Eval %s\n" (string_of_position pos) *)
  (* | E.Hint (pos, _, _) -> printf "Hint %s\n" (string_of_position pos)); *)


  match exp with
    (* most of the CPS Value forms *)
    | E.Null pos -> ret (Null (pos, Label.newLabel()))
    | E.Undefined pos -> ret (Undefined (pos, Label.newLabel()))
    | E.String (pos, str) -> ret (String(pos,Label.newLabel(),str))
    | E.Num (pos, value) -> ret (Num(pos,Label.newLabel(),value))
    | E.True pos -> ret (True (pos,Label.newLabel()))
    | E.False pos -> ret (False (pos,Label.newLabel()))
    | E.Id (pos, id) -> ret (Id(pos,Label.newLabel(),id))

    | E.App (pos, func, args) -> 
        (* because we're using n-ary functions, building the innermostRet
         * isn't a simple matter: we have to store the variable names from the
         * previous return continuations until we're ready...
         *)
      cps func exnName (fun funName ->
        let rec process_args args argNames =
          match args with
          | arg::args' -> cps arg exnName (fun arg' -> process_args args' (arg'::argNames))
          | [] -> 
            let retName = newVar "ret" in
            let retArg = newVar "x" in
            LetRetCont (Label.newLabel(), retName, retArg, ret (Id(pos,Label.newLabel(),retArg)), 
                        AppFun (pos,Label.newLabel(), funName, retName, exnName, (List.rev argNames))) in
      process_args args [])
    | E.Lambda (pos, args, body) -> 
        let retName = newVar "ret" in
        let exnName = newVar "exn" in
        ret (Lambda (pos,Label.newLabel(), retName, exnName, args, (cps_tail body exnName retName)))



    (* CPS Primitive forms *)
    | E.SetBang (pos, id, value) ->
        cps value exnName (fun var ->
          let temp = newVar "set!Temp" in
          LetPrim (pos,Label.newLabel(), temp, SetBang (pos,Label.newLabel(), id, var), 
                   ret (Id(pos,Label.newLabel(),temp))))
    | E.Op1 (pos, op, exp) -> 
        cps exp exnName (fun var ->
          match op with
          | "prevent-extension"
          | "property-names"
          | "own-property-names" ->
            let temp = newVar "mutOp1Temp" in
            LetPrim (pos,Label.newLabel(), temp, MutableOp1 (pos,Label.newLabel(), op, var), 
                     ret (Id(pos,Label.newLabel(), temp)))
          | _ -> 
            let temp = newVar "op1Temp" in
            LetPrim (pos,Label.newLabel(), temp, Op1 (pos,Label.newLabel(), op, var), 
                     ret (Id(pos,Label.newLabel(), temp))))
    | E.Op2 (pos, op, left, right) -> 
        cps left exnName (fun leftVar -> 
          cps right exnName (fun rightVar ->
            let temp = newVar "op2Temp" in
            LetPrim (pos,Label.newLabel(), temp, Op2 (pos,Label.newLabel(), op, leftVar, rightVar), 
                     ret (Id(pos,Label.newLabel(), temp)))))
    | E.DeleteField (pos, obj, field) -> 
        cps obj exnName (fun objVar -> 
          cps field exnName (fun fieldVar ->
            let temp = newVar "delTemp" in
            LetPrim (pos,Label.newLabel(), temp, DeleteField (pos,Label.newLabel(), objVar, fieldVar), 
                     ret (Id(pos,Label.newLabel(), temp)))))
    | E.GetAttr (pos, prop_meta, obj, pname) -> 
        cps obj exnName (fun objVar -> 
          cps pname exnName (fun pnameVar ->
            let temp = newVar "getTemp" in
            LetPrim (pos,Label.newLabel(), temp, GetAttr (pos,Label.newLabel(), prop_meta, objVar, pnameVar), 
                     ret (Id(pos,Label.newLabel(), temp)))))
    | E.SetAttr (pos, prop_meta, obj, pname, value) -> 
        cps obj exnName (fun objVar -> 
          cps pname exnName (fun pnameVar ->
            cps value exnName (fun valueVar ->
              let temp = newVar "setTemp" in
              LetPrim (pos,Label.newLabel(), temp, SetAttr (pos,Label.newLabel(), prop_meta, objVar, pnameVar, valueVar), 
                       ret (Id(pos,Label.newLabel(), temp))))))

    (* CPS Expression forms *)
    | E.Hint (pos, label, exp) -> cps exp exnName ret
    | E.Seq (pos, first, second) -> 
      cps first exnName (fun ignored -> cps second exnName ret)
    | E.Let (pos, id, value, body) -> 
      cps value exnName (fun value' -> LetValue(pos,Label.newLabel(), id, value', cps body exnName ret))
    | E.Rec (pos, id, value, body) -> 
      cps value exnName (fun value' -> RecValue(pos,Label.newLabel(), id, value', cps body exnName ret))

    | E.If (pos, cond, trueBranch, falseBranch) -> 
        cps cond exnName (fun var -> 
          let retName = newVar "ret" in
          let retArg = newVar "x" in
          LetRetCont (Label.newLabel(), retName, retArg, ret (Id(pos,Label.newLabel(),retArg)),
                      If (pos,Label.newLabel(), var, 
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
      let cps_data name { E.value= exp; E.writable= b } =
        fun fbody -> 
          cps exp exnName (fun exp' -> 
            let tempD = newVar ("objField_" ^ name ^ "_data") in
            LetValue(pos, Label.newLabel(), tempD, exp', fbody { value=tempD; writable=b })) in
      let cps_accessor name { E.getter=gexp; E.setter=sexp } =
        fun fbody ->
          cps gexp exnName (fun gexp' ->
            let tempG = newVar ("objField_" ^ name ^ "_getter") in
            cps sexp exnName (fun sexp' -> 
              let tempS = newVar ("objField_" ^ name ^ "_getter") in
              LetValue(pos, Label.newLabel(), tempG, gexp',
                       LetValue(pos, Label.newLabel(), tempS, sexp',
                                fbody { getter=tempG; setter=tempS })))) in
      let rec wrap_props (pos, meta, compProps) props =
        match props with
          | (s, E.Data (d, c, e))::props' ->
            cps_data s d (fun d' ->
              wrap_props (pos, meta, ((s, Data (d', c, e))::compProps)) props')
          | (s, E.Accessor (a, c, e))::props' ->
            cps_accessor s a (fun a' ->
              wrap_props (pos, meta, ((s, Accessor (a', c, e))::compProps)) props')
          | [] ->
            let temp = newVar "objVar" in
              LetValue (pos,Label.newLabel(), temp, Object(pos,Label.newLabel(), meta, List.rev compProps), 
                        ret (Id (pos,Label.newLabel(), temp))) in
      primval_wrapper (fun primval' ->
        code_wrapper (fun code' ->
          proto_wrapper (fun proto' ->
            let attrs' = { primval=primval';
                           code=code';
                           proto=proto';
                           klass=meta.E.klass;
                           extensible=meta.E.extensible; } in
           wrap_props (pos, attrs', []) props)))

    | E.GetField (pos, obj, field, args) ->
      let getField = "%getField" in
      let id id = Id(pos,Label.newLabel(), id) in
      cps obj exnName (fun obj' ->
        cps field exnName (fun field' ->
          cps args exnName (fun args' ->
            let retName = newVar "ret" in
            let argName = newVar "arg" in
            LetRetCont(Label.newLabel(), retName, argName, ret (id argName),
                       AppFun(pos,Label.newLabel(), id getField, retName, exnName, [obj'; field'; args'])))))
    | E.SetField (pos, obj, field, value, args) ->
      let updateField = "%updateField" in
      let id id = Id(pos,Label.newLabel(), id) in
      cps obj exnName (fun obj' ->
        cps field exnName (fun field' ->
          cps value exnName (fun value' ->
            cps args exnName (fun args' ->
              let retName = newVar "ret" in
              let retArg = newVar "x" in
              LetRetCont (Label.newLabel(), retName, retArg, ret (id retArg),
                          AppFun(pos,Label.newLabel(), id updateField, retName, exnName, 
                                 [obj'; obj'; field'; value'; args']))))))
    | E.Label (pos, label, body) -> 
        let newExnName = newVar "exn" in
        let argName = newVar "argX" in
        let labelArgName = newVar "labelArg" in
        let temp = newVar "labelEqTemp" in
        LetExnCont (Label.newLabel(), newExnName, argName, labelArgName,
                    LetPrim (pos,Label.newLabel(), temp, 
                             Op2(pos,Label.newLabel(), "stx=", 
                                 String(pos,Label.newLabel(), label), Id(pos,Label.newLabel(),labelArgName)),
                             If (pos,Label.newLabel(), Id(pos,Label.newLabel(),temp),
                                 ret (Id(pos,Label.newLabel(),argName)),
                                 AppExnCont(Label.newLabel(),exnName, 
                                            Id(pos,Label.newLabel(),argName), Id(pos,Label.newLabel(),labelArgName)))),
                    cps body newExnName ret)
    | E.Break (pos, label, value) -> 
      cps value exnName (fun var -> AppExnCont(Label.newLabel(), exnName, var, String(pos,Label.newLabel(),label)))
          

    | E.TryCatch (pos, body, handler_lam) -> 
      let retName = newVar "ret" in
      let argName = newVar "argX" in
      let newExnName = newVar "exn" in
      let labelArgName = newVar "labelArg" in
      let handler_app (var : id) : E.exp =
        E.App (E.pos_of handler_lam, handler_lam, [E.Id (pos, var)]) in
      let temp = newVar "catchEqTemp" in
      LetRetCont (Label.newLabel(), retName, argName, ret (Id(pos,Label.newLabel(),argName)),
                  LetExnCont (Label.newLabel(), newExnName, argName, labelArgName,
                              LetPrim (pos, Label.newLabel(), temp, Op2(pos,Label.newLabel(), "stx=", 
                                                                  String(pos,Label.newLabel(), "##catchMe##"), 
                                                                  Id(pos,Label.newLabel(),labelArgName)),
                                       If (pos,Label.newLabel(), Id(pos,Label.newLabel(),temp),
                                           cps (handler_app argName) exnName ret,
                                           AppExnCont(Label.newLabel(), exnName, 
                                                      Id(pos,Label.newLabel(),argName), Id(pos,Label.newLabel(),labelArgName))
                                       )),
                              cps_tail body newExnName retName))
    | E.TryFinally (pos, body, exp) -> 
      let finallyRet = newVar "finallyRet" in
      let argX = newVar "argX" in
      let finallyExn = newVar "finallyExn" in
      let labelArg = newVar "label" in
      LetRetCont (Label.newLabel(), finallyRet, argX, 
                  cps exp exnName (fun ignored -> ret (Id(pos,Label.newLabel(),argX))),
                  LetExnCont(Label.newLabel(), finallyExn, argX, labelArg, 
                             cps exp exnName (fun ignored -> 
                               AppExnCont(Label.newLabel(), exnName, 
                                          Id(pos,Label.newLabel(),argX), Id(pos,Label.newLabel(),labelArg))),
                             cps_tail body finallyExn finallyRet))
    | E.Throw (pos, value) -> cps value exnName (fun var -> 
      AppExnCont(Label.newLabel(), exnName, var, String(pos,Label.newLabel(),"##catchMe##")))
          (* make the exception continuation become the return continuation *)

    | E.Eval (pos, broken) -> 
      let var = newVar "dummy" in 
      LetValue (dummy_pos, Label.newLabel(), var, Null (dummy_pos, Label.newLabel()), ret (Id(pos,Label.newLabel(),var))) 




and cps_tail (exp : E.exp) (exnName : id) (retName : id) : cps_exp =
  match exp with
    (* most of the CPS Value forms *)
    | E.Null pos -> AppRetCont(Label.newLabel(), retName, Null (pos, Label.newLabel()))
    | E.Undefined pos -> AppRetCont(Label.newLabel(), retName, Undefined (pos, Label.newLabel()))
    | E.String (pos, str) -> AppRetCont(Label.newLabel(), retName, String(pos,Label.newLabel(), str))
    | E.Num (pos, value) -> AppRetCont(Label.newLabel(), retName, Num(pos,Label.newLabel(),value))
    | E.True pos -> AppRetCont(Label.newLabel(), retName, True (pos,Label.newLabel()))
    | E.False pos -> AppRetCont(Label.newLabel(), retName, False (pos,Label.newLabel()))
    | E.Id (pos, id) -> AppRetCont(Label.newLabel(), retName, Id(pos,Label.newLabel(),id))

    | E.App (pos, func, args) -> 
        (* because we're using n-ary functions, building the innermostRet
         * isn't a simple matter: we have to store the variable names from the
         * previous return continuations until we're ready...
         *)
      cps func exnName (fun funName ->
        let rec process_args args argNames =
          match args with
          | arg::args' -> cps arg exnName (fun arg' -> process_args args' (arg'::argNames))
          | [] -> AppFun (pos,Label.newLabel(), funName, retName, exnName, (List.rev argNames)) in
      process_args args [])
    | E.Lambda (pos, args, body) -> 
        let lamName = newVar "lam" in
        let retName = newVar "ret" in
        let exnName = newVar "exn" in
        LetValue (pos,Label.newLabel(), lamName, Lambda (pos,Label.newLabel(), retName, exnName, args, 
                                        (cps_tail body exnName retName)),
                  AppRetCont(Label.newLabel(), retName, Id(pos,Label.newLabel(),lamName)))



    (* CPS Primitive forms *)
    | E.SetBang (pos, id, value) ->
        cps exp exnName (fun var ->
          let temp = newVar "set!Temp" in
          LetPrim (pos,Label.newLabel(), temp, SetBang (pos,Label.newLabel(), id, var), AppRetCont(Label.newLabel(), retName, Id(pos,Label.newLabel(),temp))))
    | E.Op1 (pos, op, exp) -> 
        cps exp exnName (fun var ->
          match op with
          | "prevent-extension"
          | "property-names"
          | "own-property-names" ->
            let temp = newVar "mutOp1Temp" in
            LetPrim (pos,Label.newLabel(), temp, MutableOp1 (pos,Label.newLabel(), op, var), 
                     AppRetCont(Label.newLabel(), retName, Id(pos,Label.newLabel(),temp)))
          | _ -> 
            let temp = newVar "op1Temp" in
            LetPrim (pos,Label.newLabel(), temp, Op1 (pos,Label.newLabel(), op, var), 
                     AppRetCont(Label.newLabel(), retName, Id(pos,Label.newLabel(),temp))))
    | E.Op2 (pos, op, left, right) -> 
        cps left exnName (fun leftVar -> 
          cps right exnName (fun rightVar ->
            let temp = newVar "op2Temp" in
            LetPrim (pos,Label.newLabel(), temp, Op2 (pos,Label.newLabel(), op, leftVar, rightVar), AppRetCont(Label.newLabel(), retName, Id(pos,Label.newLabel(),temp)))))
    | E.DeleteField (pos, obj, field) -> 
        cps obj exnName (fun objVar -> 
          cps field exnName (fun fieldVar ->
            let temp = newVar "delTemp" in
            LetPrim (pos,Label.newLabel(), temp, DeleteField (pos,Label.newLabel(), objVar, fieldVar), AppRetCont(Label.newLabel(), retName, Id(pos,Label.newLabel(),temp)))))
    | E.GetAttr (pos, prop_meta, obj, pname) -> 
        cps obj exnName (fun objVar -> 
          cps pname exnName (fun pnameVar ->
            let temp = newVar "getTemp" in
            LetPrim (pos,Label.newLabel(), temp, GetAttr (pos,Label.newLabel(), prop_meta, objVar, pnameVar), AppRetCont(Label.newLabel(), retName, Id(pos,Label.newLabel(),temp)))))
    | E.SetAttr (pos, prop_meta, obj, pname, value) -> 
        cps obj exnName (fun objVar -> 
          cps pname exnName (fun pnameVar ->
            cps value exnName (fun valueVar ->
              let temp = newVar "setTemp" in
              LetPrim (pos,Label.newLabel(), temp, SetAttr (pos,Label.newLabel(), prop_meta, objVar, pnameVar, valueVar), 
                       AppRetCont(Label.newLabel(), retName, Id(pos,Label.newLabel(),temp))))))

    (* CPS Expression forms *)
    | E.Hint (pos, label, exp) -> cps_tail exp exnName retName
    | E.Seq (pos, first, second) -> 
      cps first exnName (fun ignored -> cps_tail second exnName retName)
    | E.Let (pos, id, value, body) -> 
      cps value exnName (fun value' -> LetValue(pos,Label.newLabel(), id, value', cps_tail body exnName retName))
    | E.Rec (pos, id, value, body) -> 
      cps value exnName (fun value' -> RecValue(pos,Label.newLabel(), id, value', cps_tail body exnName retName))


    | E.If (pos, cond, trueBranch, falseBranch) -> 
      cps cond exnName
        (fun var -> (If (pos,Label.newLabel(), var, 
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
      let cps_data name { E.value= exp; E.writable= b } =
        fun fbody -> 
          cps exp exnName (fun exp' -> 
            let tempD = newVar ("objField_" ^ name ^ "_data") in
            LetValue(pos, Label.newLabel(), tempD, exp', fbody { value=tempD; writable=b })) in
      let cps_accessor name { E.getter=gexp; E.setter=sexp } =
        fun fbody ->
          cps gexp exnName (fun gexp' ->
            let tempG = newVar ("objField_" ^ name ^ "_getter") in
            cps sexp exnName (fun sexp' -> 
              let tempS = newVar ("objField_" ^ name ^ "_getter") in
              LetValue(pos, Label.newLabel(), tempG, gexp',
                       LetValue(pos, Label.newLabel(), tempS, sexp',
                                fbody { getter=tempG; setter=tempS })))) in
      let rec wrap_props (pos, meta, compProps) props =
        match props with
          | (s, E.Data (d, c, e))::props' ->
            cps_data s d (fun d' ->
              wrap_props (pos, meta, ((s, Data (d', c, e))::compProps)) props')
          | (s, E.Accessor (a, c, e))::props' ->
            cps_accessor s a (fun a' ->
              wrap_props (pos, meta, ((s, Accessor (a', c, e))::compProps)) props')
          | [] ->
            let temp = newVar "objVar" in
              LetValue (pos,Label.newLabel(), temp, Object(pos,Label.newLabel(), meta, List.rev compProps), 
                        AppRetCont(Label.newLabel(), retName, Id (pos,Label.newLabel(),temp))) in
      primval_wrapper (fun primval' ->
        code_wrapper (fun code' ->
          proto_wrapper (fun proto' ->
            let attrs' = { primval=primval';
                           code=code';
                           proto=proto';
                           klass=meta.E.klass;
                           extensible=meta.E.extensible; } in
            wrap_props (pos, attrs', []) props)))

    | E.GetField (pos, obj, field, args) ->
      let getField = "%getField" in
      let id id = Id(pos,Label.newLabel(), id) in
      cps obj exnName (fun obj' ->
        cps field exnName (fun field' ->
          cps args exnName (fun args' ->
            AppFun(pos,Label.newLabel(), id getField, retName, exnName, [obj'; field'; args']))))
    | E.SetField (pos, obj, field, value, args) ->
      let updateField = "%updateField" in
      let id id = Id(pos,Label.newLabel(), id) in
      cps obj exnName (fun obj' ->
        cps field exnName (fun field' ->
          cps value exnName (fun value' ->
            cps args exnName (fun args' ->
              AppFun(pos,Label.newLabel(), id updateField, retName, exnName, 
                     [obj'; obj'; field'; value'; args'])))))

    | E.Label (pos, label, body) -> 
      let newExnName = newVar "exn" in
      let argName = newVar "argX" in
      let labelArgName = newVar "labelArg" in
      let temp = newVar "labelEqTemp" in
      LetExnCont (Label.newLabel(), newExnName, argName, labelArgName,
                  LetPrim (pos,Label.newLabel(), temp, Op2(pos,Label.newLabel(), "stx=", String(pos,Label.newLabel(), label), Id(pos,Label.newLabel(),labelArgName)),
                           If (pos,Label.newLabel(), Id(pos,Label.newLabel(),temp),
                               AppRetCont(Label.newLabel(), retName, Id(pos,Label.newLabel(),argName)),
                               AppExnCont(Label.newLabel(), exnName, Id(pos,Label.newLabel(),argName), Id(pos,Label.newLabel(),labelArgName)))),
                  cps_tail body newExnName retName)
    | E.Break (pos, label, value) -> 
      let labelName = newVar "label" in
      LetValue(pos,Label.newLabel(), labelName, String(pos,Label.newLabel(), label),
               cps value exnName (fun var -> AppExnCont(Label.newLabel(), exnName, var, Id(pos,Label.newLabel(),labelName))))
          

    | E.TryCatch (pos, body, handler_lam) -> 
      let newExnName = newVar "exn" in
      let argName = newVar "argX" in
      let labelArgName = newVar "labelArg" in
      let handler_app (var : id) : E.exp =
        E.App (E.pos_of handler_lam, handler_lam, [E.Id (pos, var)]) in
      let temp = newVar "catchEqTemp" in
      LetExnCont (Label.newLabel(), newExnName, argName, labelArgName,
                  LetPrim (pos,Label.newLabel(), temp, Op2(pos,Label.newLabel(), "stx=", String(pos,Label.newLabel(), "##catchMe##"), Id(pos,Label.newLabel(),labelArgName)),
                           If (pos,Label.newLabel(), Id(pos,Label.newLabel(),temp),
                               cps_tail (handler_app argName) exnName retName,
                               AppExnCont(Label.newLabel(), exnName, Id(pos,Label.newLabel(),argName), Id(pos,Label.newLabel(),labelArgName))
                           )),
                  cps_tail body newExnName retName)
    | E.TryFinally (pos, body, exp) -> 
      let finallyRet = newVar "finallyRet" in
      let argX = newVar "argX" in
      let finallyExn = newVar "finallyExn" in
      let labelArg = newVar "label" in
      LetRetCont (Label.newLabel(), finallyRet, argX, 
                  cps exp exnName (fun ignored -> AppRetCont(Label.newLabel(), retName, Id(pos,Label.newLabel(),argX))),
                  LetExnCont(Label.newLabel(), finallyExn, argX, labelArg, 
                             cps exp exnName (fun ignored -> AppExnCont(Label.newLabel(), exnName, Id(pos,Label.newLabel(),argX), Id(pos,Label.newLabel(),labelArg))),
                             cps_tail body finallyExn finallyRet))
    | E.Throw (pos, value) -> cps value exnName (fun var -> AppExnCont(Label.newLabel(), exnName, var, String(pos,Label.newLabel(),"##catchMe##")))
          (* make the exception continuation become the return continuation *)

    | E.Eval (pos, broken) -> 
      let var = newVar "dummy" in 
      LetValue (dummy_pos, Label.newLabel(), var, Null (dummy_pos, Label.newLabel()), AppRetCont(Label.newLabel(), retName, Id(pos,Label.newLabel(),var))) 







let rec de_cps (exp : cps_exp) : E.exp =
  match exp with
  | LetValue (pos, _, id, value, body) -> E.Let (pos, id, de_cps_val value, de_cps body)
  | RecValue (pos, _, id, value, body) -> E.Rec (pos, id, de_cps_val value, de_cps body)
  | LetPrim (pos, _, id, prim, body) -> E.Let(pos, id, de_cps_prim prim, de_cps body)
  | LetRetCont (_, contId, argId, contBody, body) -> 
    E.Let (dummy_pos, contId, E.Lambda(dummy_pos, [argId], de_cps contBody), de_cps body)
  | LetExnCont (_, contId, argId, labelId, contBody, body) ->
    E.Let (dummy_pos, contId, E.Lambda(dummy_pos, [argId; labelId], de_cps contBody), de_cps body)
  | If (pos, _, condId, trueBranch, falseBranch) -> 
    E.If(pos, de_cps_val condId, de_cps trueBranch, de_cps falseBranch)
  | AppFun (pos, _, funId, retId, exnId, argsIds) -> E.App(pos, de_cps_val funId,
                                                        E.Id(pos,retId) :: E.Id(pos, exnId) ::
                                                          (List.map de_cps_val argsIds))
  | AppRetCont (_, contName, argName) -> E.App(dummy_pos, E.Id(dummy_pos, contName), [de_cps_val argName])
  | AppExnCont (_, contName, argName, labelName) -> E.App(dummy_pos, E.Id(dummy_pos, contName), 
                                                       [de_cps_val argName; de_cps_val labelName])
  | Eval (pos, _, body) -> E.Eval(pos, de_cps body)
and de_cps_val (value : cps_value) : E.exp =
  match value with
  | Null (pos, _) -> E.Null pos
  | Undefined (pos, _) -> E.Undefined pos
  | String (pos, _, str) -> E.String (pos, str)
  | Num (pos, _, num) -> E.Num (pos, num)
  | True (pos, _) -> E.True pos
  | False (pos, _) -> E.False pos
  | Id (pos, _, id) -> E.Id (pos, id)
  | Lambda (pos, _, retName, exnName, argNames, body) -> E.Lambda (pos, retName::exnName::argNames, de_cps body)
  | Object (pos, _, attrs, props) -> 
    let id_exp_opt id = match id with None -> None | Some id -> Some (de_cps_val id) in
    let attrs' = {E.primval = id_exp_opt attrs.primval;
                  E.code = id_exp_opt attrs.code;
                  E.proto = id_exp_opt attrs.proto;
                  E.klass = attrs.klass;
                  E.extensible = attrs.extensible} in
    let prop_wrapper (name, prop) = match prop with
      | Data(value, config, enum) -> (name, E.Data ({E.value = E.Id(pos, value.value); E.writable = value.writable}, config, enum))
      | Accessor(acc, config, enum) -> 
        (name, E.Accessor ({E.getter = E.Id(pos,acc.getter); E.setter = E.Id(pos,acc.getter)}, config, enum)) in
    E.Object(pos, attrs', List.map prop_wrapper props)
and de_cps_prim (prim : cps_prim) : E.exp =
  match prim with
  | GetAttr (pos, _, prop, obj, field) -> E.GetAttr(pos, prop, de_cps_val obj, de_cps_val field)
  | SetAttr (pos, _, prop, obj, field, value) -> E.SetAttr(pos, prop, de_cps_val obj, de_cps_val field, de_cps_val value)
  | Op1 (pos, _, op, id) -> E.Op1 (pos, op, de_cps_val id)
  | Op2 (pos, _, op, left, right) -> E.Op2 (pos, op, de_cps_val left, de_cps_val right)
  | MutableOp1 (pos, _, op, id) -> E.Op1 (pos, op, de_cps_val id)
  | DeleteField (pos, _, obj, field) -> E.DeleteField (pos, de_cps_val obj, de_cps_val field)
  | SetBang (pos, _, var, value) -> E.SetBang (pos, var, de_cps_val value)

