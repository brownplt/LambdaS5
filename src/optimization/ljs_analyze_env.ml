(* This file is mainly for getting information from environment.
   
   Information including:
   - get mappings of built-in javascript function names to s5 names
   - get #writable of properties of `global`
   
   Take the following env expression as an example:

   %global["Error" = %ErrorGlobalFuncObj];
   %global["Error"<#enumerable> = false];
   %global["RegExp" = %RegExpGlobalFuncObj];
   %global["RegExp"<#enumerable> = false];
   %global["NaN" = NaN];
   %global["NaN"<#enumerable> = false];
   %global["NaN"<#configurable> = false];
   %global["NaN"<#writable> = false];

   the result is a map in which:
   "Error"  -> (Id %ErrorGlobalFuncObj, true)
   "RegExp" -> (Id %RegExpGlobalFuncObj, true)
   "NaN"    -> (Num NaN, false)
*)
open Prelude
open Ljs_syntax
open Exp_util
open Ljs_opt
  
(* name -> `s5 exp` * `writable` *)
type names_t = (exp * bool) IdMap.t
type env = exp IdMap.t

(* get the field named fld_name and its corresponding #value attr from
   the object *)
let get_field_value obj fld_name : exp option =
  let rec search_field props : exp option= match props with
    | [] -> None
    | (name, Data({value=value;_}, _, _)) :: _ when name = fld_name ->
      (* match the value field, get the id in the #value from it *)
      Some value
    | _ :: tl ->
      search_field tl
  in
  match obj with
  | Object (_, _, props) -> search_field props
  | _ -> None

(* get V from  {[] "value" : {#value V, _} ...} where V is an id *)
let get_value o : exp option =
  match get_field_value o "value" with
  | Some (v) when is_Id v -> Some (v)
  | _ -> None
    
(* get V from {[] "value" : {#writable B, _} ...} where B is True or
                                                  False *)
let get_writable o : bool option =
  match get_field_value o "writable" with
  | Some (v) -> begin match v with
      | True _ -> Some true
      | False _ -> Some false
      | _ -> None
    end
  | _ -> None

let is_defineOwnProperty (e : exp) : bool =
  same_Id "%defineOwnProperty" e || same_Id "%define15Property" e

(* in Env, expressions like match %global["Infinity" = +inf] will be actually

   let ($newval = +inf)
     %global["Infinity" = $newval]

   this function will find the correct name that does not map to an id
*)
let rec get_correct_exp (id : exp) (env : env) : exp =
  match id with
  | Id (_, s) ->
    begin try match IdMap.find s env with
      | Id (_, id) as e -> get_correct_exp e env
      | Lambda (_, _, _)
      | Object (_, _, _) -> id
      | e -> e
      with _ -> failwith "get_correct_exp find free variable"
    end
  | _ -> id
           
let get_env_names (exp : exp) : names_t =
  let is_global e = same_Id "%global" e in
  let names = ref IdMap.empty in
  let rec get_rec (exp : exp) (env : env) : exp =
    let get_names e = get_rec e env in
    match exp with
    | SetAttr (_, Writable, o, String(_, fld_name), False _) when is_global o ->
      (* match %global["fld_name"<#writable> = false] *)
      begin try
        let id, _ = IdMap.find fld_name !names in
        names := IdMap.add fld_name (id, false) !names;
        exp
        with _ ->
          (* pattern %global['fld_name'<#writable>=false] is found, but the field is not found
             something wrong with the fld_name, unmap it
          *)
          (*names := IdMap.remove fld_name !names;
            exp*)
          failwith "error field name during scanning environment"
      end
    | App (_, defineProperty, [o; String(_, fld_name); obj])
      when is_global o && is_defineOwnProperty defineProperty ->
      (* match defineOwnProperty(%global, "fld_name", {[] "value":..,"writable":..}) *)
      begin match get_value obj, get_writable obj with
        | Some v, Some w ->
          let real_id = get_correct_exp v env in
          names := IdMap.add fld_name (real_id, w) !names
        | _ ->
          names := IdMap.remove fld_name !names
      end;
      exp
    | SetField (_, o, String(_, fld_name), v, _)
      when is_global o && (is_Id v || is_Num v || is_Undef v) ->
      (* match %global["RegExp" = %RegExpGlobalFuncObj]; *) 
      (* match %global["Infinity" = +inf]; *)
      let real_v = get_correct_exp v env in
      names := IdMap.add fld_name (real_v, true) !names;
      exp
    | Let (_, x, xv, body) ->
      let env = IdMap.add x xv env in
      get_rec body env
    | Rec (_, x, xv, body) ->
      let env = IdMap.add x xv env in
      get_rec body env
    | _ -> optimize get_names exp
  in
  let _ = get_rec exp IdMap.empty in
  ! names
