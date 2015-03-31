open Prelude
open Ljs_syntax
open Ljs_opt
open Exp_util

let debug_on = false
let dprint = Debug.make_debug_printer ~on:debug_on "fix arity"

(* take out argument declaration exp, and return ordered formal
   parameter list *)
let trim_args (exp : exp) : id list * exp =
  let get_args e =
    match e with
    | GetField (_, Id (_, "%args"), String (_, index), _) ->
      begin try
        Some (int_of_string index)
      with
        _ -> None
      end
    | _ -> None
  in
  let get_order (args : (int * id) list) : id list =
    let rec fetch (cur : int) =
      try
        let x = List.assoc cur args in
        x :: fetch (cur+1)
      with
        _ -> []
    in
    fetch 0
  in
  let args : (int * id) list ref = ref [] in
  let rec trim exp : exp =
    match exp with
    | Let (pos, x, xv, body) ->
      begin match get_args xv with
        | Some (index) ->
          args := (index, x) :: !args;
          trim body
        | None ->
          Let (pos, x, trim xv, trim body)
      end
    | Lambda (_, _, _) -> exp
    | exp -> optimize trim exp
  in
  get_order !args, trim exp

let update_args (old_xs : id list) (new_xs : id list) =
  match old_xs with
  | hd :: tl when hd = "%this" ->
    hd :: new_xs
  | _ -> old_xs

(* mkArgsObj is called on an object which has the arguments as properties.
   the following two functions will extract those arguments.
*)
let get_field_values (obj : exp) : exp list option =
  let rec get_values props = match props with
    | [] -> []
    | (s, Data({value=value}, _, _)) :: tl ->
      if is_num s then
        value :: get_values tl
      else
        get_values tl
    | (s, Accessor(_,_,_)) :: tl ->
      failwith "ArgsObj should not contain Accessor"
  in
  match obj with
  | Object (_, _, props) ->
    begin try
        Some (get_values props)
      with
        _ -> failwith (sprintf "ArgsObj pattern match failed: %s"
                         (Exp_util.ljs_str obj))
    end
  | _ -> None
    
let parse_args_obj ?(raw_obj=false) (args : exp list) : exp list option =
  match raw_obj, args with
  | false, match_this :: [App (_, Id (_, "%mkArgsObj"), [argobj])] ->
    begin match get_field_values argobj with
      | Some (lst) -> Some (match_this :: lst)
      | None -> None
    end
  | true, match_this :: [App (_, Id (_, builtin), args)]
    when builtin = "%oneArgObj" || builtin = "%twoArgObj" ->
    Some (match_this :: args)
  | true, match_this :: [argobj] ->
    begin match get_field_values argobj with
      | Some (lst) -> Some (match_this :: lst)
      | None -> None
    end
  | _ -> None

(* delete one field whose name is given by string fld *)
let delete_field (fld : string) (obj : exp) : exp =
  let rec delete (fld : string) (props : (string * prop) list) : (string * prop) list =
    match props with
    | [] -> []
    | (str, p) :: tl when str = fld -> delete fld tl
    | hd :: tl ->
      hd :: (delete fld tl)
  in
  match obj with
  | Object (p, a, props) ->
    Object (p, a, delete fld props)
  | _ -> obj

(* fix the arity for code that just uses args['0'] with binding it
   to a specific name *)
(* TODO: when apply this function to user code, it just happens to
   to be right for getters. because max_arity now returns None for
    function that does not use 'args' in body. The right thing to
    do is to explictly keep the signature as (this, args) even when
    args is not used. See fix_arity.

    fix_arity did not clean the SetField, which is wrong. fix_by_giving_name
    is doing right thing for fix_arity.
*)
let rec fix_by_giving_name ~in_env (exp : exp) : exp =
  let rec fix e = fix_by_giving_name ~in_env e in
  (*let arity_changed name = IdMap.mem fixed name in*)
  let fixable_sig (args : string list) = match args with
    | ["this"; "args"] -> true
    | _ -> false
  in
  let args_with_num exp : int option = match exp with
    (* get the number(int) in args['0'] *)
    | GetField(_, Id (_, "args"), String(_, s), _) ->
        begin try Some (int_of_string s)
          with _ -> None
        end
    | _ -> None
  in
  let max_arity exp : int option =
    let result = ref (-1) in
    let use_arg = ref false in
    let rec get_max_arity exp : unit = match exp with
      | Id (_, "args") ->
        let _ = dprint "use args alone\n" in
        use_arg := true
      | SetBang(_, "args", _) ->
        let _ = dprint "setbang args\n" in
        use_arg := true
      | GetField(_, Id(_, "args"), _, _) ->
        begin match args_with_num exp with
          | Some (n) ->
            let _ = dprint (sprintf "match args['n'] :%s\n" (ljs_str exp)) in
            if !result < n then
              result := n
          | None -> (*use arg for other property*)
            use_arg := true
        end
      | _ -> List.iter get_max_arity (child_exps exp)
    in
    begin
      get_max_arity exp;
      if !use_arg || !result = -1 then
        None
      else
        Some (!result + 1)
    end
  in
  let make_arg (n : int) : string =
    "fargsn" ^ (string_of_int n)
  in
  let make_args (total : int) : string list =
    let rec helper cur =
      if cur >= total then
        []
      else
        (make_arg cur) :: (helper (cur+1))
    in
    helper 0
  in
  let rec remove_args (exp : exp) : exp =
    (*1. remove all the let (t = args['0']), and
        2. replace all the use of args['0'] with fargsn0
    *)
    match exp with
    | GetField (_, _, _, _) ->
      begin match args_with_num exp with
        | Some (n) -> Id (Pos.dummy, make_arg n)
        | None -> exp
      end
    | _ -> optimize remove_args exp
  in
  match exp with
  | Lambda (p, xs, body) when fixable_sig xs ->
    (* good for both env and user *)
    begin match max_arity body with
      | None ->
        (* 1. make sure the variable arity is not used,like args['length'] *)
        let _ = dprint (sprintf "max arity is not found in %s\n" (ljs_str body)) in
        Lambda (p, xs, body) (*XXX: maybe no need to go deeper?*)
      | Some (n) ->
        (* 2. fix the arity *)
        let _ = dprint "fix the arity \n" in
        let newxs = "this" :: (make_args n) in
        let newbody = remove_args (fix body) in
        Lambda (p, newxs, newbody)
    end
  | App (p, Id(p0, f), args) when in_env ->
    (*this pattern only for env*)
    begin match parse_args_obj ~raw_obj:true args with
      | Some (arg_list) ->
        App (p, Id(p0, f), arg_list)
      | None ->
        let args = List.map fix args in
        App (p, Id(p0, f), args)
    end
  | Seq (p, S.Hint (p1, s, e), e2) when is_env_delimiter s ->
    Seq (p, S.Hint (p1, s, e), fix_by_giving_name ~in_env:false e2)

  | SetField (p, obj, fld, newval, arg) ->
    (* good for both env and user *)
    (* Junsong: why fixing this? Wow, really complicated story.

       If makesetter is fixed(which is used in defineGlobalVar),
       set-property will run code like this
       
         {let
             ($newVal = val)
             obj[fld = $newVal ,
                 {[#proto: null, #class: "Object", #extensible: true,]
                  '0' : {#value ($newVal) ,
                         #writable true ,
                         #configurable true}

       now, if we just same
       defineGlobalVar(context, 'a')
       set-property(context, 'a', 1)

       'a' now actually {[] '0':{#value 1...}}, instead of 1.
    *)
    begin match get_field_values arg with
      | Some (e) ->
        SetField (p, obj, fld, newval, List.nth e 0)
      | None ->
        exp
    end
  | _ -> optimize fix exp
    
let fix_arity (exp : exp) : exp =
  (* clean formal parameter *)
  let rec fix_formal_parameter ?(in_getter=false) (exp : exp) : exp =
    let fix e = fix_formal_parameter ~in_getter e in
    (* clean related %args expression *)
    let rec clean_args (fbody : exp) : exp =
      let is_arg_delete (exp : exp) : bool = match exp with
        (* match %args[delete "%new"] *)
        | DeleteField(_, Id(_, "%args"), String (_, "%new")) -> true
        | _ -> false
      in
      let rec clean_arguments (exp : exp) : exp =
        (* clean "arguments" property in context *)
        match exp with
        | Let (p, "%context", xv, body) ->
          (*let _ = dprint "start clean the arguments(if any)\n" in*)
          Let (p, "%context", clean_arguments xv, body)
        | Let (p, x, xv, body) ->
          Let (p, x, xv, clean_arguments body)
        | Object (_, _, _) -> delete_field "arguments" exp
        | Lambda (_, _, _) -> exp
        | _ -> optimize clean_arguments exp
      in
      match fbody with
      | Seq (_, e1, e2) when is_arg_delete e1 ->
        clean_arguments e2
      | _ -> fbody
    in
    match exp with
    | Lambda (pos, xs, body)
      when not in_getter && xs = ["%this"; "%args"]->
      (*let _ = dprint "find a non-getter lambda, transform it\n%!" in*)
      (* take out those Let bindings in function body *)
      let args, new_body = trim_args body in
      (* make a new formal parameter list *)
      let new_xs = update_args xs args in
      (* clean %args in the body, and "arguments" property in context(if exists)*)
      let new_body = clean_args new_body in
      Lambda (pos, new_xs, fix_formal_parameter ~in_getter new_body)
    | Lambda (pos, ["%this"; "%args"], body) when in_getter->
      (*let _ = dprint "find a getter, do not transform the formal argument\n%!" in*)
      Lambda (pos, ["%this"; "%args"], fix_formal_parameter ~in_getter:false body)
    | Object (p, attrs, props) ->
      let new_attrs = apply_to_attr fix attrs in
      let new_props = List.map
          (fun p -> match p with
             | (s, Data (data, enum, config)) ->
               s, Data ({value = fix data.value; writable=data.writable}, enum, config)
             | (s, Accessor (acc, enum, config)) ->
               s, Accessor ({getter = fix_formal_parameter ~in_getter:true acc.getter;
                             setter = fix acc.setter}, enum, config))
          props
      in
      Object (p, new_attrs, new_props)
    | _ ->
      optimize fix exp
  in
  (* clean call site *)
  let rec fix_call_site (exp : exp) : exp =
    match exp with
    | App (p, f, args) ->
      let f = fix_call_site f in
      begin match parse_args_obj args with
      | Some (arg_list) ->
        App (p, f, arg_list)
      | None ->
        let args = List.map fix_call_site args in
        App (p, f, args)
      end
    | _ -> optimize fix_call_site exp
  in
  let has_env = match get_code_after_delimiter exp with
      | None -> false
      | _ -> true
  in
  let newexp = fix_by_giving_name ~in_env:has_env exp in
  let e1 = fix_formal_parameter newexp in
  let e2 = fix_call_site e1 in
  e2

