open Prelude
open Ljs_syntax
open Ljs_opt

type env = exp IdMap.t

let debug_on = false

let dprint, dprint_string, dprint_ljs = Debug.make_debug_printer ~on:debug_on "preprocess"

(* in function object #code attr, parent context is always shadowed,
   This function will recognize pattern of the new context and try to
   get 
     1) function's parameters 
     2) function's local variables.
     3)? if `arguments` keyword are not used, the whole 
         Let(_, %context...) shall be removed

   Note: parameter exp is the x_v part of Let(_,x,x_v,body), not the 
   whole Let expression.

one good example is

let (%context = {
 let (%a11 = undefined) {
 let (%x12 = %args ["0" , null]) 
   {[#proto: %parent, #class: "Object", #extensible: true,]
    'arguments' : {#value (%args) , #writable true , #configurable false},
    'x' : {#getter func (this , args) {%x12} ,
           #setter func (this , args) {%x12 := args ["0" , {[#proto: %ArrayProto,
                                                             #class: "Array",
                                                             #extensible: true,]}]}},
    'a' : {#getter func (this , args) {%a11} ,
           #setter func (this , args) 
                   {%a11 := args["0",{[#proto:%ArrayProto,
                                       #class:"Array",
                                       #extensible: true,]}]}}}}}) {...}
desugared from
function f1(x) {var a = x};

*)
let recognize_new_context exp ctx : env =
  (* get_locals will get the local IdMaps for %a11 and %x12 *)
  (*let get_locals_args exp = 
    let rec get_rec exp (locals : (string * exp) list) (args : (string * exp) list) : 
      ((string * exp) list * (string * exp) list) = 
    match exp with
    | Let (_, x, x_v, body) ->
      (match x_v with
       | Undefined _ -> 
         let local, arg = get_rec body locals args in
         (x, x_v) :: local, arg
       | GetField (_, Id (_, id), String (_, num), _) ->
         if id <> "%args" then failwith "[1]pattern assertion failed"
         else 
           let local, arg = get_rec body locals args in
           local, (x, x_v) :: arg
       | _ -> failwith "[2]pattern assertion failed"
      )
    | _ -> locals, args
    in 
    let locals, args = get_rec exp [] [] in
    List.append locals args
  in *)
  let rec strip_let exp : exp =  match exp with
    | Let (_, _, _, body) -> strip_let body
    | _ -> exp
  in 
  let rec get_id_in_getter exp = match exp with
    | Id (_, _) -> exp
    | Lambda (_, xs, body) -> get_id_in_getter body
    | Label (_, _, body) -> get_id_in_getter body
    | Break (_, _, body) -> get_id_in_getter body
    | _ -> failwith "[5] pattern assertion failed: getter contains more complicated structure"
  in 
  let rec collect_fields prop ctx : env = match prop with
    | fld, Data ({value=value; writable=_},_,_) -> 
      IdMap.add fld value ctx
    | fld, Accessor ({getter=getter; setter=_},_,_) ->
      IdMap.add fld (get_id_in_getter getter) ctx
  in 
  let rec recog_field exp ctx : env = 
    match exp with 
    | Object (_, _, props) -> 
      List.fold_right collect_fields props ctx 
    | _ -> (* assume: obj follows let *)
      Exp_util.print_ljs exp; print_newline();
      failwith "[4]pattern assertion failed:"
  in 
  let obj = strip_let exp in
  recog_field obj ctx
    
(* local context has the pattern that
 let (%context = {
     let (local1=..)
     let (local2=..)
     let (arg1=..)
     let (arg2=..)
        contextobject})
   body

this function will recognize the pattern and return the option of an exp that takes out
the contextobject and results in

 let (local1=..)
 let (local2=..)
 let (arg1=..)
 let (arg2=..)
   body

body is also returned as the second argument for convenience.

todo: arguments keyword in function
*)
let get_localcontext (let_exp : exp) : exp option =
  let rec get_let let_exp : exp =
    match let_exp with
    | Let (p, x, x_v, letb) ->
      Let (p, x, x_v, get_let letb)
    | Object (_,_,_) -> Undefined Pos.dummy
    | _ -> failwith "not context"
  in
  match let_exp with
  | Let (p, "%context", x_v, body) ->
    (try 
      Some (get_let x_v)
    with _ -> None
    )
  | _ -> None 
      
let replace_let_body let_exp new_body =
  let rec traverse let_exp : exp = match let_exp with
    | Let (p, x, x_v, body) ->
      Let (p, x, x_v, traverse body)
    | Undefined _ -> new_body 
    | _ -> failwith "replace_let_body: should not reach here"
  in 
  traverse let_exp 
  
(* these function will check if the program contains assignment to "this" or "window".
   Such assignments will create new variables silently. To be more specific, this 
   function will look for
   1. %context["window"]: code may do bad things through window
   2. %EnvCheckAssign(_, _, %this, _): code may do bad things through the alias of 'this' 
   3. passing %this to a function: code may do something like `function z(a) {a.x = 1}; z(this)`
   4. string computation in field

   5. x++, x--, ++x, --x: this will be desugared to %PostIncrement(%context, "x"), we don't have corresponding operation on S5 identifiers.
   6. with(o): code will make a new context, and we cannot decide if the expression %context["x"] should be translated to identifier x or leave it as %context["x"].

todo: in strict mode
*)
let rec eligible_for_preprocess exp : bool = 
  (*let apply_to_attr (attr : attrs) = 
    let apply_to_option (opt : exp option) : bool = match opt with
      | Some(e) -> eligible_for_preprocess e
      | None -> true
    in 
    apply_to_option attr.primval &&
    apply_to_option attr.code &&
    apply_to_option attr.proto 
  in 
  let rec apply_to_props (props : (string * prop) list) : bool =
    let handle_prop p = match p with
      | (_, Data (data, _, _)) -> 
        eligible_for_preprocess data.value
      | (_, Accessor (acc, _, _)) ->
        eligible_for_preprocess acc.getter &&
        eligible_for_preprocess acc.setter
    in
    List.for_all handle_prop props
  in *)
  let is_static_field fld = match fld with
    | String (_, _) -> true
    | _ -> 
      dprint "not eligible: find static field: %s\n%!" (Exp_util.ljs_str fld);
      false
  in 
  let rec pass_this_arg (args : exp list) = 
    (* pass "%this" as the function arguments *)
    let rec contain_this exp = match exp with
      | Id (_, id) -> 
        let res = (id = "%this") in
        if res then 
          (dprint_string "not eligible: args contains %%this\nargs: ";
           List.iter (fun l -> dprint_ljs l) args;
           dprint_string "\n"
          )
        else ();
        res
      | _ -> List.exists contain_this (child_exps exp)
    in 
    begin match args with
    | [] -> false
    | hd :: rest -> contain_this hd || pass_this_arg rest
    end 
  in 
  match exp with
  | Undefined _
  | Null _
  | String (_,_)
  | Num (_,_)
  | True _
  | False _ 
  | Id _ -> true
  | GetField (_, obj, fld, args) ->
    (match obj, fld with
    | Id(_, "%context"), String(_, "window") -> 
      dprint_string "not eligible: get window";
      false
    | Id(_, "%context"), fld -> is_static_field fld
    | _ -> 
      eligible_for_preprocess obj &&
      eligible_for_preprocess fld &&
      eligible_for_preprocess args
    )
  | App (_, f, args) -> (match f, args with
      | Id (_, "%EnvCheckAssign"), [_;_; Id(_, "%this");_] -> 
        false
        (* todo: we can translate this into s5! *)
      | Id (_, "%PostIncrement"), _ -> false
      | Id (_, "%PostDecrement"), _ -> false
      | Id (_, "%PrefixDecrement"), _ -> false
      | Id (_, "%PrefixIncrement"), _ -> false
      (* don't check internal functions like %resolvethis *)
      | Id (_, fname), args ->
        if fname.[0] = '%' then true else    
          List.for_all eligible_for_preprocess args  
      | _ -> 
        eligible_for_preprocess f && 
        List.for_all eligible_for_preprocess args &&
        (pass_this_arg args)
    )
  | _ -> List.for_all eligible_for_preprocess (child_exps exp)
  
(* this phase highly relies on the desugared patterns.
   this phase must be the first phase before all optimizations.

   recognize the following pattern:
   - %defineGlobalVar(%context, "x") 
     => let (x = undefined) ...
   - %context["x"] if x in %context
     => x or x's actual binding location
   - %context["x" = ..] if "x" in %context
     => x := ... or mutation on x's actual binding identifiers 
   - in function object: let {%context = {let..let..let { contextobj}} function-body}
         remove the %context
   - %PropAccessorCheck(%this) in top-level
     => %context
     therefore, this.x, which will be desugared to %PropAccessorCheck(%this)["x"..], will be
     translated to %context["x"]


todo: think about the pattern
    %set-property(%context, "x", 1), maybe to %context["x"=1] and then x := 1?
*)
let preprocess (e : exp) : exp =
  let rec preprocess_rec ?(in_lambda=false) (e : exp) (ctx : env) : exp = 
    match e with 
    | Seq (p, e1, e2) ->
      (match e1 with
       | App (_, Id (_, "%defineGlobalVar"), [Id(_,"%context"); String (_, id)]) ->
         dprint "find defineGlobalVar %s\n" id;
         let ctx = IdMap.add id (Undefined Pos.dummy) ctx in
         let newe2 = preprocess_rec ~in_lambda e2 ctx in
         Let (p, id, Undefined Pos.dummy, newe2)
       | _ -> 
         let newe1 = preprocess_rec ~in_lambda e1 ctx in
         let newe2 = preprocess_rec ~in_lambda e2 ctx in
         Seq (p, newe1, newe2))
    | GetField (pos, obj, fld, args) ->
      let o = preprocess_rec ~in_lambda obj ctx in
      let f = preprocess_rec ~in_lambda fld ctx in
      let a = preprocess_rec ~in_lambda args ctx in
      (match o, f with
      | Id (_, "%context"), String (_, fldstr) -> (* get fld from context *)
        (*printf "match context['%s']\n%!" fldstr;
        IdMap.iter (fun k v->printf "%s  -> %s\n%!" k (Exp_util.ljs_str v)) ctx;*)
        (try
          match IdMap.find fldstr ctx with
          | Undefined _ -> Id (Pos.dummy, fldstr)
          | Id (_,_) as id -> id
          | e -> 
            (* printf "not expecting: %s\n%!" (Exp_util.ljs_str e); *)
            e
        with Not_found -> GetField (pos, o, f, a)
        )
      | _ -> GetField (pos, o, f, a)
      )
    | SetField (pos, obj, fld, newval, args) ->
      let o = preprocess_rec ~in_lambda obj ctx in
      let f = preprocess_rec ~in_lambda fld ctx in
      let v = preprocess_rec ~in_lambda newval ctx in
      let a = preprocess_rec ~in_lambda args ctx in
      (match o, f with
       | Id (_, "%context"), String (_, fldstr) ->
         (try match IdMap.find fldstr ctx with
            | Undefined _ -> SetBang (pos, fldstr, v)
            | Id (_, id) -> SetBang (pos, id, v)
            | _ -> failwith "SetField: how could IdMap stores unrecognized exp"
          with Not_found -> SetField (pos, o, f, v, a)
         )
       | _ -> SetField (pos, o, f, v, a)
      )
    | App (pos, f, args) ->
      let f = preprocess_rec ~in_lambda f ctx in
      let args = List.map (fun x->preprocess_rec ~in_lambda x ctx) args in
      (match f, args with 
       | Id (_, "%EnvCheckAssign"), [Id (_, "%context"); String (_, id); v; _] ->
         (try match IdMap.find id ctx with
            | Undefined _ -> SetBang (pos, id, v)
            | Id (_, actual_id) -> SetBang (pos, actual_id, v)
            | _ -> failwith "EnvCheckAssign: how could IdMap stores unrecognized exp"
          with Not_found -> App (pos, f, args))
       | Id (_, "%PropAccessorCheck"), [Id (_, "%this")] ->
         if in_lambda then
           App (pos, f, args)
         else 
           Id (pos, "%context")
       | Id (p1, "%set-property"), [Id (p2, "%context"); String (p3, id); v] ->
         let newexp = SetField (p1, Id(p2, "%context"), String(p3,id), v, Null Pos.dummy) in
         (match preprocess_rec ~in_lambda newexp ctx, newexp with
          | SetField(_,_,_,_,_), SetField(_,_,_,_,_) ->
            (* cannot translate, use the original set-property exp *)
            App (pos, f, args)
          | result, _ -> result
         )
       | _ -> App (pos, f, args)
      )
    | Let (p, x, x_v, body) ->
      let x_v = preprocess_rec ~in_lambda x_v ctx in
      begin match get_localcontext e with
      | None -> (* not a new context binding in lambda *)
        (if x = "%context" then  (* rebind x, ignore the whole body *)
            e
          else 
            Let (p, x, x_v, preprocess_rec ~in_lambda body ctx))
      | Some (new_let)->
        (try
           let new_ctx = recognize_new_context x_v ctx in 
           replace_let_body new_let (preprocess_rec ~in_lambda body new_ctx)
         with Failure msg -> 
           (printf "oops, pattern error: %s\n%!" msg;
            Let (p, x, x_v, preprocess_rec ~in_lambda body ctx)
           )
        )
      end 
    | Lambda (p, xs, body) ->
      let result = preprocess_rec ~in_lambda:true body ctx in 
      Lambda (p, xs, result)
    | Undefined _ 
    | Null _ 
    | String (_, _)
    | Num (_, _)
    | True _ 
    | False _ 
    | Id (_, _)
    | Op1 (_,_,_)
    | Op2 (_,_,_,_)
    | If (_,_,_,_)
    | Label (_,_,_)
    | Object (_,_,_) 
    | GetObjAttr (_, _, _)
    | SetAttr (_,_,_,_,_)
    | GetAttr (_,_,_,_)
    | SetObjAttr (_,_,_,_)
    | DeleteField (_, _, _) 
    | OwnFieldNames (_,_)
    | SetBang (_,_,_)
    | Rec (_,_,_,_)
    | Break (_,_,_)
    | TryCatch (_,_,_)
    | TryFinally (_,_,_)
    | Throw (_,_)
    | Hint (_,_,_)
      -> optimize (fun e->preprocess_rec ~in_lambda e ctx) e
  in 
  if eligible_for_preprocess e then
    let env = IdMap.empty in
    dprint_string "eligible for preprocess, start preprocessing...\n";
    match e with 
    | Let (_, "%context", Id (_, "%nonstrictContext"), body) ->
      preprocess_rec body env
    | _ -> 
      dprint_string "the first expression is not let (%%context = ..)\n";
      dprint_string "preprocess failed. return original program\n";
      e
  else 
    (dprint_string "not eligible for preprocess, return original one\n";
     e)
