open Prelude
open Ljs_syntax
open Ljs_opt

type env = exp IdMap.t

let debug_on = true

let dprint, dprint_string, dprint_ljs = Debug.make_debug_printer ~on:debug_on "preprocess"

(* 
   This phase will try to undo the global variable wrapping, i.e. make %context['var'] 
   to `var`. 

   This phase needs to know all global variable names before the actual transformation.

   this phase should only work in strict mode. In non-strict mode, code like
   function(a) {this.x = a} will create x in global environment. 
   Creating code silently makes this phase to lose track of global variables and to do 
   transformation incorrectly. Consider the code in non-strict mode

   var bar = 2
   function foo() { this.bar = 1 }
   foo();
   bar;

   this phase will turn the last bar as identifier `bar' but leaves the `this.bar = 1` as
   it is, which is setting field `bar' of `this' object', something like 
   %set-property(%this, "bar", 1)

*)

let global_bindings =
  [("window", "%global");
   ("print", "%print");
   ("console", "%console");
   ("Array", "%ArrayGlobalFuncObj");
   ("String", "%StringGlobalFuncObj");
   ("Object", "%ObjectGlobalFuncObj");
   ("Number", "%NumberGlobalFuncObj");
   ("Boolean", "%BooleanGlobalFuncObj");
   ("Date", "%DateGlobalFuncObj");
   ("isNaN", "%isNaN");
   ("Math", "%Math");
   ("parseInt", "%parseInt");
   ("decodeURI", "%decodeURI");
   ("decodeURIComponent", "%decodeURIComponent");
   ("encodeURI", "%encodeURI");
   ("encodeURIComponent", "%encodeURIComponent");
   ("TypeError", "%TypeErrorGlobalFuncObj");
   ("ReferenceError", "%ReferenceErrorGlobalFuncObj");
   ("SyntaxError", "%SyntaxErrorGlobalFuncObj");
   ("RangeError", "%RangeErrorGlobalFuncObj");
   ("URIError", "%URIErrorGlobalFuncObj");
   ("Error", "%ErrorGlobalFuncObj");
   ("RegExp", "%RegExpGlobalFuncObj");
   ("NaN", "NaN");
   ("Infinity", "+inf");
   ("undefined", "undefined");
  ]

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
  

(* these functions will check if the program contains assignment to "this" or "window".
   Such assignments will create new variables silently. To be more specific, this 
   function will look for
   1. %context["window"]: code may do bad things through window
   2. %EnvCheckAssign(_, _, %this, _): code may do bad things through the alias of 'this' 
   3. passing %this to a function: code may do something like `function z(a) {a.x = 1}; z(this)`
   4. string computation in field

   5. x++, x--, ++x, --x: this will be desugared to %PostIncrement(%context, "x"), we don't have corresponding operation on S5 identifiers.
   
   6. with(o): strict mode does not allow "with". But here is it: code will make a new context, and
      we cannot decide if the expression %context["x"] should be translated to identifier x or leave it as %context["x"].

todo: in strict mode
*)
let rec window_free ?(toplevel=true) exp : bool =
  (* distinct top-level window and in function window *)
  (* on top level, we should prohibit: this.window; this['window']; window  *)
  (* in function: we should only prohibit window variable. Because we also
       prohibit passing this as argument, a['window'] works fine *)
  match exp with
  | GetField (_, obj, String(_, "window"), args) ->
    window_free ~toplevel args && 
    (match obj with
     | Id (_, "%context") -> dprint_string "not eligible: reference to window variable\n";
       false
     | App (_, Id (_, "%PropAccessorCheck"), [Id (_, "%this")]) -> 
       if toplevel then 
         (dprint_string "not eligible: reference window through this in top-level\n";
          false)
       else true
     | _ -> window_free ~toplevel obj)
  | Lambda (_, _, body) ->
    window_free ~toplevel:false body
  | _ -> List.for_all (fun e -> window_free ~toplevel e) (child_exps exp)

let rec eligible_for_preprocess exp : bool = 
  let is_static_field fld = match fld with
    | String (_, _) -> true
    | _ -> 
      dprint "not eligible: find static field: %s\n%!" (Exp_util.ljs_str fld);
      false
  in 
  let rec pass_this_as_arg (args_obj : exp) = 
    (* pass "this" in jscode. `this` will be desugared to function call to
       %mkArgsObj; internally produce %resolve(.., %this) is fine. *)
    match args_obj with
     | Object (_, _, props) -> 
       let rec prop_contains_this prop = match prop with
         | fld, Data({value=Id(_, "%this"); writable=_}, _, _) -> 
           dprint_string "the code pass this to a function\n";
           true
         | _ -> List.for_all eligible_for_preprocess (child_exps args_obj)
       in 
       (*dprint "check this in arg: %s" (Exp_util.ljs_str args_obj);*)
       List.exists prop_contains_this props
     | _ -> failwith "find none object in mkdArgsObj arguments"
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
    | _, String(_, "window") ->
      dprint "not eligible: try to get window: %s\n" (Exp_util.ljs_str exp);
      false
    | Id(_, "%context"), fld -> is_static_field fld
    | _ -> 
      eligible_for_preprocess obj &&
      eligible_for_preprocess fld &&
      eligible_for_preprocess args
    )
  | App (_, f, args) -> (match f, args with
      | Id (_, "%EnvCheckAssign"), [_;_; Id(_, "%this");_] -> 
        dprint_string "not eligible: make alias on %%this\n";
        false
      | Id (_, "%set-property"), [App(_, Id(_,"%ToObject"), [Id(_, "%this")]);
                                  this_fld; _] ->
        (* this['fld'] = 1=> desugar to %set-property(%ToObject(%this), 'fld', 1.)  *)
        is_static_field this_fld
        (* todo: we can translate this into s5! *)
      | Id (_, "%PostIncrement"), _ 
      | Id (_, "%PostDecrement"), _
      | Id (_, "%PrefixDecrement"), _ 
      | Id (_, "%PrefixIncrement"), _ 
        -> 
        dprint_string "not eligible: contains ++,--: not implemented the conversion\n";
        false
      (* don't check internal functions like %resolvethis *)
      | Id (_, fname), args ->
        List.for_all eligible_for_preprocess args &&
        (if fname = "%mkArgsObj" then 
           (assert ((List.length args) = 1);
            not (pass_this_as_arg (List.nth args 0)))
         else true)
      | _ -> 
        eligible_for_preprocess f && 
        List.for_all eligible_for_preprocess args
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
    (* todo: find let %context = strict or nonstrict binding and starts opt from there *)
    match e with 
    | Let (p, "%context", Id (p1, i), body) ->
      let body = preprocess_rec body env in
      Let (p, "%context", Id (p1, i), body)
    | _ -> 
      dprint_string "the first expression is not let (%%context = ..)\n";
      dprint_string "preprocess failed. return original program\n";
      e
  else 
    (dprint_string "not eligible for preprocess, return original one\n";
     e)
