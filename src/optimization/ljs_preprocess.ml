open Prelude
open Ljs_syntax
open Ljs_opt

type env = exp IdMap.t

let debug_on = false

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

let create_global_bindings () = 
  let global_internals =
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
  in  
  let rec to_map maps internals = match internals with
    | [] -> maps
    | hd :: rest ->
      to_map (IdMap.add (fst2 hd) (snd2 hd) maps) rest
  in 
  to_map IdMap.empty global_internals
    
let global_bindings = create_global_bindings ()

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
   0. strict mode
   1. %context["window"]: code may do bad things through window
   2. %EnvCheckAssign(_, _, %this, _): code may do bad things through the alias of 'this' 
      %EnvCheckAssign(_, _, {object field as this}, _): code may do bad things through the alias of 'this' 
   3. passing %this to a function: code may do something like `function z(a) {a.x = 1}; z(this)`
   4. computation string field on top level. In function computation is fine.

   5. with(o): strict mode does not allow "with". But here is how it works: code will make a new context, and
      we cannot decide if the expression %context["x"] should be translated to identifier x or leave it as %context["x"].

*)

let rec all_in_strict exp : bool = match exp with
  (* checking whether all functions are in strict mode does not work.
     because 'with' expression can appear on top level.
  *)
  | Let (_, "#strict", False _, body) -> false
  | _ -> List.for_all all_in_strict (child_exps exp)
    
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
      dprint "not eligible: find non-static field: %s\n%!" (Exp_util.ljs_str fld);
      false
  in 
  let rec contain_this_keyword toplevel (args_obj : exp) = 
    match args_obj with
    | Id (_, "%this") -> let result = toplevel && true in
      if result then (dprint_string "not eligible: make alias on %this\n"; true)
      else false
    | Lambda (_, _, body) -> contain_this_keyword false body
    | _ -> List.exists (fun e ->  contain_this_keyword toplevel e) (child_exps args_obj)
  in 
  let rec is_eligible_rec ?(toplevel=true) exp : bool = 
    let is_eligible exp = is_eligible_rec ~toplevel exp in
    match exp with
    | Undefined _
    | Null _
    | String (_,_)
    | Num (_,_)
    | True _
    | False _ 
    | Id _ -> true
    | GetField (_, obj, fld, args) ->
      let eligible_field obj fld = match obj with
        (* when obj is `this` and it is on top-level, only static field is 
           allowed; computation fields on other objects are fine. *)
        | App (_,Id(_,"%PropAccessorCheck"),[Id(_,"%this")]) -> is_static_field fld
        | _ -> true
      in 
      (* static field is not required in function *)
      is_eligible obj && is_eligible fld && is_eligible args &&
      (if toplevel then (eligible_field obj fld) else true)
    | App (_, f, args) -> (match f, args with
        | Id (_, "%EnvCheckAssign"), [_;_; Id(_, "%this");_] -> 
          false
        | Id (_, "%EnvCheckAssign"), [_;_; Object(_,_,_) as obj;_] -> 
          not (List.exists (fun x->contain_this_keyword toplevel x) (child_exps obj)) &&
          (List.for_all is_eligible args)
        | Id (_, "%set-property"), [App(_, Id(_,"%ToObject"), [Id(_, "%this")]);
                                    this_fld; arg] ->
          (* this['fld'] = 1=> desugar to %set-property(%ToObject(%this), 'fld', 1.)  *)
          is_eligible arg && (if toplevel then (is_static_field this_fld) else true)
        | Id (_, fname), args ->
          List.for_all is_eligible args &&
          (if fname = "%mkArgsObj" && toplevel then 
                      (assert ((List.length args) = 1);
                       not (contain_this_keyword toplevel (List.nth args 0)))
                    else true)
        | _ -> 
          is_eligible f && 
          List.for_all is_eligible args
      )
    | Lambda (_, _, body) ->
      is_eligible_rec ~toplevel:false body
    | _ -> List.for_all is_eligible (child_exps exp)
  in 
  all_in_strict exp && window_free exp && is_eligible_rec exp



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
*)
let pre_post_transform (op : string) (id : id) : exp option = 
  let p = Pos.dummy in 
  let make_prim op id = match op with
    | "-" -> App (p, Id(p, "%PrimSub"), [App(p, Id (p,"%ToNumber"), [Id(p,id)]); Num(p,1.)])
    | "+" -> App (p, Id(p, "%PrimAdd"), [App(p, Id (p,"%ToNumber"), [Id(p,id)]); Num(p,1.)])
    | _ -> failwith "make_prim gets unexpected argument"
  in 
  match op with
  | "%PrefixDecrement" -> (* --i => i := %PrimSub(%ToNumber(i), 1) *)
    Some (SetBang (p, id, make_prim "-" id))
  | "%PrefixIncrement" -> (* ++i => i := %PrimAdd(%ToNumber(i), 1) *)
    Some (SetBang (p, id, make_prim "+" id))
  | "%PostIncrement" -> (* i++ => let (post = i) {i := %PrimAdd(%ToNumber(i),1); post} *)
    Some (Let (p, "post", Id(p, id),
               Seq (p, SetBang(p,id,make_prim "+" id), Id (p, "post"))))
  | "%PostDecrement" -> (* i-- => let (post = i) {i := %PrimSub(%ToNumber(i),1); post} *)
    Some (Let (p, "post", Id(p, id),
               Seq (p, SetBang(p,id,make_prim "-" id), Id (p, "post"))))
  | _ -> None 
  
let rec preprocess (e : exp) : exp =
  let rec preprocess_rec ?(in_lambda=false) (e : exp) (ctx : env) : exp = 
    match e with 
    | Seq (p, e1, e2) ->
      (match e1 with
       | App (_, Id (_, "%defineGlobalVar"), [Id(_,"%context"); String (_, id)]) ->
         dprint "find defineGlobalVar %s\n" id;
         let ctx = IdMap.add id (Undefined Pos.dummy) ctx in
         let newe2 = preprocess_rec ~in_lambda e2 ctx in
         Let (p, id, Undefined Pos.dummy, newe2)
       | App (_, Id (_, "%defineGlobalAccessors"), [Id(_, "%context"); String (_, id)]) 
         when (IdMap.mem id global_bindings) ->
         dprint "find defineGlobalAccessor %s in %%global bindings\n" id;
         let id_v = Id (Pos.dummy, IdMap.find id global_bindings) in
         let ctx = IdMap.add id id_v ctx in
         let newe2 = preprocess_rec ~in_lambda e2 ctx in
         Let (p, id, id_v, newe2)
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
       | Id (pos, op), [Id(_, "%context"); String(_, id)] ->
         (match pre_post_transform op id with
          | Some (result) -> result
          | None -> App (pos, f, args))
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
  let rec jump_env (e : exp) : exp =
    match e with
    | Let (p, "%context", Id (p1, c), body) when c = "%strictContext" ->
        if eligible_for_preprocess e then begin
          let env = IdMap.empty in
          dprint_string "eligible for preprocess, start preprocessing...\n";
          let newbody = preprocess_rec body env in
	  (* after getting newbody, apply preprocess2 on the newbody *)
	  let newbody2 = preprocess2 newbody in
          Let (p, "%context", Id (p1, c), newbody2)
        end else 
          (dprint_string "not eligible for preprocess, return original one\n";
           e)
    
    | Let (p, "%context", Id (p1, c), body) when c = "%nonstrictContext" ->
        dprint_string "find nonstrict context. not eligible for preprocessing...\n";
        e
    | _ -> optimize jump_env e
  in
  jump_env e

and preprocess2 exp : exp =
  let js_func_pattern exp : exp * bool = match exp with
    | Let (pos, tmp_name, func, SetBang(_, real_name, Id(_, tmp_name2)))
      when tmp_name = tmp_name2 ->
       Let (pos, real_name, func, Undefined Pos.dummy), true
    | e -> e, false
  in 
  match exp with
  | Seq (pos, e1, e2) -> 
     (match js_func_pattern e1 with
      | Let(pos,real_name,func,Undefined _), true ->
        (* use Rec for recursive function definition *)
	    let new_e2 = preprocess2 e2 in Rec (pos,real_name,func,new_e2)
      | _ ->
	    let new_e1 = preprocess2 e1 in
        let new_e2 = preprocess2 e2 in
        Seq (pos, new_e1, new_e2)
     )
  | _ -> optimize preprocess2 exp

     
