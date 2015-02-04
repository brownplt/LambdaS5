open Prelude
open Ljs_syntax
open Ljs_opt


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

type env = exp IdMap.t

let debug_on = false

let dprint, dprint_string, dprint_ljs = Debug.make_debug_printer ~on:debug_on "preprocess"

(* only apply the preprocess on code that is in strict mode *)
let only_strict = false

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
     (* special case undefined and NaN *)
    ]
  in  
  let rec to_map maps internals = match internals with
    | [] -> maps
    | hd :: rest ->
      to_map (IdMap.add (fst2 hd) (Id (Pos.dummy, snd2 hd)) maps) rest
  in 
  let map = IdMap.from_list [("NaN", Num(Pos.dummy, nan));
                             ("Infinity", Num(Pos.dummy, infinity)); 
                             ("undefined", Undefined Pos.dummy)] in
  to_map map global_internals

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
   0. strict mode: can be turned off.
   1. %context["window"]: code may do bad things through window
   2. %EnvCheckAssign(_, _, %this, _): code may do bad things through the alias of 'this'
      %EnvCheckAssign(_, _, {object field as this}, _): code may do bad things through the alias of 'this'.
      the "this" alias should also prohibited in lambda, see 6)
   3. passing %this to a function: code may do something like `function z(a) {a.x = 1}; z(this)`
   4. computation string field on top level. In function computation is fine.

   5. with(o): strict mode does not allow "with". But here is how it works: code will make a new context, and
      we cannot decide if the expression %context["x"] should be translated to identifier x or leave it as %context["x"].
   6. this[delete "x"]: try to delete variable from this(no matter in toplevel or lambda).
   7. iterate through all property of top-level this
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


(*
let by_pass_args func = match func with
  | Id (_, "%PropAccessorCheck") -> true
  | _ -> false
    
let is_context ~toplevel (obj : exp) : bool =
  match obj with
  | Id (_, "%context") -> true
  | App (_, f, [arg]) when by_pass_args f ->
    begin match arg with
      | Id (_, "%this") when toplevel -> true
      | _ -> false
    end
  | _ -> false

(* top level can use window properties but cannot make assignment to it.
   any refer to window object itself should be prohibited.
   Explicitly prohibit
*)
let rec is_window_obj ~toplevel e =
  (* window object will be desugared to multiple patterns*)
  match e with
  | GetField (_, obj, String(_, "window"), _)
    when is_context ~toplevel obj -> true
  | App (_, f, [arg]) when by_pass_args f ->
    is_window_obj ~toplevel arg
  | _ -> false

let rec window_free ?(toplevel=true) exp : bool =
  match exp with
  | GetField (_, obj, String(_, "window"), args) ->
    window_free ~toplevel args && (not (is_context ~toplevel obj))
  | GetField (_, obj, _, _) when is_window_obj ~toplevel obj ->
    (* OK. use property of window. *)
    true
  | Lambda (_, _, body) -> window_free ~toplevel:false body
  | _ -> List.for_all (fun e -> window_free ~toplevel e) (child_exps exp)
*)

let rec eligible_for_preprocess exp : bool = 
  let is_static_field fld = match fld with
    | String (_, _) -> true
    | _ -> 
      dprint "not eligible: find non-static field: %s\n%!" (Exp_util.ljs_str fld);
      false
  in 
  let rec contain_this_keyword toplevel (args_obj : exp) = 
    match args_obj with
    | Id (_, "%this") -> let result = toplevel in
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
    | Object (_, attr, props) ->
      let is_eligible_option ~toplevel (opt : exp option) = match opt with
        | Some (e) -> is_eligible_rec ~toplevel e
        | None -> true
      in
      let handle_prop prop = match prop with
        | (s, Data(data, _, _)) -> is_eligible_rec ~toplevel data.value
        | (s, Accessor(acc, _, _)) -> is_eligible_rec ~toplevel acc.getter && is_eligible_rec ~toplevel acc.setter
      in
      is_eligible_option ~toplevel attr.primval &&
      is_eligible_option ~toplevel:false attr.code &&
      is_eligible_option ~toplevel attr.proto &&
      List.for_all handle_prop props

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
        | Id (_, "%EnvCheckAssign"), [_;_; Id(_, "%this");_] when toplevel -> 
          dprint_string "make alias of 'this'. not eligible";
          false
        | Id (_, "%EnvCheckAssign"), [_;_; Object(_,_,_) as obj;_] -> 
          not (List.exists (fun x->contain_this_keyword toplevel x) (child_exps obj)) &&
          (List.for_all is_eligible args)
        | Id (_, "%set-property"), [App(_, Id(_,"%ToObject"), [Id(_, "%this")]);
                                    this_fld; arg] ->
          (* this['fld'] = 1=> desugar to %set-property(%ToObject(%this), 'fld', 1.)  *)
          is_eligible arg && (if toplevel then (is_static_field this_fld) else true)
        | Id (_, "%makeWithContext"), _ ->
          dprint_string "Use 'with'. Not eligible";
          false
        | Id (_, "%propertyNames"), [Id(_, "%this"); _] when toplevel ->
          dprint_string "get property from top-level this. Not eligible";
          false
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
      is_eligible_rec ~toplevel body
    | DeleteField (_, Id(_, "%this"), v) ->
      dprint_string (sprintf "deletefield: %s\n" (Exp_util.ljs_str v));
      false
    | _ -> List.for_all is_eligible (child_exps exp)
  in
  let check_strict = if only_strict then all_in_strict exp else true in
  check_strict && window_free exp && is_eligible_rec exp

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
  let toNumber id : exp = App (Pos.dummy, Id (Pos.dummy, "%ToNumber"), [Id (Pos.dummy, id)]) in
  let make_prim op id = match op with
    | "-" -> App (p, Id(p, "%PrimSub"), [toNumber id; Num(p,1.)])
    | "+" -> App (p, Id(p, "%PrimAdd"), [toNumber id; Num(p,1.)])
    | _ -> failwith "make_prim gets unexpected argument"
  in 
  match op with
  | "%PrefixDecrement" -> (* --i => i := %PrimSub(%ToNumber(i), 1) *)
    Some (SetBang (p, id, make_prim "-" id))
  | "%PrefixIncrement" -> (* ++i => i := %PrimAdd(%ToNumber(i), 1) *)
    Some (SetBang (p, id, make_prim "+" id))
  | "%PostIncrement" -> (* i++ => let (post = ToNumber(i)) {i := %PrimAdd(%ToNumber(i),1); post} *)
    Some (Let (p, "post", toNumber id,
               Seq (p, SetBang(p, id , make_prim "+" id), Id (p, "post"))))
  | "%PostDecrement" -> (* i-- => let (post = ToNumber(i)) {i := %PrimSub(%ToNumber(i),1); post} *)
    Some (Let (p, "post", toNumber id,
               Seq (p, SetBang(p, id, make_prim "-" id), Id (p, "post"))))
  | _ -> None 

let make_writable_error (msg : string) : exp =
  let msg = msg ^ " not writable" in
  App (Pos.dummy, Id(Pos.dummy, "%TypeError"), [String (Pos.dummy, msg)])

let rec preprocess (e : exp) : exp =
  let rec preprocess_rec ?(in_lambda=false) (e : exp) (ctx : env) : exp = 
    match e with 
    | Seq (p, e1, e2) ->
      (match e1 with
       | App (_, Id (_, "%defineGlobalVar"), [Id(_,"%context"); String (_, id)]) ->
         dprint "find defineGlobalVar %s\n" id;
         (*toplevel define global var by %defineGlobalVar. if the id is NaN, undefined and Infinity etc
           that are unwritable, stores they as Num (except undefined). Later when context['NaN'=1] appears in
           toplevel, since NaN is a Number, assignment to NaN is turned to typeError.
         *)
         let ctx = if id = "NaN" || id = "undefined" || id = "Infinity" then
             IdMap.add id (IdMap.find id global_bindings) ctx
           else IdMap.add id (Undefined Pos.dummy) ctx 
         in
         let newe2 = preprocess_rec ~in_lambda e2 ctx in
         Let (p, id, Undefined Pos.dummy, newe2)
       | App (_, Id (_, "%defineGlobalAccessors"), [Id(_, "%context"); String (_, id)]) 
         when (IdMap.mem id global_bindings) ->
         dprint "find defineGlobalAccessor %s in %%global bindings\n" id;
         let id_v = IdMap.find id global_bindings in
         let ctx = IdMap.add id id_v ctx in
         preprocess_rec ~in_lambda e2 ctx 
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
         begin 
           try
            match IdMap.find fldstr ctx with
            | Undefined _ when fldstr <> "undefined" -> Id (Pos.dummy, fldstr)
            | Undefined _ as udf -> udf
            | Id (_,_) as id -> id
            | Num (_,_) as n -> n
            | e -> 
              (*dprint "not expecting: %s\n%!" (Exp_util.ljs_str e);*)
              e
          with Not_found -> GetField (pos, o, f, a)
         end 
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
            | Undefined _ when fldstr <> "undefined" -> SetBang (pos, fldstr, v)
            | Id (_, id) -> SetBang (pos, id, v)
            | Undefined _
            | Num (_,_) -> make_writable_error fldstr
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
            | Undefined _ when id <> "undefined" -> SetBang (pos, id, v)
            | Id (_, actual_id) -> SetBang (pos, actual_id, v)
            (* if NaN, undefined, Infinity, we need to check the writable field *)
            | Undefined _
            | Num (_,_) -> make_writable_error id
            | normal_exp ->
              (* get normal exp, which means that id is somehow declared in contxt, use that id(see example of es5id: 12.14-1 *)
              SetBang (pos, id, v)
          with Not_found -> App (pos, f, args))
       | Id (_, "%PropAccessorCheck"), [Id (_, "%this")] ->
         if in_lambda then
           App (pos, f, args)
         else 
           Id (pos, "%context")
       | Id (p1, "%set-property"), [Id (p2, "%context"); String (p3, id); v] ->
         let newexp = SetField (p1, Id(p2, "%context"), String(p3,id), v, Null Pos.dummy) in
         (match preprocess_rec ~in_lambda newexp ctx with
          | SetField(_,_,_,_,_) ->
            (* cannot translate, use the original set-property exp *)
            App (pos, f, args)
          | result -> result
         )
       | Id (_, "%ToObject"), [Id(_, "%this")] when not in_lambda ->
         Id (Pos.dummy, "%context")
       | Id (_, "%Typeof"), [Id(_, "%context"); String(_, id)] 
         when IdMap.mem id ctx ->
         let actual_var = match IdMap.find id ctx with
           | Undefined _ when id <> "undefined" -> Id (Pos.dummy, id)
           | Undefined _ as udf -> udf
           | Id (_, actual_id) -> Id (Pos.dummy, actual_id)
           | Num (_,_) as n -> n
           | _ -> failwith "%Typeof: IdMap stores unrecognized exp"
         in 
         TryCatch (Pos.dummy,
                   Op1(Pos.dummy, "typeof", actual_var),
                   Lambda (Pos.dummy, ["e"], Undefined Pos.dummy))
       | Id (pos, op), [Id(_, "%context"); String(_, id)]
         when IdMap.mem id ctx ->
         let transform var = match pre_post_transform op var with
           | Some (result) -> result
           | None -> App (pos, f, args)
         in
         begin match IdMap.find id ctx with
           | Undefined _ when id <> "undefined" -> transform id
           | Id (_, actual_id) -> transform actual_id
           | Undefined _
           | Num (_,_) -> make_writable_error id
           | _ -> failwith (sprintf "%s: IdMap stores unrecognized exp" op)
         end
       | _ -> App (pos, f, args)
      )
    | Let (p, x, x_v, body) ->
      let x_v = preprocess_rec ~in_lambda x_v ctx in
      (* first match with context patterns in lambda *)
      begin match get_localcontext e with
        | None -> (* not a new context binding in lambda *)
          (* in the desugared code, there is no place to bind %context to a non-obj *)
          assert (x <> "%context");
          Let (p, x, x_v, preprocess_rec ~in_lambda body ctx)
        | Some (new_let) -> (* FIXME: 12.14-1 *)
          dprint "new_let is %s\n" (Exp_util.ljs_str new_let);
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
    | Let (p, "%context", Id (p1, c), body) ->
      if (only_strict && c = "%strictContext") || (not only_strict) then
        begin 
          if eligible_for_preprocess e then
            begin
              let env = IdMap.empty in
              dprint_string "eligible for preprocess, start preprocessing...\n";
              let newbody = preprocess_rec body env in
              Let (p, "%context", Id (p1, c), newbody)
            end else 
            (dprint_string "not eligible for preprocess, return original one\n";
             e)
        end
      else
        begin
          dprint_string "find nonstrict context. not eligible for preprocessing...\n";
          e
        end 
    | _ -> optimize jump_env e
  in
  let rec propagate_this (e : exp) (env : env) =
    let propagate e = propagate_this e env in
    match e with
    | Id (pos, id) when IdMap.mem id env -> Id (pos, "%this")
    | Let (pos, x, Id (p1, "%this"), body) ->
      let body = propagate_this body (IdMap.add x (Undefined Pos.dummy) env) in
      Let(pos, x, Id(p1, "%this"), body)
    | _ -> optimize propagate e
  in
  let e = propagate_this e IdMap.empty in
  jump_env e

