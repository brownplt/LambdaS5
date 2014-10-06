open Prelude
open Ljs_syntax
open Ljs_opt

type env = exp IdMap.t

let is_obj_context = function
  | Id (_, id) -> id = "%context" || id = "%global" || id = "%globalContext"
  | _ -> false

let transform_GetField pos obj fld args =
  let get_static_str_fld e : string option = match e with
    | String (_, str) -> Some str
    | _ -> None
  in 
  match is_obj_context obj, get_static_str_fld fld with
  | true, Some(s) -> Id (pos, s)
  | _ -> GetField (pos, obj, fld, args)

(* %context["z" = fobj6, args] returns Some ("z", fobj6)
*)
let transform_SetField pos obj fld newval args : exp =
  let get_static_str_fld e : string option = match e with
    | String (_, str) -> Some str
    | _ -> None
  in 
  match is_obj_context obj, get_static_str_fld fld with
  | true, Some(s) -> SetBang (pos, s, newval)
  | _ -> SetField (pos, obj, fld, newval, args)

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
  let rec recog_prop prop ctx : env = match prop with
    | fld, Data ({value=value; writable=_},_,_) -> 
      IdMap.add fld value ctx
    | fld, Accessor ({getter=getter; setter=_},_,_) ->
      IdMap.add fld (get_id_in_getter getter) ctx
  in 
  let rec recog_field exp ctx : env = 
    match exp with 
    | Object (_, _, props) -> 
      List.fold_right recog_prop props ctx 
    | _ -> (* assume: obj follows let *)
      Exp_util.print_ljs exp; print_newline();
      failwith "[4]pattern assertion failed:"
  in 
  let obj = strip_let exp in
  recog_field obj ctx
    

(* this phase highly relies on the desugared patterns.
   this phase must be the first phase before all optimizations.
*)
let preprocess (e : exp) : exp =
  let rec preprocess_rec (e : exp) (ctx : env) : exp = 
    match e with 
    | Seq (p, e1, e2) ->
      printf "got seqence\n%!";
      (match e1 with
       | App (_, Id (_, "%defineGlobalVar"), [Id(_,_); String (_, id)]) ->
         let ctx = IdMap.add id (Undefined Pos.dummy) ctx in
         let newe2 = preprocess_rec e2 ctx in
         Let (p, id, Undefined Pos.dummy, newe2)
       | _ -> 
         let newe1 = preprocess_rec e1 ctx in
         let newe2 = preprocess_rec e2 ctx in
         Seq (p, newe1, newe2))
    | GetField (pos, obj, fld, args) ->
      let o = preprocess_rec obj ctx in
      let f = preprocess_rec fld ctx in
      let a = preprocess_rec args ctx in
      (match o, f with
      | Id (_, "%context"), String (_, fldstr) -> (* get fld from context *)
        printf "match context['%s']\n%!" fldstr;
        IdMap.iter (fun k v->printf "%s  -> %s\n%!" k (Exp_util.ljs_str v)) ctx;
        (try
          match IdMap.find fldstr ctx with
          | Undefined _ -> Id (Pos.dummy, fldstr)
          | Id (_,_) as id -> id
          | _ -> failwith "how could IdMap stores unrecognized exp"
        with Not_found -> GetField (pos, o, f, a)
        )
      | _ -> GetField (pos, o, f, a)
      )
    | SetField (pos, obj, fld, newval, args) ->
      let o = preprocess_rec obj ctx in
      let f = preprocess_rec fld ctx in
      let v = preprocess_rec newval ctx in
      let a = preprocess_rec args ctx in
      (match o, f with
       | Id (_, "%context"), String (_, fldstr) ->
         if IdMap.mem fldstr ctx
         then SetBang (pos, fldstr, v)
         else SetField (pos, o, f, v, a)
       | _ -> SetField (pos, o, f, v, a)
      )
    | App (pos, f, args) ->
      let f = preprocess_rec f ctx in
      let args = List.map (fun x->preprocess_rec x ctx) args in
      (match f, args with 
       | Id (_, "%EnvCheckAssign"),
         [Id (_, "%context"); String (_, id); v; _] ->
         (* todo: %envcheckassign[context, 'a', 1] may appear at different blocks!
            adding binding 'a'->1 is not enough! *)
         SetBang (pos, id, v)
       | _ -> App (pos, f, args)
      )
    | Let (p, x, x_v, body) ->
      let x_v = preprocess_rec x_v ctx in
      (try
        if x = "%context" then 
          let new_ctx = recognize_new_context x_v ctx in begin
          IdMap.iter (fun k v->printf "%s -> %s\n%!" k (Exp_util.ljs_str v)) new_ctx; 
          print_newline() ;
          
          Let (p, x, x_v, preprocess_rec body new_ctx) end
        else 
          Let (p, x, x_v, preprocess_rec body ctx)
      with Failure e -> 
        printf "fail %s\n%!" e;
        Let (p, x, x_v, preprocess_rec body ctx)
      )
    | Lambda (p, xs, body) ->
      printf "entering Lambda (%!";
      List.iter (fun x->printf "%s,%!" x) xs; print_newline() ;
      printf "the body is:\n %s" (Exp_util.ljs_str body);
      print_endline "==================";
      let result = preprocess_rec body ctx in begin
      printf "leaving Lambda\n%!";
      Lambda (p, xs, result) end
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
      -> optimize (fun e->preprocess_rec e ctx) e
  in 
  let env = IdMap.empty in
  preprocess_rec e env
