open Ljs_sym_values

(* pretty printing for Z3 format *)
open Prelude

open Format
open FormatExt


let log_z3 = true
let simple_print = true (* print in human readable form *)


let rec vert_intersperse a lst = match lst with
  | [] -> []
  | [x] -> [x]
  | x :: xs -> squish [x; a] :: (vert_intersperse a xs)

let prim_to_z3 op = match op with
  | "NOT" -> "not"
  | "stx=" -> "="
  | "!" -> "bang"
  | _ -> op

let rec value v store = 
  match v with
  | Null -> text "NULL"
  | Undefined -> text "UNDEF"
  | Num n -> 
    if (n = infinity) then text "(NUM inf)"
    else if (n = neg_infinity) then text "(NUM neg_inf)"
    else if (n <> n) then text "(NUM NaN)"
    else parens (horz [text "NUM"; text (string_of_float n)])
  | String s -> text ("S_" ^ s) (* for now; this doesn't support spaces... *)
  | True -> text "(BOOL true)"
  | False -> text "(BOOL false)"
  | ObjPtr loc -> text ("(OBJPTR " ^ (Store.print_loc loc) ^ ")") (* obj (sto_lookup_obj loc store) *)
  | Closure _ -> text "(FUN closure)"
  (* | Lambda (p,lbl, ret, exn, xs, e) -> *)
  (*   label verbose lbl (vert [squish [text "lam"; parens (horz (text "Ret" :: text ret :: text "," :: *)
  (*                                                                text "Exn" :: text exn :: text ";" ::  *)
  (*                                                                (intersperse (text ",") (map text xs))))]; *)
  (*                            braces (exp e)]) *)
  | SymScalar id -> text id
  | NewSym (id, loc) -> parens (text ("NewSym " ^ id))

(* and obj ({ attrs = avs; conps = conprops; symps = symprops; }, store) =  *)
(*   (\*    horz [(braces (vert [attrsv avs;  *\) (\* ignoring avs for the moment *\) *)
(*   parens ( *)
(*     horz [text "OBJ"; *)
(*           parens  *)
(*             (horz [text "Array2Fields"; *)
(*                    List.fold_left (fun acc (f, p) -> *)
(*                      let value =  *)
(*                        match p with *)
(*                        | Data ({value=v; writable=w}, enum, config) ->  *)
(*                          parens (horz [text "Data"; (uncurry value) (sto_lookup_val v store);  *)
(*                                        text (string_of_bool w); *)
(*                                        text (string_of_bool enum);  *)
(*                                        text (string_of_bool config)]) *)
(*                        | Accessor ({getter=g; setter=s}, enum, config) ->  *)
(*                          parens (horz [text "Accessor"; (uncurry value) (sto_lookup_val g store); *)
(*                                        (uncurry value) (sto_lookup_val s store); *)
(*                                        text (string_of_bool enum);  *)
(*                                        text (string_of_bool config)]) *)
(*                      in parens (vert [horz[text "store"; acc]; horz[parens (horz[text "s"; text ("S_" ^ f)]); value]])) *)
(*                      (text "mtObj") *)
(*                      (List.append (IdMap.bindings conprops) *)
(*                                   (IdMap.bindings symprops))])]) *)


(* and prim verbose p =  *)
(*   let value = value verbose in *)
(*   match p with *)
(*   | GetAttr (p,lbl, a, o, f) -> *)
(*     label verbose lbl (squish [value o; *)
(*                                brackets (horz [value f; angles (horz [text (Ljs_syntax.string_of_attr a)])])]) *)
(*   | SetAttr (p,lbl, a, o, f, v) -> *)
(*     label verbose lbl (squish [value o; *)
(*                                brackets (squish [value f; angles (horz [text (Ljs_syntax.string_of_attr a)]); *)
(*                                                  text "="; value v])]) *)
(*   | SetBang (p,lbl, x, e) -> *)
(*     label verbose lbl (horz [text x; text "<-"; value e]) *)
(*   | DeleteField (p,lbl, o, f) -> *)
(*     label verbose lbl (squish [value o; brackets (horz [text "delete"; value f])]) *)

and exp e store = 
  let castFn t e = match t with
    | TNum -> parens (horz [text "n"; e])
    | TBool -> parens (horz [text "b"; e])
    | TSymString
    | TString -> parens (horz [text "s"; e])
    | TFun _ -> parens (horz [text "f"; e])
    | TObjPtr -> parens (horz [text "loc"; e])
    | _ -> e in
  let uncastFn t e = match t with
    | TNum -> parens (horz [text "NUM"; e])
    | TBool -> parens (horz [text "BOOL"; e])
    | TSymString
    | TString -> parens (horz [text "STR"; e])
    | TFun _ -> parens (horz [text "FUN"; e])
    | TObjPtr -> parens (horz [text "OBJPTR"; e])
    | _ -> e in
  match e with
  | Hint s -> horz [text ";;"; text s] 
  | Concrete v -> value v store
  | STime t -> int t
  | SLoc l -> text (Store.print_loc l)
  | SId id -> text id
  | SOp1 (op, e) -> 
    let (t, ret) = Ljs_sym_delta.typeofOp1 op in
    uncastFn ret (parens (horz [text (prim_to_z3 op); castFn t (exp e store)]))
  | SOp2 (op, e1, e2) ->
    let (t1, t2, ret) = Ljs_sym_delta.typeofOp2 op in
    uncastFn ret (parens (horz [text (prim_to_z3 op); castFn t1 (exp e1 store); castFn t2 (exp e2 store)]))
  | SApp (f, args) ->
    parens (horz ((exp f store) :: (map (fun a -> exp a store) args)))
  | SLet (id, e1) ->
    parens(horz [text "assert"; parens(horz[text "="; text id; exp e1 store])])
  | SCastJS (t, e) -> castFn t (exp e store)
  | SUncastJS (t, e) -> uncastFn t (exp e store)
  | SNot e -> parens (horz [text "not"; exp e store])
  | SAnd es -> parens (horz (text "and" :: (map (fun e -> exp e store) es)))
  | SOr es -> parens (horz (text "or" :: (map (fun e -> exp e store) es)))
  | SImplies (pre, post) -> parens (horz [text "=>"; exp pre store; exp post store])
  | SAssert e -> parens (horz [text "assert"; exp e store])
  | SIsMissing e ->
    parens (horz [text "="; exp e store; text "ABSENT"])
  | SGetField (id, f) ->
    uncastFn TAny (parens(horz [text "select"; (parens(horz [text "Fields2Array"; castFn TObjPtr (text id);])); castFn TString (text f)]))

(* and attrsv store { proto = p; code = c; extensible = b; klass = k } = *)
(*   let proto = [horz [text "#proto:"; value p store]] in *)
(*   let code = match c with None -> []  *)
(*     | Some e -> [horz [text "#code:"; value e store]] in *)
(*   brackets (vert (map (fun x -> squish [x; (text ",")]) *)
(*                     (proto@ *)
(*                        code@ *)
(*                        [horz [text "#class:"; text ("\"" ^ k ^ "\"")];  *)
(*                         horz [text "#extensible:"; text (string_of_bool b)]]))) *)
    
(* (\* TODO: print and parse enum and config *\) *)
(* and prop store (f, prop) = match prop with *)
(*   | Data ({value=v; writable=w}, enum, config) -> *)
(*     horz [text ("'" ^ f ^ "'"); text ":"; braces (horz [text "#value";  *)
(*                                                         (\* TODO: lookup val in store *\) *)
(*                                                         text (Store.print_loc v); text ",";  *)
(*                                                         text "#writable";   *)
(*                                                         text (string_of_bool w); *)
(*                                                         text ","; *)
(*                                                         text "#configurable"; *)
(*                                                         text (string_of_bool config)])] *)
(*   | Accessor ({getter=g; setter=s}, enum, config) -> *)
(*     horz [text ("'" ^ f ^ "'"); text ":"; braces (horz [text "#getter"; *)
(*                                                         text (Store.print_loc g); text ",";  *)
(*                                                         text "#setter"; *)
(*                                                         text (Store.print_loc s)])] *)
;;
let to_string v store = exp v store Format.str_formatter; Format.flush_str_formatter() 

let rec simple_value v = 
  match v with
  | Null -> text "null"
  | Undefined -> text "undefined"
  | Num n -> 
    if (n = infinity) then text "inf"
    else if (n = neg_infinity) then text "neg_inf"
    else if (n <> n) then text "NaN"
    else text (string_of_float n)
  | String s -> text ("S_" ^ s) (* for now; this doesn't support spaces... *)
  | True -> text "true"
  | False -> text "false"
  | ObjPtr loc -> text ("&<" ^ (Store.print_loc loc) ^ ">") (* obj (sto_lookup_obj loc store) *)
  | Closure _ -> text "(closure)"
  | SymScalar id -> text id
  | NewSym (id, loc) -> parens (text ("NewSym " ^ id))

let rec simple_exp e = 
  match e with
  | Hint s -> horz [text ";;"; text s] 
  | Concrete v -> simple_value v
  | SLoc l -> text (Store.print_loc l)
  | SId id -> text id
  | SOp1 (op, e) -> 
    parens (horz [text (prim_to_z3 op); simple_exp e])
  | SOp2 (op, e1, e2) ->
    parens (horz [text (prim_to_z3 op); simple_exp e1; simple_exp e2])
  | SApp (f, args) ->
    parens (horz (simple_exp f :: (map (fun a -> simple_exp a) args)))
  | SLet (id, e1) ->
    parens (horz [parens(horz[text "let"; text id; simple_exp e1])])
  | SCastJS (t, e) -> simple_exp e
  | SUncastJS (t, e) -> simple_exp e
  | SNot e -> parens (horz [text "not"; simple_exp e])
  | SAnd es -> parens (horz (text "and" :: (map (fun e -> simple_exp e) es)))
  | SOr es -> parens (horz (text "or" :: (map (fun e -> simple_exp e) es)))
  | SImplies (pre, post) -> parens (horz [text "=>"; simple_exp pre; simple_exp post])
  | SAssert e -> simple_exp e
  | _ -> text "Missed something"

let substitute exp id_defs =
  let rec sub exp = match exp with
  | SId id ->
    begin try sub (IdMap.find id id_defs)
    with Not_found -> exp end
  | SOp1 (op, e) ->
    if op = "prim->bool"
    then sub e
    else SOp1 (op, sub e)
  | SOp2 (op, e1, e2) -> SOp2 (op, sub e1, sub e2)
  | SApp (f, args) -> SApp (f, map sub args)
  | SCastJS (t, e) -> sub e
  | SUncastJS (t, e) -> sub e
  | SNot e -> SNot (sub e)
  | SAnd es -> SAnd (map sub es)
  | SOr es -> SOr (map sub es)
  | SImplies (pre, post) -> SImplies (sub pre, sub post)
  | SAssert e -> sub e
  | _ -> exp
  in sub exp


let simplify result cs =
  let (lets, assns) = List.partition (fun c -> match c with SLet _ -> true | _ -> false) cs in
  let id_defs =
    fold_left
      (fun id_defs letc ->
        match letc with
        | SLet (id, exp) -> IdMap.add id exp id_defs
        | _ -> id_defs)
      IdMap.empty lets
  in
  (* Substitute all ids with their defs in assns *)
  let assns =
    fold_left
      (fun assns assn -> substitute assn id_defs :: assns)
      [] assns
  in
  (* We'd also like to see the def of the result *)
  let id_defs = match result with
  | SymScalar id ->
    IdMap.add id (substitute (SId id) id_defs) id_defs
  | _ -> id_defs
  in
  (id_defs, assns)

let simple_pc result pc =
  let (id_defs, assns) = simplify result pc.constraints in
  let res = match result with
    | SymScalar id ->
      [horz [text id;
            text "="; 
            simple_exp (IdMap.find id id_defs);]]
    | _ -> []
  in
  let assns = map (fun a -> simple_exp a) assns in
  vert (res @ [
    text "Assns:";
    vert assns;
  ]);;

let simple_to_string result pc = simple_pc result pc Format.str_formatter; Format.flush_str_formatter() 

let print_results (rets, exns) = 
  let ret_grps, exn_grps = collect compare rets, collect compare exns in
  List.iter
    (fun (v, pcs) ->
      (*print_string "##########\n";*)
      printf "Result: %s:\n" (Ljs_sym_pretty.val_to_string v);
      List.iter
        (fun pc ->
          print_string "----------\n";
          if simple_print then begin
            (match v with
            | ObjPtr loc ->
              (*printf "%s\n" (Ljs_sym_pretty.store_to_string pc.store);*)
              printf "Var names: %s\n" (Ljs_sym_pretty.rec_val_to_string v pc);
              printf "Value:\n%s\n" (Ljs_sym_pretty.rec_obj_to_string (sto_lookup_obj_pair loc pc) pc)
            | _ -> ());
          (*print_string "##########\n";*)
            printf "%s\n" (simple_to_string v pc)
          end else begin
            List.iter 
              (fun c -> printf "%s\n" (to_string c pc))
              pc.Ljs_sym_values.constraints
          end
          (*printf "%s\n" (Ljs_sym_pretty.env_to_string pc.print_env)*)
        ) pcs;
      (*printf "%s\n" (Ljs_sym_pretty.store_to_string p.Ljs_sym_values.store);*)
      print_newline())
    ret_grps;

  List.iter
    (fun (v, pcs) -> match v with
      | Ljs_sym_values.Throw v ->
        printf "Exn: %s:\n" (Ljs_sym_pretty.val_to_string v)
      | _ -> printf "Exn: something other than a Throw\n")
    exn_grps

(*let ty_to_typeof tp = match tp with*)
(*  | TNull -> Some "null"*)
(*  | TUndef -> Some "undefined"*)
(*  | TSymString*)
(*  | TString -> Some "string"*)
(*  | TBool -> Some "boolean"*)
(*  | TNum -> Some "number"*)
(*  | TObj -> Some "object"*)
(*  | TFun _ -> Some "function"*)
(*  | TAny -> None*)
(*  | TData -> None*)
(*  | TAccessor -> None*)

(* communicating with Z3 *)

let uncastTy ty = match ty with
  | TNull -> Some "NULL"
  | TUndef -> Some "UNDEF"
  | TNum -> Some "NUM"
  | TString -> Some "STR"
  | TBool -> Some "BOOL"
  | TFun _ -> Some "FUN"
  | _ -> None

let def_op1 name out_ty else_val func = 
  let header = "(define-fun " ^ name ^ " ((x JS)) "
    ^ out_ty ^ "\n" in
  header ^
  (List.fold_left
    (fun def ty ->
      match uncastTy ty with
      | None -> def
      | Some tystr -> "   (if (is-" ^ tystr ^ " x) "
        ^ func ty ^ "\n" ^ def ^ ")")
    ("     " ^ else_val)
    [TNull; TUndef; TString; TBool; TNum; TFun 0; TObjPtr]) ^ ")\n"

let op1_defs =
  def_op1 "prim->bool" "Bool" "true"
    (fun ty -> match ty with
    | TNull
    | TUndef -> "false"
    | TString -> "(not (= (length (s x)) 0.))"
    | TBool -> "(b x)"
    | TNum -> "(not (or (= (n x) NaN) (= (n x) 0.)))"
    | TFun _ -> "true"
    | TObjPtr -> "true"
    | _ -> failwith "Shouldn't hit")
  ^
  def_op1 "typeof" "Str" "(s S_undefined)"
    (fun ty -> "(s S_" ^
      (match ty with
      | TNull -> "null"
      | TUndef -> "undefined"
      | TString -> "string"
      | TBool -> "boolean"
      | TNum -> "number"
      | TFun _ -> "function"
      | TObjPtr -> "object"
      | _ -> failwith "Shouldn't hit")
      ^ ")")
  ^
  def_op1 "bang" "Bool" "false"
    (fun ty -> match ty with
      | TNull -> "true"
      | TUndef -> "true"
      | TString -> "(= x S_)"
      | TBool -> "(not (b x))"
      (* TODO look at delta fun and figure out what they were using <> for *)
      | TNum -> "(or (= (n x) 0.) (not (= (n x) (n x))))"
      | TFun _ -> "false"
      | TObjPtr -> "false"
      | _ -> failwith "Shouldn't hit")

let z3prelude = "\
(set-option :produce-models true)
(set-option :auto-config false)
(set-option :model-compact true)

(declare-sort Fun)
(declare-sort Str)

(declare-fun length (Str) Real)
(declare-fun strlen (Str) Real)
(declare-fun char-at (Str Real) Str)
(declare-fun numstr->num (Str) Real)

(define-fun neg_inf () Real (- 0.0 1234567890.984321))
(define-fun inf () Real 12345678.321)
(define-fun NaN () Real 876545689.24565432)
(declare-const closure Fun)

(declare-datatypes ()
                   ((Attr Config Enum Writable Value Getter Setter)))
(declare-datatypes ()
                   ((JS
                     (NUM (n Real))
                     (UNDEF)
                     (NULL)
                     (BOOL (b Bool))
                     (STR (s Str))
                     (OBJPTR (loc Int))
                     (FUN (f Fun)))))

(declare-fun prim->str (JS) Str)
(define-fun primitive? ((x JS)) Bool true)
"

let tot = ref 0.;;

let is_sat (p : ctx) hint : bool =
  let t1 = Sys.time() in
  (* Only ask z3 if we have constraints to ask about *)
  match List.filter (fun c -> match c with Hint _ -> false | _ -> true) p.constraints with
  | [] -> true | _ ->

  (* Add all typeof strs to vars so that we can use them
   * to define typeof to z3 later *)
  let p =
    List.fold_left
      (fun pc type_str -> add_const_string type_str pc)
      p
      ["undefined"; "null"; "string"; "number"; "boolean"; "function"; "object"]
  in

  let { constraints = cs; vars = vs; store = store } = p in

  let (inch, outch) = Unix.open_process "z3 -smt2 -in" in 
  if log_z3 then Printf.printf "%s\n" z3prelude;
  output_string outch z3prelude; output_string outch "\n";

  IdMap.iter
    (fun id (tp, hint) -> 
      let assertion =
        match tp with
        | TNull -> Printf.sprintf "(declare-const %s JS) ;; \"%s\"\n(assert (is-NULL %s))\n" id hint id
        | TUndef -> Printf.sprintf "(declare-const %s JS) ;; \"%s\"\n(assert (is-UNDEF %s))\n" id hint id
        | TString
        | TSymString -> Printf.sprintf "(declare-const %s JS) ;; \"%s\"\n(assert (is-STR %s))\n" id hint id
        | TBool -> Printf.sprintf "(declare-const %s JS) ;; \"%s\"\n(assert (is-BOOL %s))\n" id hint id
        | TNum -> Printf.sprintf "(declare-const %s JS) ;; \"%s\"\n(assert (is-NUM %s))\n" id hint id
        | TObjPtr -> Printf.sprintf "(declare-const %s JS) ;; \"%s\"\n(assert (is-OBJPTR %s))\n" id hint id
        | TFun arity -> Printf.sprintf "(declare-const %s JS) ;; \"%s\"\n(assert (is-FUN %s))\n" id hint id
        (* All we know about syms of unknown type is that they can't be obj ptrs, because
         * that case is subsumed by our obj branching, and they can't be funs, because we
         * don't know how to handle sym funs. TODO do better than this*)
        | TAny -> Printf.sprintf "(declare-const %s JS) ;; \"%s\"\n(assert (and (not (is-OBJPTR %s)) (not (is-FUN %s))))\n" id hint id id
        | TData -> Printf.sprintf 
          "(declare-const %s Prop) ;; \"%s\"\n(assert (is-Data %s))\n" id hint id
        | TAccessor -> Printf.sprintf
          "(declare-const %s Prop) ;; \"%s\"\n(assert (is-Accessor %s))\n" id hint id
      in
      if log_z3 then Printf.printf "%s" assertion;
      output_string outch assertion;
    )
    vs; 
  
  if log_z3 then Printf.printf ";; String variables:\n";
  let strvs = IdMap.filter (fun _ (tp, _) -> tp = TString) vs in
  if not (IdMap.is_empty strvs) then begin
    let distinctStrs = IdMap.fold (fun id _ acc -> id ^ " " ^ acc) strvs "" in
    if log_z3 then Printf.printf "(assert (distinct %s))\n\n" distinctStrs;
    output_string outch (Printf.sprintf "(assert (distinct %s))\n" distinctStrs);
  end;

  if log_z3 then Printf.printf ";; Operators:\n";
  if log_z3 then Printf.printf "%s\n" op1_defs;
  output_string outch op1_defs; output_string outch "\n";

  let (lets, rest) = List.partition (fun pc -> match pc with SLet _ -> true | _ -> false) cs in
  let print_pc constraintExp = 
    if log_z3 then Printf.printf "%s\n" (to_string constraintExp p);
    output_string outch 
      (Printf.sprintf "%s\n" (to_string constraintExp p)) in
  if log_z3 then Printf.printf ";; Let constraints:\n";
  List.iter print_pc lets;
  if log_z3 then Printf.printf ";; Other constraints:\n";
  List.iter print_pc rest;

  output_string outch "(check-sat)";
  if log_z3 then Printf.printf "(check-sat)\n";
  if log_z3 then Printf.printf "%s\n" hint;
  close_out outch;
  flush stdout;
  let res = input_line inch in
  close_in inch; 
  let  _ = Unix.close_process (inch, outch) in
  if log_z3 then Printf.printf "z3 said: %s\n\n" res;
  let res = if (String.length res) > 3 then String.sub res 0 3 else res in (* strip line endings... *)
  if log_z3 then begin
    let t2 = Sys.time() in
    tot := !tot +. (t2 -. t1);
    Printf.printf "z3 took: %f secs\n" (t2 -. t1);
    Printf.printf "total: %f secs\n\n" (!tot)
  end;
  (res = "sat")
    
