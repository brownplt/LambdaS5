open Prelude
open Ljs_sym_values

open Format
open FormatExt

let rec vert_intersperse a lst = match lst with
  | [] -> []
  | [x] -> [x]
  | x :: xs -> squish [x; a] :: (vert_intersperse a xs)

let symbool b = match b with
  | BTrue -> text "true" 
  | BFalse -> text "false"
  | BSym id -> text id 
let symstring s = match s with
  | SString str -> text str 
  | SSym id -> text id 

let rec value v = 
  match v with
  | Null -> text "null"
  | Undefined -> text "undefined"
  | Num n -> text (string_of_float n)
  | String s -> text ("\"" ^ s ^ "\"")
  | True -> text "true"
  | False -> text "false"
  | ObjPtr loc -> horz [squish [text "&<"; text (Store.print_loc loc); text ">"]]
  | Closure func -> text "(closure)"
  (* | Lambda (p,lbl, ret, exn, xs, e) -> *)
  (*   label verbose lbl (vert [squish [text "lam"; parens (horz (text "Ret" :: text ret :: text "," :: *)
  (*                                                                text "Exn" :: text exn :: text ";" ::  *)
  (*                                                                (intersperse (text ",") (map text xs))))]; *)
  (*                            braces (exp e)]) *)
  | SymScalar id -> text id
  | NewSym (id, locs) -> horz [text ("NewSym " ^ id);
                               brackets (horz (map (fun loc -> text (Store.print_loc loc)) locs))]
                                 

and obj o = match o with
  | NewSymObj locs -> horz [text "NewSymObj"; brackets (horz (map (fun loc -> text (Store.print_loc loc)) locs))]
  | SymObj f -> helper f "@sym"
  | ConObj f -> helper f "@"
and helper { attrs = attrsv; conps = conpsv; symps = sympsv; } prefix = 
  if IdMap.is_empty conpsv && IdMap.is_empty sympsv 
  then squish [text prefix; braces (attrs attrsv)]
  else 
    horz [squish [text prefix; (braces (vert [attrs attrsv; 
                                           text "- Con fields -";
                                           vert (vert_intersperse (text ",")
                                                   (map con_prop (IdMap.bindings conpsv)));
                                           text "- Sym fields -";
                                           vert (vert_intersperse (text ",")
                                                   (map sym_prop (IdMap.bindings sympsv)));]))]]


and attrs { proto = p; code = c; extensible = b; klass = k } =
  let proto = [horz [text "#proto:"; text (Store.print_loc p)]] in
  let code = match c with None -> [] 
    | Some e -> [horz [text "#code:"; text (Store.print_loc e)]] in
  brackets (horzOrVert (map (fun x -> squish [x; (text ",")])
                          (proto@
                             code@
                             [horz [text "#class:"; symstring k]; 
                              horz [text "#extensible:"; symbool b]])))

(* TODO: print and parse enum and config *)
and prop (f, prop) = match prop with
  | Data ({value=v; writable=w}, enum, config) ->
    horz [text f; text ":"; braces (horz [text "#value"; 
                                                        text (Store.print_loc v); text ",";
                                                        text "#writable";  
                                                        symbool w;
                                                        text ",";
                                                        text "#configurable";
                                                        symbool config;])]
  | Accessor ({getter=g; setter=s}, enum, config) ->
    horz [text ("'" ^ f ^ "'"); text ":"; braces (horz [text "#getter";
                                                        text (Store.print_loc g); text ",";
                                                        text "#setter";
                                                        text (Store.print_loc s)])]

and sym_prop fp = prop fp
and con_prop (f, p) = prop ("'" ^ f ^ "'", p)

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
and castFn t e = match t with
    | TNum -> parens (horz [text "num"; exp e])
    | TBool -> parens (horz [text "bool"; exp e])
    | TString -> parens (horz [text "string"; exp e])
    | TFun _ -> parens (horz [text "fun"; exp e])
    | TObj -> parens (horz [text "fields"; exp e])
    | _ -> exp e
and uncastFn t e = match t with
    | TNum -> parens (horz [text "NUM"; exp e])
    | TBool -> parens (horz [text "BOOL"; exp e])
    | TString -> parens (horz [text "STR"; exp e])
    | TFun _ -> parens (horz [text "FUN"; exp e])
    | TObj -> parens (horz [text "OBJ"; exp e])
    | _ -> exp e

and exp e = 
  match e with
  | Hint s -> horz [text ";;"; text s]
  | Concrete v -> value v
  | STime t -> horz[text "time:"; int t]
  | SLoc l -> horz[text "&"; text (Store.print_loc l)]
  | SId id -> text id
  | SOp1 (op, e) -> 
    (squish [text "prim"; parens (horz [text ("\"" ^ op ^ "\","); exp e])])
  | SOp2 (op, e1, e2) ->
    (squish [text "prim"; parens (horz [text ("\"" ^ op ^ "\","); 
                                        exp e1; text ","; exp e2])])
  | SApp (f, args) ->
    (squish [exp f; parens (squish (intersperse (text ", ") (map (fun a -> exp a) args)))])
  | SLet (id, e1) -> 
    squish [text "let"; text id; text "="; exp e1]
  | SCastJS (t, e) -> castFn t e
  | SUncastJS (t, e) -> uncastFn t e
  | SNot e -> parens (horz [text "!"; exp e])
  | SAnd es -> parens (horz (text "&&" :: (map (fun e -> exp e) es)))
  | SOr es -> parens (horz (text "||" :: (map (fun e -> exp e) es)))
  | SAssert e -> parens (horz [text "ASSERT"; exp e])
  | SImplies (pre, post) -> parens (horz [exp pre; text "=>"; exp post])
  | SIsMissing e ->
    horz [exp e; text "IS MISSING"]
  | SGetField (id, f) ->
    squish [text id; text "."; text f]

;;

(*let to_string x = x Format.str_formatter; Format.flush_str_formatter();;*)

let val_to_string = to_string value
let obj_to_string = to_string obj

let one_store store one_v = vert
  (map (fun (loc, v) -> horz [text (Store.print_loc loc);
                              text ":"; one_v v;])
      (Store.bindings store))

let store { objs = objs; vals = vals } =
   vert [ 
     text "--- Values:  ---";
     braces (one_store vals value); 
     text "--- Objects: ---"; 
     braces (one_store objs obj); ]
;;

let store_to_string = to_string store
