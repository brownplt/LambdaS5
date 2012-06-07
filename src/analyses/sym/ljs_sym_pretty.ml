open Prelude
open Ljs_sym_values

open Format
open FormatExt

let print_hidden = false
let verbose_objs = true

let rec vert_intersperse a lst = match lst with
  | [] -> []
  | [x] -> [x]
  | x :: xs -> squish [x; a] :: (vert_intersperse a xs)

let sbool b = match b with
  | BTrue -> text "true" 
  | BFalse -> text "false"
  | BSym id -> text id 
let sstring s = match s with
  | SString str -> text str 
  | SSym id -> text id 

let rec value (v, rec_stuff) = 
  match v with
  | Null -> text "null"
  | Undefined -> text "undefined"
  | Num n -> text (string_of_float n)
  | String s -> text ("\"" ^ s ^ "\"")
  | True -> text "true"
  | False -> text "false"
  | ObjPtr loc -> begin
    let loc_box = horz [squish [text "&<"; text (Store.print_loc loc); text ">"]] in
    match rec_stuff with
    | Some (pc, inv_env, seen_locs) -> 
      let o, hide = sto_lookup_obj_pair loc pc in
      begin try
        horz [squish (intersperse (text ", ")
              (map text (Store.lookup loc inv_env)))]
      with Not_found ->
      (*printf "o: %s\n" (Store.print_loc loc);*)
        if List.mem loc seen_locs
          || (hide && not print_hidden)
        then loc_box
        else horz 
          (if verbose_objs then [loc_box; text ":";] else []
          @ [obj ((o, hide), Some (pc, inv_env, loc::seen_locs))])
      end
    | None -> loc_box
  end
  | Closure func -> text "(closure)"
  (* | Lambda (p,lbl, ret, exn, xs, e) -> *)
  (*   label verbose lbl (vert [squish [text "lam"; parens (horz (text "Ret" :: text ret :: text "," :: *)
  (*                                                                text "Exn" :: text exn :: text ";" ::  *)
  (*                                                                (intersperse (text ",") (map text xs))))]; *)
  (*                            braces (exp e)]) *)
  | SymScalar id -> text id
  | NewSym (id, locs) -> horz [text ("NewSym " ^ id);
                               brackets (horz (map (fun loc -> text (Store.print_loc loc)) locs))]
                                 
and obj ((o, hide), rec_stuff) =
  let hide_str = if hide then "hidden" else "" in
  match o with
  | NewSymObj locs ->
    horz ([text hide_str; text "NewSymObj";]
    @ if not verbose_objs then [] else
    [brackets (horz (map (fun loc -> text (Store.print_loc loc)) locs))])
  | SymObj f -> helper f (hide_str ^ "@sym") rec_stuff
  | ConObj f -> helper f (hide_str ^ "@") rec_stuff
and helper { attrs = attrsv; conps = conpsv; symps = sympsv; } prefix rec_stuff = 
  let do_val =
    match rec_stuff with
    | Some (pc, inv_env, _) ->
        (fun vloc ->
          (*printf "v: %s\n" (Store.print_loc vloc);*)
           value (sto_lookup_val vloc pc, rec_stuff))
    | None -> (fun vloc -> text (Store.print_loc vloc))
  in
  if IdMap.is_empty conpsv && IdMap.is_empty sympsv 
  then squish [text prefix; braces (attrs attrsv do_val)]
  else 
    horz [squish [text prefix; (braces (vert
    ( [attrs attrsv do_val]
      @ if IdMap.is_empty conpsv then [] else
      [text "- Con fields -";
       vert (vert_intersperse (text ",")
               (map (fun p -> con_prop p do_val) (IdMap.bindings conpsv)))]
      @ if IdMap.is_empty sympsv then [] else
      [text "- Sym fields -";
       vert (vert_intersperse (text ",")
               (map (fun p -> sym_prop p do_val) (IdMap.bindings sympsv)))]
    )))]]


and attrs { proto = p; code = c; extensible = b; klass = k } do_val =
  let proto = [horz [text "#proto:"; do_val p]] in
  let code = match c with None -> [] 
    | Some e -> [horz [text "#code:"; do_val p]] in
  brackets (horzOrVert
              (map (fun x -> squish [x; (text ",")])
                          (proto @ if not verbose_objs then [] else
                           code @
                           [horz [text "#class:"; sstring k]; 
                            horz [text "#extensible:"; sbool b]])))

and prop (f, prop) do_val =
  match prop with
  | Data ({value=v; writable=w}, enum, config) ->
    horz [text f; text ":";
    if not verbose_objs then do_val v else
    braces (horz
    [text "#value"; do_val v; text ",";
     text "#writable";  sbool w; text ",";
     text "#enumerable"; sbool enum; text ",";
     text "#configurable"; sbool config;])]
  | Accessor ({getter=g; setter=s}, enum, config) ->
    horz [text ("'" ^ f ^ "'"); text ":";
    if not verbose_objs then text "[accessors]" else
    braces (horz
    [text "#getter"; do_val g; text ",";
     text "#setter"; do_val s])]

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
(*and castFn t e pc = match t with*)
(*    | TNum -> parens (horz [text "num"; exp e pc])*)
(*    | TBool -> parens (horz [text "bool"; exp e pc])*)
(*    | TString -> parens (horz [text "string"; exp e pc])*)
(*    | TFun _ -> parens (horz [text "fun"; exp e pc])*)
(*    | TObjPtr -> parens (horz [text "objptr"; exp e pc])*)
(*    | _ -> exp e pc*)
(*and uncastFn t e pc = match t with*)
(*    | TNum -> parens (horz [text "NUM"; exp e pc])*)
(*    | TBool -> parens (horz [text "BOOL"; exp e pc])*)
(*    | TString -> parens (horz [text "STR"; exp e pc])*)
(*    | TFun _ -> parens (horz [text "FUN"; exp e pc])*)
(*    | TObjPtr -> parens (horz [text "OBJPTR"; exp e pc])*)
(*    | _ -> exp e pc*)

(*and exp e pc = *)
(*  match e with*)
(*  | Hint s -> horz [text ";;"; text s]*)
(*  | Concrete v -> value (v, pc)*)
(*  | STime t -> horz[text "time:"; int t]*)
(*  | SLoc l -> horz[text "&"; text (Store.print_loc l)]*)
(*  | SId id -> text id*)
(*  | SOp1 (op, e) -> *)
(*    (squish [text "prim"; parens (horz [text ("\"" ^ op ^ "\","); exp e pc])])*)
(*  | SOp2 (op, e1, e2) ->*)
(*    (squish [text "prim"; parens (horz [text ("\"" ^ op ^ "\","); *)
(*                                        exp e1 pc; text ","; exp e2 pc])])*)
(*  | SApp (f, args) ->*)
(*    (squish [exp f pc; parens (squish (intersperse (text ", ") (map (fun a -> exp a pc) args)))])*)
(*  | SLet (id, e1) -> *)
(*    squish [text "let"; text id; text "="; exp e1 pc]*)
(*  | SCastJS (t, e) -> castFn t e pc*)
(*  | SUncastJS (t, e) -> uncastFn t e pc*)
(*  | SNot e -> parens (horz [text "!"; exp e pc])*)
(*  | SAnd es -> parens (horz (text "&&" :: (map (fun e -> exp e pc) es)))*)
(*  | SOr es -> parens (horz (text "||" :: (map (fun e -> exp e pc) es)))*)
(*  | SAssert e -> parens (horz [text "ASSERT"; exp e pc])*)
(*  | SImplies (pre, post) -> parens (horz [exp pre pc; text "=>"; exp post pc])*)
(*  | SIsMissing e ->*)
(*    horz [exp e pc; text "IS MISSING"]*)
(*  | SGetField (id, f) ->*)
(*    squish [text id; text "."; text f]*)

;;

(*let to_string x = x Format.str_formatter; Format.flush_str_formatter();;*)
let updateWith f k v m =
  Store.update k
    (try f v (Store.lookup k m)
    with Not_found -> v) m

let invert_env pc : (id list) Store.t =
  IdMap.fold
    (fun id vloc inv_map ->
      match sto_lookup_val vloc pc with
      | ObjPtr oloc -> updateWith (@) oloc [id] inv_map
      | _ -> inv_map)
    pc.print_env
    Store.empty

let val_to_string v = to_string value (v, None)
let rec_val_to_string v pc = to_string value (v, Some (pc, invert_env pc, []))
let obj_to_string o = to_string obj (o, None)
let rec_obj_to_string o pc = to_string obj (o, Some (pc, invert_env pc, []))

let one_store store one_v is_hidden = vert
  (map (fun (loc, v) -> 
          if is_hidden v && not print_hidden
          then (fun _ -> ())
          else horz [text (Store.print_loc loc);
                     text ":"; one_v (v, None);])
      (Store.bindings store))

let store { objs = objs; vals = vals } =
   vert [ 
     text "--- Values:  ---";
     braces (one_store vals value (fun _ -> false)); 
     text "--- Objects: ---"; 
     braces (one_store objs obj snd); ]
;;

let store_to_string = to_string store

let env env_map = vert
  (map (fun (id, loc) ->
         horz [text id; text ":"; 
               text (Store.print_loc loc);])
       (IdMap.bindings env_map))

let env_to_string = to_string env

