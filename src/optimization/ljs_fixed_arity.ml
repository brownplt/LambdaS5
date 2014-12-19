open Prelude
open Ljs_syntax
open Ljs_opt

(* take out argument declaration exp, and return ordered formal
   parameters *)
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

let parse_args_obj (args : exp list) : exp list option =
  let get_field_values (obj : exp) : exp list option =
    let rec get_values props = match props with
      | [] -> []
      | (s, Data({value=value}, _, _)) :: tl ->
        value :: get_values tl
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
  in
  match args with
  | match_this :: [App (_, Id (_, "%mkArgsObj"), [argobj])] ->
    begin match get_field_values argobj with
      | Some (lst) -> Some (match_this :: lst)
      | None -> None
    end
  | _ -> None
  
let fixed_arity (exp : exp) : exp =
  let rec fixed_formal_parameter (exp : exp) : exp =
    match exp with
    | Lambda (pos, xs, body) ->
      let args, new_body = trim_args body in
      let new_xs = update_args xs args in
      Lambda (pos, new_xs, fixed_formal_parameter new_body)
    | _ ->
      optimize fixed_formal_parameter exp
  in
  let rec fixed_call_site (exp : exp) : exp =
    match exp with
    | App (p, f, args) ->
      let f = fixed_call_site f in
      begin match parse_args_obj args with
      | Some (arg_list) ->
        App (p, f, arg_list)
      | None ->
        let args = List.map fixed_call_site args in
        App (p, f, args)
      end
    | _ -> optimize fixed_call_site exp
  in
  let e1 = fixed_formal_parameter exp in
  let e2 = fixed_call_site e1 in
  e2
