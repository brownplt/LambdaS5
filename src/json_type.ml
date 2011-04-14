type json_type =
    Object of (string * json_type) list
  | Array of json_type list
  | String of string
  | Int of int
  | Float of float
  | Bool of bool
  | Null

type t = json_type

exception Json_error of string

let compare = Pervasives.compare

let string v = match v with
  | String s -> s
  | _ -> raise (Json_error "expected a JSON string")

let get key v = match v with
  | Object pairs -> 
    begin try List.assoc key pairs
      with Not_found -> raise (Json_error ("expected a " ^ key ^ "field"))
    end
  | _ -> raise (Json_error "expected a JSON object")

let list v = match v with
  | Array lst -> lst
  | _ -> raise (Json_error "expected a JSON array")

let is_null v = match v with
  | Null -> true
  | _ -> false
