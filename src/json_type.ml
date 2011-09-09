open Printf
open Format
open FormatExt

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
  | Array _ -> raise (Json_error "expected a JSON string, got a JSON array")
  | Object _ -> raise (Json_error "expected a JSON string, got a JSON object")
  | Int _ -> raise (Json_error "expected a JSON string, got a JSON int")
  | Float _ -> raise (Json_error "expected a JSON string, got a JSON float")
  | Bool _ -> raise (Json_error "expected a JSON string, got a JSON bool")
  | Null -> raise (Json_error "expected a JSON string, got a JSON null")

let int v = match v with
  | Int i -> i
  | Array _ -> raise (Json_error "expected a JSON int, got a JSON array")
  | Object _ -> raise (Json_error "expected a JSON int, got a JSON object")
  | String _ -> raise (Json_error "expected a JSON int, got a JSON string")
  | Float _ -> raise (Json_error "expected a JSON int, got a JSON float")
  | Bool _ -> raise (Json_error "expected a JSON int, got a JSON bool")
  | Null -> raise (Json_error "expected a JSON int, got a JSON null")

let float v = match v with
  | Float f -> f
  | Array _ -> raise (Json_error "expected a JSON float, got a JSON array")
  | Object _ -> raise (Json_error "expected a JSON float, got a JSON object")
  | String _ -> raise (Json_error "expected a JSON float, got a JSON string")
  | Int _ -> raise (Json_error "expected a JSON float, got a JSON int")
  | Bool _ -> raise (Json_error "expected a JSON float, got a JSON bool")
  | Null -> raise (Json_error "expected a JSON float, got a JSON null")

let get key v = match v with
  | Object pairs -> 
    begin try List.assoc key pairs
      with Not_found -> 
        raise (Json_error ("expected a " ^ key ^ " field in " ^
                              (FormatExt.to_string (fun i -> (braces (horz (List.map text i)))) (List.map fst pairs))))
        
    end
  | _ -> raise (Json_error (sprintf "expected a JSON object %s" key))

let list v = match v with
  | Array lst -> lst
  | _ -> raise (Json_error "expected a JSON array")

let is_null v = match v with
  | Null -> true
  | _ -> false

let is_array v = match v with
  | Array _ -> true
  | _ -> false

let bool v = match v with
  | Bool b -> b
  | _ -> raise (Json_error "expected boolean")
