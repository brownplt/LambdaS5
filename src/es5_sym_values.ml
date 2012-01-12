open Prelude
open Es5_syntax

type value =
  | Null
  | Undefined
  | Num of float
  | String of string
  | True
  | False
      (* A VarCell can contain an ObjCell, but not vice versa.  This
      mimics the semantics of heap-like object refs alongside mutable
      variables *)
  | VarCell of value ref 
      (* Objects shouldn't have VarCells in them, but can have any of
      the other kinds of values *)
  | ObjCell of (attrsv * (propv IdMap.t)) ref
  | Closure of (value list -> path -> int -> result list)
  | Fail of string
  | Sym of sym_exp (* symbolic expression *)
and 
  sym_exp =
  | Concrete of value 
  | SId of id
  | SOp1 of string * sym_exp
  | SOp2 of string * sym_exp * sym_exp
  | SApp of sym_exp * sym_exp list
and result = value * path

and path = { constraints : sym_exp list;
             vars : var list; }

and var = id * string

and
  attrsv = { code : value option;
             proto : value;
             extensible : bool;
             klass : string;
             primval : value option; }
and
  propv = 
  | Data of datav * bool * bool
  | Accessor of accessorv * bool * bool
and datav = { value : value; writable : bool; }
and accessorv = { getter : value; setter : value; }

let d_attrsv = { primval = None;
                 code = None; 
                 proto = Undefined; 
                 extensible = false; 
                 klass = "LambdaJS internal"; }

type env = value IdMap.t
type label = string

exception Break of label * value
exception Throw of value

let rec pretty_value v = match v with 
  | Num d -> string_of_float d
  | String s -> "\"" ^ s ^ "\""
  | True -> "true"
  | False -> "false"
  | Undefined -> "undefined"
  | Null -> "null"
  | Closure c -> "function"
  | ObjCell o -> "object"
  | VarCell v -> "&<" ^ pretty_value !v ^ ">"
  | Fail s -> "[fail: " ^ s ^ "]"
  | Sym e -> "Sym(" ^ pretty_sym_exp e ^ ")"

and pretty_sym_exp e = match e with
  | Concrete v -> pretty_value v
  | SId x -> x
  | SOp1 (op, e) -> "(" ^ op ^ " " ^ (pretty_sym_exp e) ^ ")"
  | SOp2 (op, l, r) -> "(" ^ op ^ " " ^ (pretty_sym_exp l) 
    ^ " " ^ (pretty_sym_exp r) ^ ")"
  | SApp (f, args) -> 
    "(" ^ (pretty_sym_exp f) ^ " " ^ (String.concat " " (map pretty_sym_exp args)) ^ ")"

let rec pretty_value_list vs = match vs with
  | (v::vs) -> pretty_value v ^ ", " ^ pretty_value_list vs
  | [] -> ""

let mtPath = { constraints = []; vars = []; }
