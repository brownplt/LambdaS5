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

val compare : t -> t -> int

val string : t -> string

val get : string -> t -> t

val list : t -> t list

val is_null : t -> bool

val is_array : t -> bool

val bool : t -> bool
