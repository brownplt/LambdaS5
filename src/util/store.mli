open Format
open FormatExt
open Prelude

type loc
module LocSet : SetExt.S with type elt = loc
module LocMap : MapExt.S with type key = loc

type +'a t = 'a LocMap.t
val distinct : loc -> loc -> bool
val print_loc : loc -> string
val alloc : 'a -> 'a t -> loc * 'a t

val empty : 'a t
val update : loc -> 'a -> 'a t -> 'a t
val free : loc -> 'a t -> 'a t
val mem : loc -> 'a t -> bool
val lookup : loc -> 'a t -> 'a
val iter : (loc -> 'a -> unit) -> 'a t -> unit
val fold : (loc -> 'a -> 'b -> 'b) -> 'a t -> 'b -> 'b
val for_all : (loc -> 'a -> bool) -> 'a t -> bool
val exists : (loc -> 'a -> bool) -> 'a t -> bool
val filter : (loc -> 'a -> bool) -> 'a t -> 'a t
val partition : (loc -> 'a -> bool) -> 'a t -> 'a t * 'a t
val cardinal : 'a t -> int
val bindings : 'a t -> (loc * 'a) list
val map : ('a -> 'b) -> 'a t -> 'b t
val mapi : (loc -> 'a -> 'b) -> 'a t -> 'b t

val unsafe_store_reset : unit -> unit
