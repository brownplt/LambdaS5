type id = string


module Pos : sig
  type t = Lexing.position * Lexing.position * bool (* start, end, is synthetic? *)
  val dummy : t
  val compare : t -> t -> int
  val before : t -> t -> bool
  val synth : t -> t
  val synthetic : Lexing.position * Lexing.position -> t
  val real : Lexing.position * Lexing.position -> t
  val rangeToString : Lexing.position -> Lexing.position -> string
  val string_of_pos : t -> string
  val toLexPos : t -> Lexing.position * Lexing.position
  val isSynthetic : t -> bool
  val fname : t -> string
end

module IntSet : Set.S
  with type elt = int

module IntSetExt : SetExt.S
  with type elt = int
  and type t = IntSet.t

module IdSet : Set.S 
  with type elt = id

module IdSetExt : SetExt.S 
  with type elt = id 
  and type t = IdSet.t

module IdHashtbl : Hashtbl.S
  with type key = id

module PosSet : Set.S 
  with type elt = Pos.t

module PosSetExt : SetExt.S 
  with type elt = Pos.t
  and type t = PosSet.t

module PosMap : Map.S
  with type key = Pos.t

module PosMapExt : MapExt.S
  with type key = Pos.t
  with type +'a t = 'a PosMap.t

module IdMap : Map.S
  with type key = id

module IdMapExt : MapExt.S
  with type key = id
  with type +'a t = 'a IdMap.t


val fold_left : ('a -> 'b -> 'a) -> 'a -> 'b list -> 'a

val fold_right : ('a -> 'b -> 'b) -> 'a list -> 'b -> 'b

val map : ('a -> 'b) -> 'a list -> 'b list

val second2 : ('b -> 'c) -> 'a * 'b -> 'a * 'c

val third3 : ('c -> 'd) -> 'a * 'b * 'c -> 'a * 'b * 'd

val snd3 : 'a * 'b * 'c -> 'b

val snd2 : 'a * 'b -> 'b

val fst2 : 'a * 'b -> 'a

val fst3 : 'a * 'b * 'c -> 'a

val thd3 : 'a * 'b * 'c -> 'c

val printf : ('a, out_channel, unit) format -> 'a

val eprintf : ('a, out_channel, unit) format -> 'a

val sprintf : ('a, unit, string) format -> 'a

val intersperse : 'a -> 'a list -> 'a list

val take_while : ('a -> bool) -> 'a list -> 'a list * 'a list

val match_while : ( 'a -> 'b option) -> 'a list -> 'b list * 'a list

(** [nub lst] removes duplicates from the [lst]. Duplicates are identified by
    structural equality. *)
val nub : 'a list -> 'a list

(** [iota n] returns the list of integers [0] through [n-1], inclusive. *)
val iota : int -> int list

val curry : ('a * 'b -> 'c) -> ('a -> 'b -> 'c)
val uncurry : ('a -> 'b -> 'c) -> ('a * 'b -> 'c)

(** [group cmp lst] collects like elts of [lst] into lists using [cmp] to check equality.
  * Returns a list of lists, where all like elts are in one sublist *)
val group : ('a -> 'a -> int) -> 'a list -> 'a list list 
