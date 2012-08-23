open Format
open FormatExt
open Prelude

type loc = int

module Loc = struct
  type t = loc
  let compare = Pervasives.compare
end

module LocMap = MapExt.Make (Loc)
module LocSet = SetExt.Make (Loc)

let distinct loc1 loc2 = (loc1 <> loc2)
let print_loc loc = (string_of_int loc)

let alloc valu (store, loc) =
  (loc, (LocMap.add loc valu store, loc + 1))

let lift0 f (store, loc) = (f store, loc)
let lift1 f x = lift0 (f x)
let lift2 f x y = lift0 (f x y)
let app0 f (store, loc) = f store
let app1 f x = app0 (f x)
let app2 f x y = app0 (f x y)

type 'a t = 'a LocMap.t * loc
let empty = (LocMap.empty, 0)
let update x y = lift2 LocMap.add x y
(* You'd really like to take the x out, wouldn't you?
   Try it. I dare you. *)
let free x = lift1 LocMap.remove x
let mem x = app1 LocMap.mem x
let lookup x = app1 LocMap.find x
let iter x = app1 LocMap.iter x
let fold f (store, _) v = LocMap.fold f store v
let for_all x = app1 LocMap.for_all x
let exists x = app1 LocMap.exists x
let filter x = lift1 LocMap.filter x
let cardinal x = app0 LocMap.cardinal x
let bindings x = app0 LocMap.bindings x
let map x = lift1 LocMap.map x
let mapi x = lift1 LocMap.mapi x
let to_map = fst
let values x = app0 LocMap.values x
let keys x = app0 LocMap.keys x
