open Format
open FormatExt
open Prelude

let loc = ref 0

type loc = int

module Loc = struct
  type t = int
  let compare = Pervasives.compare
end

module LocMap = MapExt.Make (Loc)
module LocSet = SetExt.Make (Loc)

let newLoc () : Loc.t =
  loc := !loc + 1;
  !loc

let distinct loc1 loc2 = (loc1 <> loc2)
let print_loc loc = (string_of_int loc)
let alloc valu store = 
  let loc = newLoc () in 
  (loc, LocMap.add loc valu store)


type 'a t = 'a LocMap.t
let empty = LocMap.empty
let update = LocMap.add
let free = LocMap.remove 
let mem = LocMap.mem
let lookup = LocMap.find 
let iter = LocMap.iter
let fold = LocMap.fold
let for_all = LocMap.for_all
let exists = LocMap.exists
let filter = LocMap.filter
let partition = LocMap.partition
let cardinal = LocMap.cardinal
let bindings = LocMap.bindings
let map = LocMap.map
let mapi = LocMap.mapi

(* This may NOT be called during evaluation *)
let unsafe_store_reset () =
  loc := 0
