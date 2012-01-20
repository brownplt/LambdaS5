open Format
open FormatExt
open Prelude

let loc = ref 0

module Loc = struct
  type t = int
  let compare = Pervasives.compare
end
module LocMap = Map.Make (Loc)
type loc = int
let newLoc () : Loc.t =
  loc := !loc + 1;
  !loc
let distinct loc1 loc2 = (loc1 <> loc2)
let print_loc loc = (string_of_int loc)
type 'a t = 'a LocMap.t
let empty = LocMap.empty
let alloc valu store = 
  let loc = newLoc () in 
  (loc, LocMap.add loc valu store)
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
