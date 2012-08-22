open Lexing

type id = string

module IdOrderedType = struct
  type t = id
  let compare = Pervasives.compare
end

module IdHashedType = struct
  type t = id
  let equal t1 t2 = t1 = t2
  let hash = Hashtbl.hash
end


module Pos = struct

  type t = Lexing.position * Lexing.position * bool (* start, end, is synthetic? *)

  let dummy = (Lexing.dummy_pos, Lexing.dummy_pos, true)
  let compare = Pervasives.compare

  let before (_, p1_end, _) (p2_start, _, _) = 
    p1_end.pos_cnum < p2_start.pos_cnum
    || p1_end.pos_lnum < p2_start.pos_lnum (* may not have cnum info from SpiderMonkey positions *)
    || p1_end.pos_bol < p2_start.pos_bol

  let synth (p_start, p_end, _) = (p_start, p_end, true)
  let synthetic (p_start, p_end) = (p_start, p_end, true)
  let real (p_start, p_end) = (p_start, p_end, false)
  let rangeToString p e =
    if (p.pos_lnum = e.pos_lnum) 
    then Format.sprintf "%s:%d:%d-%d" p.pos_fname p.pos_lnum (p.pos_cnum - p.pos_bol)
      (e.pos_cnum - e.pos_bol)
    else Format.sprintf "%s:%d:%d-%d:%d" p.pos_fname p.pos_lnum (p.pos_cnum - p.pos_bol)
      e.pos_lnum (e.pos_cnum - e.pos_bol)
  let string_of_pos (p, e, _) = rangeToString p e
  let toLexPos (s, e, _) = (s, e)
  let isSynthetic (_, _, synth) = synth
  let fname (s, e, _) = s.pos_fname

  (* let string_of_pos p = *)
  (*   Printf.sprintf "[%s]: Line %d, Col %d - Line %d, Col %d" *)
  (*     (fst p).Lexing.pos_fname *)
  (*     (fst p).Lexing.pos_lnum *)
  (*     (fst p).Lexing.pos_bol *)
  (*     (snd p).Lexing.pos_lnum *)
  (*     (snd p).Lexing.pos_bol *)
end


module Int = struct
  type t = int
  let compare = Pervasives.compare
end

module IntSet = SetExt.Make (Int)

module IdSet = SetExt.Make (IdOrderedType)

module PosSet = SetExt.Make (Pos)

module PosMap = MapExt.Make (Pos)

module IdMap = MapExt.Make (IdOrderedType)

module IdMapExt = MapExt.Make (IdOrderedType)

module IdHashtbl = Hashtbl.Make(IdHashedType)

let fold_left = List.fold_left

let fold_right = List.fold_right

let map = List.map

let printf = Printf.printf

let eprintf = Printf.eprintf

let sprintf = Printf.sprintf

let second2 f (a, b) = (a, f b)

let third3 f (a, b, c) = (a, b, f c)

(* let string_of_position (p, e) =  *)
(*   Format.sprintf "%s:%d:%d-%d" p.pos_fname p.pos_lnum (p.pos_cnum - p.pos_bol) *)
(*     (e.pos_cnum - e.pos_bol) *)

let snd3 (a, b, c) = b

let snd2 (a, b) = b

let fst2 (a, b) = a

let fst3 (a, _, _) = a

let thd3 (_, _, c) = c

let rec intersperse a lst = match lst with
    [] -> []
  | [x] -> [x]
  | x :: xs -> x :: a :: (intersperse a xs)

let rec take_while f xs = match xs with
    [] -> [], []
  | x :: xs' -> 
      if f x then
        let lhs, rhs = take_while f xs' in
          x :: lhs, rhs
      else
        [], xs

let rec match_while f xs = match xs with
    [] -> [], []
  | x :: xs' -> begin match f x with
        Some y ->
          let ys, xs'' = match_while f xs' in
            y :: ys, xs''
      | None -> [], xs
    end
    
let rec take n xs = match n, xs with
  | 0, _ -> []
  | _, [] -> []
  | _, x::xs -> x :: take (n-1) xs

let rec rem (elt : 'a) (lst : 'a list) : 'a list = match lst with
    [] -> []
  | x :: xs -> if elt = x then rem elt xs else x :: (rem elt xs)

let rec nub (lst : 'a list) : 'a list = match lst with
    [] -> []
  | x :: xs -> x :: (nub (rem x xs))

let rec iota' m lst = 
  if m < 0 then lst
  else iota' (m - 1) (m :: lst)

let iota n = iota' (n - 1) []

(* let flatmap f lst = List.concat (List.map f lst) *)

let curry f = (fun a b -> f(a,b))
let uncurry f = (fun (a,b) -> f a b)

let flip f = (fun a b -> f b a)

let group (cmp : ('a -> 'a -> int)) (lst : 'a list) : 'a list list =
  let sorted = List.sort cmp lst in
  List.fold_left
    (fun groups elt -> match groups with
      | [] -> [[elt]]
      | grp::grps ->
        if cmp elt (List.hd grp) = 0
        then (elt::grp)::grps
        else [elt]::grp::grps)
    [] sorted

let list_of_option opt = match opt with
  | None -> []
  | Some x -> [x]

let null list = match list with
  | [] -> true
  | _ -> false

let rec last list = match list with
  | [] -> failwith "Attempted to take last element of empty list."
  | [x] -> x
  | (x :: xs) -> last xs

let identity x = x

let rec compose fs x = match fs with
  | [] -> x
  | (f :: fs) -> let x = f x in compose fs x

let apply f list = compose (List.map f list)

let rec repeat n f x =
  if n = 0
  then x
  else repeat (n - 1) f (f x)

(* Brent's Algorithm. Returns empty list if there is no cycle. *)
let find_cycle (first : 'a) (next : 'a -> 'a option) (equals : 'a -> 'a -> bool) : 'a list =
  let rec find_cycle tortoise hare power loop_len loop =
    if equals tortoise hare
    then (hare :: loop)
    else match next hare with
    | None -> []
    | Some hare' ->
      if power = loop_len
      then find_cycle hare hare' (power * 2) 1 []
      else find_cycle tortoise hare' power (loop_len + 1) (hare :: loop) in
  match next first with
  | None -> []
  | Some second -> find_cycle first second 1 1 []

(* Read a file into a string *)
let string_of_file file_name =
  let inchan = open_in file_name in
  let buf = String.create (in_channel_length inchan) in
  really_input inchan buf 0 (in_channel_length inchan);
  buf
