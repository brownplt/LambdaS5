open FormatExt

module type S = sig
  include Map.S

  val from_list : (key * 'a) list -> 'a t
  val to_list : 'a t -> (key * 'a) list
  val keys : 'a t -> key list
  val values : 'a t -> 'a list
  val union : ('a -> 'a -> 'a) -> 'a t -> 'a t -> 'a t
  val join : (key -> 'a -> 'a -> 'a) -> 'a t -> 'a t -> 'a t
  val p_map : (key -> printer) -> ('a -> printer) -> 'a t -> printer
  val diff : 'a t -> 'a t -> 'a t
  val filter : (key -> 'a -> bool) -> 'a t -> 'a t
end

module Make (Ord: Map.OrderedType) = struct

  include Map.Make(Ord)

  let from_list lst = 
    List.fold_left (fun m (k, v) -> add k v m) empty lst

  let to_list m = 
    fold (fun k v lst -> (k, v) :: lst) m []

  let keys m =
      fold (fun k _ lst -> k :: lst) m []

  let values m =
      fold (fun _ v lst -> v :: lst) m []

  (* NOTE(jonah): This doesn't really look like a union to me...*)
  let union f m1 m2 = 
    let rec g (k1, v1) (k2, v2) =
      if Ord.compare k1 k2 = 0 then (k1, f v1 v2)
      else raise Not_found
    in from_list (List.map2 g (to_list m1) (to_list m2))

  let join f m1 m2 =
    let mk k v acc = 
      if mem k acc then 
        add k (f k v (find k acc)) acc (* f m1-val  m2-val *)
      else 
        add k v acc
    in fold mk m1 m2 (* m2 is the accumulator *)

  let p_map p_key p_val t = 
    vert (List.map (fun (k, v) -> brackets (horz [ p_key k; p_val v ]))
            (to_list t))

  let diff m1 m2 = 
    let fn key v acc =
      if mem key m2 then acc else add key v acc in
      fold fn m1 empty

  let filter f m = 
    let g k v m' = if f k v then add k v m' else m' in
      fold g m empty
     

end
