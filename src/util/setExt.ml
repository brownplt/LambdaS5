open Format
open FormatExt

module type S = sig
  include Set.S

  val unions : t list -> t
  val from_list : elt list -> t
  val from_option : elt option -> t
  val to_list : t -> elt list
  val p_set : (elt -> printer) -> t -> printer
  val fix_point : (elt -> t) -> t -> t
end

module Make (Ord : Set.OrderedType) = struct

  include Set.Make(Ord)

  let unions lst = List.fold_left union empty lst

  let from_list lst = 
    List.fold_left (fun set x -> add x set) empty lst

  let from_option opt = match opt with
    | None -> empty
    | Some x -> singleton x

  let to_list set =
    fold (fun e lst -> e :: lst) set []    

  let p_set p_elt set = 
    braces (horz (List.map p_elt (to_list set)))

  let rec fix_point gen set =
    let set' = union set (unions (List.map gen (to_list set))) in
    if set == set' then set else fix_point gen set'

end
