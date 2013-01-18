module GC = Ljs_gc
module P = Prelude
module S = Ljs_syntax
module V = Ljs_values
module LocSet = Store.LocSet

(* CESK machine-specific closures *)
type clos =
| ExpClos of S.exp * V.env
| ValClos of V.value * V.env
| AttrExpClos of S.attrs * V.env
| AttrValClos of V.attrsv * V.env
| PropExpClos of (string * S.prop) * V.env
| PropValClos of (string * V.propv) * V.env
| LobClos of exn (* bit of a misnomer, since there's no env *)

let exp_of clos = match clos with
  | ExpClos (expr, _) -> Some expr
  | _ -> None
let env_of clos = match clos with
  | ExpClos (_, env) -> Some env
  | _ -> None
let env_of_any clos = match clos with
  | ExpClos (_, env) -> env
  | ValClos (_, env) -> env
  | AttrExpClos  (_, env) -> env
  | AttrValClos  (_, env) -> env
  | PropExpClos  (_, env) -> env
  | PropValClos  (_, env) -> env
  | LobClos  _ -> P.IdMap.empty
let add_opt clos xs f = match f clos with
  | Some x -> x::xs
  | None -> xs

let locs_of_clos clo = match clo with
  | ExpClos (_, e) -> GC.locs_of_env e
  | ValClos (v, e) -> LocSet.union (GC.locs_of_value v) (GC.locs_of_env e)
  | AttrExpClos (_, e) -> GC.locs_of_env e
  | AttrValClos (_, e) -> GC.locs_of_env e
  | PropExpClos (_, e) -> GC.locs_of_env e
  | PropValClos (_, e) -> GC.locs_of_env e
  | LobClos _      -> LocSet.empty
