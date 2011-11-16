open Prelude
module E = Es5_cps
module V = Es5_cps_values
open Format
open FormatExt

(* module type Lattice = sig *)
(*   type t *)
(*   val _Top : unit -> t *)
(*   val _Bot : unit -> t *)
(*   val meet : t list -> t *)
(*   val join : t list -> t *)
(*   val pretty : t -> Format.formatter *)
(* end *)

(* module type SET_LATTICE = sig  *)
(*   type s *)
(*   type elt *)
(*   type t = Bot | Set of s | Top *)
(*   val _Top : unit -> t *)
(*   val _Bot : unit -> t *)
(*   val meet : t list -> t *)
(*   val join : t list -> t *)
(*   val elements : s -> elt list *)
(*   val inject : elt -> t *)
(*   val pretty : (elt -> FormatExt.printer) -> t -> FormatExt.printer *)
(* end *)
(* module SetLattice (S : Set.S) : SET_LATTICE with type s = S.t with type elt = S.elt = struct *)
(*   type s = S.t *)
(*   type elt = S.elt *)
(*   type t = Bot | Set of s | Top *)
(*   let _Bot () = Bot *)
(*   let _Top () = Top *)
(*   let join ts =  *)
(*     let join' t1 t2 = match (t1, t2) with *)
(*       | Bot, t *)
(*       | t, Bot -> t *)
(*       | _, Top *)
(*       | Top, _ -> Top *)
(*       | Set s1, Set s2 -> Set (S.union s1 s2) *)
(*     in List.fold_left join' Bot ts *)
(*   let meet ts = *)
(*     let meet' t1 t2 = match (t1, t2) with *)
(*       | Top, t *)
(*       | t, Top -> t *)
(*       | Bot, _ *)
(*       | _, Bot -> Bot *)
(*       | Set s1, Set s2 -> Set (S.inter s1 s2) *)
(*     in List.fold_left meet' Top ts *)
(*   let elements set = S.elements set *)
(*   let pretty eltPrint v = match v with *)
(*     | Bot -> text "Set:Bot" *)
(*     | Top -> text "Set:Top" *)
(*     | Set s -> braces (vert (S.fold (fun e acc -> (eltPrint e)::acc) s [])) *)
(*   let inject e = Set (S.singleton e) *)
(* end *)

module CLOSURE = struct
  type t = id * id * id list * E.cps_exp * V.bindingEnv * V.retContEnv * V.exnContEnv
  let compare = Pervasives.compare
  let pretty (ret,exn,args,_,_,_,_) = horz [squish [text "\\("; text ret; text ", "; text exn; text " ;"];
                                            squish (List.map text args);
                                            text ")"]
end

module AddressSet = Set.Make(V.ADDRESS)
module ClosureSet = Set.Make(CLOSURE)

module rec BoolLattice : sig
  type t =
    | Bot 
    | TrueTypeof of StringLattice.typeofStrings * ValueLattice.t
    | True 
    | FalseTypeof of StringLattice.typeofStrings * ValueLattice.t
    | False
    | Bool
  val _Top : unit -> t
  val _Bot : unit -> t
  val meet : t list -> t
  val join : t list -> t
  val inject : bool -> t
  val injectTypeof : bool * ValueLattice.t * StringLattice.typeofStrings -> t
  val eq : t -> t -> BoolLattice.t
  val pretty : t -> FormatExt.printer
end = struct
  type t = 
    | Bot 
    | TrueTypeof of StringLattice.typeofStrings * ValueLattice.t
    | True 
    | FalseTypeof of StringLattice.typeofStrings * ValueLattice.t
    | False
    | Bool
  let _Top () = Bool
  let _Bot () = Bot
  let join ts =
    let join' t1 t2 = match (t1, t2) with
      | _, Bool
      | Bool, _ -> Bool
      | True, False
      | False, True 
      | TrueTypeof _, False
      | FalseTypeof _, True
      | False, TrueTypeof _
      | True, FalseTypeof _
      | FalseTypeof _, TrueTypeof _
      | TrueTypeof _, FalseTypeof _ -> Bool
      | TrueTypeof (t1, i1), TrueTypeof (t2, i2) -> if t1 = t2 && i1 = i2 then TrueTypeof (t1, i1) else True
      | FalseTypeof (t1, i1), FalseTypeof (t2, i2) -> if t1 = t2 && i1 = i2 then FalseTypeof (t1, i1) else False
      | True, True
      | True, TrueTypeof _ 
      | TrueTypeof _, True -> True
      | False, False
      | False, FalseTypeof _
      | FalseTypeof _, False -> False
      | Bot, t
      | t, Bot -> t
    in List.fold_left join' (_Bot ()) ts
  let meet ts =
    let meet' t1 t2 = match (t1, t2) with
      | Bot, _
      | _, Bot -> Bot
      | False, False -> False
      | True, True -> True
      | TrueTypeof (t1, i1), TrueTypeof (t2, i2) -> if t1 = t2 && i1 = i2 then TrueTypeof (t1, i1) else Bot
      | FalseTypeof (t1, i1), FalseTypeof (t2, i2) -> if t1 = t2 && i1 = i2 then FalseTypeof (t1, i1) else Bot
      | TrueTypeof (t, id), True
      | True, TrueTypeof (t, id) -> TrueTypeof (t, id)
      | FalseTypeof (t, id), False
      | False, FalseTypeof (t, id) -> FalseTypeof (t, id)
      | False, True
      | True, False
      | TrueTypeof _, False
      | FalseTypeof _, True
      | False, TrueTypeof _
      | True, FalseTypeof _
      | FalseTypeof _, TrueTypeof _
      | TrueTypeof _, FalseTypeof _  -> Bot
      | Bool, t
      | t, Bool -> t
    in List.fold_left meet' (_Top ()) ts
  let inject b = if b then True else False
  let injectTypeof (b, id, ty) = if b then TrueTypeof (ty, id) else FalseTypeof (ty, id)
  let eq b1 b2 = match (b1, b2) with
    | Bot, Bot
    | True, True
    | True, TrueTypeof _
    | TrueTypeof _, True
    | False, False
    | False, FalseTypeof _
    | FalseTypeof _, False -> True
    | Bool, Bool -> Bool
    | _ -> False
  let pretty b = match b with
    | Bot -> text "Bool:Bot"
    | True -> text "True"
    | False -> text "False"
    | TrueTypeof (t, _) -> horz [squish [text "True{"; text (StringLattice.stringofTypeof t); text "}"]]
    | FalseTypeof (t, _) -> horz [squish [text "False{"; text (StringLattice.stringofTypeof t); text "}"]]
    | Bool -> text "Bool:Top"
end
and UndefLattice : sig
  type t = Bot | Undef
  val _Top : unit -> t
  val _Bot : unit -> t
  val meet : t list -> t
  val join : t list -> t
  val eq : t -> t -> BoolLattice.t
  val pretty : t -> FormatExt.printer
end = struct
  type t = Bot | Undef
  let _Top () = Undef
  let _Bot () = Bot
  let join ts =
    let join' t1 t2 = match (t1, t2) with
      | Undef, _
      | _, Undef -> Undef
      | _ -> Bot
    in List.fold_left join' (_Bot ()) ts
  let meet ts =
    let meet' t1 t2 = match (t1, t2) with
      | Bot, _
      | _, Bot -> Bot
      | _ -> Undef
    in List.fold_left meet' (_Top ()) ts
  let eq u1 u2 = match (u1, u2) with
    | Bot, Bot
    | Undef, Undef -> BoolLattice.inject true
    | _ -> BoolLattice.inject false
  let pretty u = match u with
    | Bot -> text "Undef:Bot"
    | Undef -> text "Undef"
end
and NullLattice : sig
  type t = Bot | Null
  val _Top : unit -> t
  val _Bot : unit -> t
  val meet : t list -> t
  val join : t list -> t
  val eq : t -> t -> BoolLattice.t
  val pretty : t -> FormatExt.printer
end = struct
  type t = Bot | Null
  let _Top () = Null
  let _Bot () = Bot
  let join ts =
    let join' t1 t2 = match (t1, t2) with
      | Null, _
      | _, Null -> Null
      | _ -> Bot
    in List.fold_left join' (_Bot ()) ts
  let meet ts =
    let meet' t1 t2 = match (t1, t2) with
      | Bot, _
      | _, Bot -> Bot
      | _ -> Null
    in List.fold_left meet' (_Top ()) ts
  let eq n1 n2 = match (n1, n2) with
    | Bot, Bot
    | Null, Null -> BoolLattice.inject true
    | _ -> BoolLattice.inject false
  let pretty n = match n with
    | Bot -> text "Null:Bot"
    | Null -> text "Null"
end
and StringLattice : sig
  type typeofStrings = TyUndefined | TyNull | TyString | TyNumber | TyBoolean | TyFunction | TyObject | TyLambda
  type t = 
    | Bot 
    | ConcreteUint of string 
    | TypeofString of typeofStrings * ValueLattice.t (* value is of type typeofString *)
    | ConcreteNonUint of string 
    | UintString 
    | NonUintString
    | String
  val _Top : unit -> t
  val _Bot : unit -> t
  val meet : t list -> t
  val join : t list -> t
  val inject : string -> t
  val injectTypeof : typeofStrings * ValueLattice.t -> t
  val stringofTypeof : typeofStrings -> string
  val eq : t -> t -> BoolLattice.t
  val pretty : t -> FormatExt.printer
end = struct
  type typeofStrings = TyUndefined | TyNull | TyString | TyNumber | TyBoolean | TyFunction | TyObject | TyLambda
  type t = 
    | Bot 
    | ConcreteUint of string 
    | TypeofString of typeofStrings * ValueLattice.t (* id is of type typeofString *)
    | ConcreteNonUint of string 
    | UintString 
    | NonUintString
    | String
  let _Top () = String
  let _Bot () = Bot
  let inject s =
    try
      let n = int_of_string s in
      if n >= 0 then ConcreteUint s else ConcreteNonUint s
    with _ -> ConcreteNonUint s
  let injectTypeof (t, v) = TypeofString (t, v)
  let stringofTypeof t = match t with
    | TyUndefined -> "undefined"
    | TyNull -> "null"
    | TyString -> "string"
    | TyNumber -> "number"
    | TyBoolean -> "boolean"
    | TyFunction -> "function"
    | TyObject -> "object"
    | TyLambda -> "lambda"
  let eq s1 s2 = match (s1, s2) with
    | Bot, Bot -> BoolLattice.inject true
    | ConcreteUint s1, ConcreteUint s2
    | ConcreteNonUint s1, ConcreteNonUint s2
    | ConcreteUint s1, ConcreteNonUint s2
    | ConcreteNonUint s1, ConcreteUint s2 -> BoolLattice.inject (s1 = s2)
    | TypeofString (t1, _), TypeofString (t2, _) -> BoolLattice.inject (t1 = t2)
    | ConcreteNonUint s, TypeofString (t, _)
    | TypeofString (t, _), ConcreteNonUint s -> BoolLattice.inject (s = stringofTypeof t)
    | TypeofString _, ConcreteUint _
    | ConcreteUint _, TypeofString _ -> BoolLattice.inject false
    | _ -> BoolLattice._Top ()
  let join ts =
    let join' t1 t2 = match (t1, t2) with
      | Bot, t
      | t, Bot -> t
      | ConcreteUint s1, ConcreteUint s2 -> if s1 = s2 then t1 else UintString
      | ConcreteUint _, UintString
      | UintString, ConcreteUint _ 
      | UintString, UintString -> UintString
      | ConcreteNonUint s, TypeofString (t, id)
      | TypeofString (t, id), ConcreteNonUint s -> 
        if (s = stringofTypeof t) then TypeofString (t, id) else NonUintString
      | TypeofString (ty1, id1), TypeofString (ty2, id2) -> if ty1 = ty2 then t1 else NonUintString
      | TypeofString _, NonUintString
      | NonUintString, TypeofString _ -> NonUintString
      | ConcreteNonUint s1, ConcreteNonUint s2 -> if s1 = s2 then t1 else NonUintString
      | ConcreteNonUint _, NonUintString
      | NonUintString, ConcreteNonUint _ 
      | NonUintString, NonUintString -> NonUintString
      | String, _
      | _, String 
      | NonUintString, ConcreteUint _
      | ConcreteUint _, NonUintString
      | NonUintString, UintString 
      | UintString, NonUintString 
      | UintString, TypeofString _
      | ConcreteUint _, TypeofString _
      | TypeofString _, UintString
      | TypeofString _, ConcreteUint _
      | ConcreteNonUint _, ConcreteUint _
      | ConcreteUint _, ConcreteNonUint _
      | ConcreteNonUint _, UintString 
      | UintString, ConcreteNonUint _ -> String
    in List.fold_left join' (_Bot ()) ts
  let meet ts =
    let meet' t1 t2 = match (t1, t2) with
      | String, t
      | t, String -> t
      | _, Bot
      | Bot, _ -> Bot
      | NonUintString, NonUintString -> NonUintString
      | UintString, UintString -> UintString
      | NonUintString, ConcreteNonUint s
      | ConcreteNonUint s, NonUintString -> ConcreteNonUint s
      | NonUintString, TypeofString (t,id)
      | TypeofString (t, id), NonUintString -> TypeofString (t, id)
      | TypeofString (t, id), ConcreteNonUint s
      | ConcreteNonUint s, TypeofString (t, id) ->
        if (s = stringofTypeof t) then TypeofString(t, id) else Bot
      | TypeofString (ty1, id1), TypeofString (ty2, id2) -> if ty1 = ty2 then t1 else Bot
      | UintString, ConcreteUint s
      | ConcreteUint s, UintString -> ConcreteUint s
      | ConcreteUint s1, ConcreteUint s2 -> if s1 = s2 then t1 else Bot
      | ConcreteNonUint s1, ConcreteNonUint s2 -> if s1 = s2 then t1 else Bot
      | ConcreteUint _, ConcreteNonUint _ 
      | ConcreteNonUint _, ConcreteUint _ 
      | ConcreteNonUint _, UintString
      | UintString, ConcreteNonUint _ 
      | UintString, TypeofString _
      | TypeofString _, UintString
      | ConcreteUint _, NonUintString
      | ConcreteUint _, TypeofString _
      | TypeofString _, ConcreteUint _
      | NonUintString, ConcreteUint _ 
      | NonUintString, UintString
      | UintString, NonUintString -> Bot
    in List.fold_left meet' (_Top ()) ts
  let pretty s = match s with
    | Bot -> text "Str:Bot"
    | ConcreteUint s -> horz[squish[text "UintS{"; text s; text "}"]]
    | ConcreteNonUint s -> horz[squish[text "NonUintS{"; text s; text "}"]]
    | TypeofString (t, _) -> horz[squish[text "Typeof{"; text (stringofTypeof t); text ",_}"]]
    | UintString -> text "UintString"
    | NonUintString -> text "NonUintString"
    | String -> text "Str:Top"
end
and NumLattice : sig
  type t = Bot | PosInf | NegInf | INF | NaN 
           | ConcreteUint of int | Uint | ConcreteNonUint of float | NonUint | Num
  val _Top : unit -> t
  val _Bot : unit -> t
  val meet : t list -> t
  val join : t list -> t
  val inject : float -> t
  val eq : t -> t -> BoolLattice.t
  val pretty : t -> FormatExt.printer
end = struct
  type t = Bot | PosInf | NegInf | INF | NaN 
           | ConcreteUint of int | Uint | ConcreteNonUint of float | NonUint | Num
  let _Bot () = Bot
  let _Top () = Num
  let join ts =
    let join' t1 t2 = match (t1, t2) with
      | Bot, t
      | t, Bot -> t
      | PosInf, PosInf -> PosInf
      | NegInf, NegInf -> NegInf
      | PosInf, NegInf
      | NegInf, PosInf 
      | PosInf, INF
      | INF, PosInf
      | NegInf, INF
      | INF, NegInf
      | INF, INF -> INF
      | NegInf, _
      | _, NegInf
      | PosInf, _
      | _, PosInf
      | INF, _
      | _, INF -> Num
      | NaN, NaN -> NaN
      | NaN, _
      | _, NaN -> Num
      | ConcreteUint n1, ConcreteUint n2 -> if n1 = n2 then t1 else Uint
      | ConcreteUint _, Uint
      | Uint, ConcreteUint _ 
      | Uint, Uint -> Uint
      | ConcreteNonUint n1, ConcreteNonUint n2 -> if n1 = n2 then t1 else NonUint
      | ConcreteNonUint _, NonUint
      | NonUint, ConcreteNonUint _ 
      | NonUint, NonUint -> NonUint
      | NonUint, Uint
      | Uint, NonUint
      | NonUint, ConcreteUint _
      | ConcreteUint _, NonUint
      | Uint, ConcreteNonUint _
      | ConcreteNonUint _, Uint
      | ConcreteUint _, ConcreteNonUint _
      | ConcreteNonUint _, ConcreteUint _
      | Num, _
      | _, Num -> Num
    in List.fold_left join' (_Bot ()) ts
  let meet ts = 
    let meet' t1 t2 = match (t1, t2) with
      | Num, t
      | t, Num -> t
      | Bot, _
      | _, Bot -> Bot
      | INF, INF -> INF
      | Uint, Uint -> Uint
      | NonUint, NonUint -> NonUint
      | NaN, NaN -> NaN
      | INF, PosInf
      | PosInf, INF
      | PosInf, PosInf -> PosInf
      | INF, NegInf
      | NegInf, INF
      | NegInf, NegInf -> NegInf
      | NegInf, _
      | _, NegInf
      | PosInf, _
      | _, PosInf
      | INF, _
      | _, INF -> Bot
      | NaN, _
      | _, NaN -> Bot
      | Uint, ConcreteUint n
      | ConcreteUint n, Uint -> ConcreteUint n
      | ConcreteUint n1, ConcreteUint n2 -> if n1 = n2 then t1 else Bot
      | ConcreteNonUint n, NonUint
      | NonUint, ConcreteNonUint n -> ConcreteNonUint n
      | ConcreteNonUint n1, ConcreteNonUint n2 -> if n1 = n2 then t1 else Bot
      | ConcreteNonUint _, _
      | ConcreteUint _, _
      | Uint, _
      | NonUint, _ -> Bot
    in List.fold_left meet' (_Top ()) ts
  let inject f = 
    match (classify_float f) with
    | FP_nan -> NaN
    | FP_infinite -> if (f > 0.) then PosInf else NegInf
    | FP_zero -> ConcreteUint 0
    | _ ->
      try
        let n = int_of_float f in
        if (abs_float(f -. (float_of_int n)) < epsilon_float) && n >= 0 then ConcreteUint n else ConcreteNonUint f
      with _ -> ConcreteNonUint f
  let eq n1 n2 = match (n1, n2) with
    | NaN, _
    | _, NaN -> BoolLattice.inject false
    | Bot, Bot
    | PosInf, PosInf
    | NegInf, NegInf -> BoolLattice.inject true
    | ConcreteUint i1, ConcreteUint i2 -> BoolLattice.inject (i1 = i2)
    | ConcreteNonUint f1, ConcreteNonUint f2 -> BoolLattice.inject (f1 = f2)
    | ConcreteUint _, ConcreteNonUint _
    | ConcreteNonUint _, ConcreteUint _ -> BoolLattice.inject false
    | ConcreteUint _, PosInf
    | ConcreteUint _, NegInf
    | ConcreteUint _, INF
    | ConcreteUint _, NonUint -> BoolLattice.inject false
    | PosInf, ConcreteUint _
    | NegInf, ConcreteUint _
    | INF, ConcreteUint _
    | NonUint, ConcreteUint _ -> BoolLattice.inject false
    | ConcreteNonUint _, PosInf
    | ConcreteNonUint _, NegInf
    | ConcreteNonUint _, INF
    | ConcreteNonUint _, Uint -> BoolLattice.inject false
    | PosInf, ConcreteNonUint _
    | NegInf, ConcreteNonUint _
    | INF, ConcreteNonUint _
    | Uint, ConcreteNonUint _ -> BoolLattice.inject false
    | _ -> BoolLattice._Top ()
  let pretty n = match n with
    | Bot -> text "Num:Bot"
    | PosInf -> text "+Inf"
    | NegInf -> text "-Inf"
    | INF -> text "?INF"
    | NaN -> text "NaN"
    | ConcreteUint n -> horz [squish [text "Uint("; int n; text ")"]]
    | Uint -> text "Uint"
    | ConcreteNonUint f -> horz [squish [text "NonUint("; float f; text ")"]]
    | NonUint -> text "NonUint"
    | Num -> text "Num:Top"
end
and AddressSetLattice : sig 
  type t = Bot | Set of AddressSet.t | Top
  val _Top : unit -> t
  val _Bot : unit -> t
  val meet : t list -> t
  val join : t list -> t
  val elements : AddressSet.t -> AddressSet.elt list
  val inject : AddressSet.elt -> t
  val pretty : (AddressSet.elt -> FormatExt.printer) -> t -> FormatExt.printer
end = struct
  type t = Bot | Set of AddressSet.t | Top
  let _Bot () = Bot
  let _Top () = Top
  let join ts = 
    let join' t1 t2 = match (t1, t2) with
      | Bot, t
      | t, Bot -> t
      | _, Top
      | Top, _ -> Top
      | Set s1, Set s2 -> Set (AddressSet.union s1 s2)
    in List.fold_left join' (_Bot ()) ts
  let meet ts =
    let meet' t1 t2 = match (t1, t2) with
      | Top, t
      | t, Top -> t
      | Bot, _
      | _, Bot -> Bot
      | Set s1, Set s2 -> Set (AddressSet.inter s1 s2)
    in List.fold_left meet' (_Top ()) ts
  let elements set = AddressSet.elements set
  let pretty eltPrint v = match v with
    | Bot -> text "Set:Bot"
    | Top -> text "Set:Top"
    | Set s -> braces (vert (AddressSet.fold (fun e acc -> (eltPrint e)::acc) s []))
  let inject e = Set (AddressSet.singleton e)
end

and ClosureSetLattice : sig 
  type t = Bot | Set of ClosureSet.t | Top
  val _Top : unit -> t
  val _Bot : unit -> t
  val meet : t list -> t
  val join : t list -> t
  val elements : ClosureSet.t -> ClosureSet.elt list
  val inject : ClosureSet.elt -> t
  val pretty : (ClosureSet.elt -> FormatExt.printer) -> t -> FormatExt.printer
end = struct
  type t = Bot | Set of ClosureSet.t | Top
  let _Bot () = Bot
  let _Top () = Top
  let join ts = 
    let join' t1 t2 = match (t1, t2) with
      | Bot, t
      | t, Bot -> t
      | _, Top
      | Top, _ -> Top
      | Set s1, Set s2 -> Set (ClosureSet.union s1 s2)
    in List.fold_left join' Bot ts
  let meet ts =
    let meet' t1 t2 = match (t1, t2) with
      | Top, t
      | t, Top -> t
      | Bot, _
      | _, Bot -> Bot
      | Set s1, Set s2 -> Set (ClosureSet.inter s1 s2)
    in List.fold_left meet' Top ts
  let elements set = ClosureSet.elements set
  let pretty eltPrint v = match v with
    | Bot -> text "Set:Bot"
    | Top -> text "Set:Top"
    | Set s -> braces (vert (ClosureSet.fold (fun e acc -> (eltPrint e)::acc) s []))
  let inject e = Set (ClosureSet.singleton e)
end

and ObjLattice : sig
  type bindAttrs = 
      { primval : ValueLattice.t option;
        code : ClosureSetLattice.t option;
        proto : ValueLattice.t option;
        klass : StringLattice.t;
        extensible : BoolLattice.t }
  and bindProp = 
    | Data of dataBindValue * BoolLattice.t * BoolLattice.t
    | Accessor of accBindValue * BoolLattice.t * BoolLattice.t 
    | Unknown
    | PropTop
  and dataBindValue = {value : ValueLattice.t; writable : BoolLattice.t}
  and accBindValue = {getter : ValueLattice.t; setter : ValueLattice.t}
  type t = Bot | Obj of bindAttrs * bindProp IdMap.t | Top
  val _Top : unit -> t
  val _Bot : unit -> t
  val meet : t list -> t
  val join : t list -> t
  val setExtensible : t -> BoolLattice.t -> t
  val setKlass : t -> StringLattice.t -> t
  val setProto : t -> ValueLattice.t option -> t
  val setCode : t -> ClosureSetLattice.t option -> t
  val setPrimval : t -> ValueLattice.t option -> t
  val setWritable : t -> id -> BoolLattice.t -> t
  val setValue : t -> id -> ValueLattice.t -> t
  val setGetter : t -> id -> ValueLattice.t -> t
  val setSetter : t -> id -> ValueLattice.t -> t
  val pretty : t -> FormatExt.printer
end = struct
  type bindAttrs = 
      { primval : ValueLattice.t option;
        code : ClosureSetLattice.t option;
        proto : ValueLattice.t option;
        klass : StringLattice.t;
        extensible : BoolLattice.t }
  and bindProp = 
    | Data of dataBindValue * BoolLattice.t * BoolLattice.t
    | Accessor of accBindValue * BoolLattice.t * BoolLattice.t 
    | Unknown
    | PropTop
  and dataBindValue = {value : ValueLattice.t; writable : BoolLattice.t}
  and accBindValue = {getter : ValueLattice.t; setter : ValueLattice.t}
  type t = Bot | Obj of bindAttrs * bindProp IdMap.t | Top
  let _Bot () = Bot
  let _Top () = Top
  let join ts =
    let join' t1 t2 = match (t1, t2) with
      | Bot, t
      | t, Bot -> t
      | Top, _
      | _, Top -> Top
      | Obj ({primval=v1; code=c1; proto=t1; klass=k1; extensible=e1}, p1), 
        Obj ({primval=v2; code=c2; proto=t2; klass=k2; extensible=e2}, p2) ->
        let joinOpt v1 v2 = match (v1, v2) with
          | None, v
          | v, None -> v
          | Some v1, Some v2 -> Some (ValueLattice.join [v1; v2]) in
        let v = joinOpt v1 v2 in
        let c = match c1, c2 with
          | None, c
          | c, None -> c
          | Some c1, Some c2 -> Some (ClosureSetLattice.join [c1;c2]) in
        let t = joinOpt t1 t2 in
        let k = StringLattice.join [k1;k2] in
        let e = BoolLattice.join [e1;e2] in
        let bindProps = {primval=v;code=c;proto=t;klass=k;extensible=e} in
        let merge k v1 v2 = match (v1, v2) with
          | None, _
          | _, None -> Some Unknown
          | Some (Data({value=v1; writable=w1}, e1, c1)), Some (Data({value=v2;writable=w2}, e2, c2)) -> 
            Some (Data ({value = ValueLattice.join [v1;v2];writable=BoolLattice.join [w1;w2]},
                        BoolLattice.join [e1;e2], BoolLattice.join [c1;c2]))
          | Some (Accessor({getter=g1;setter=s1}, e1, c1)), Some(Accessor({getter=g2;setter=s2}, e2, c2)) ->
            Some (Accessor({getter = ValueLattice.join [g1;g2]; setter = ValueLattice.join [s1;s2]},
                        BoolLattice.join [e1;e2], BoolLattice.join [c1;c2]))
          | _ -> Some PropTop in
        let newProps = IdMap.merge merge p1 p2 in
        Obj (bindProps, newProps)
    in List.fold_left join' (_Bot ()) ts
  let meet ts =
    let meet' t1 t2 = match (t1, t2) with
      | Bot, _
      | _, Bot -> Bot
      | Top, t
      | t, Top -> t
      | Obj ({primval=v1; code=c1; proto=t1; klass=k1; extensible=e1}, p1), 
        Obj ({primval=v2; code=c2; proto=t2; klass=k2; extensible=e2}, p2) ->
        let meetOpt v1 v2 = match (v1, v2) with
          | None, v
          | v, None -> Some (ValueLattice._Bot ())
          | Some v1, Some v2 -> Some (ValueLattice.meet [v1; v2]) in
        let v = meetOpt v1 v2 in
        let c = match c1, c2 with
          | None, c
          | c, None -> Some (ClosureSetLattice._Bot ())
          | Some c1, Some c2 -> Some (ClosureSetLattice.meet [c1;c2]) in
        let t = meetOpt t1 t2 in
        let k = StringLattice.meet [k1;k2] in
        let e = BoolLattice.meet [e1;e2] in
        let bindProps = {primval=v;code=c;proto=t;klass=k;extensible=e} in
        let merge k v1 v2 = match (v1, v2) with
          | None, _
          | _, None -> Some Unknown
          | Some (Data({value=v1; writable=w1}, e1, c1)), Some (Data({value=v2;writable=w2}, e2, c2)) -> 
            Some (Data ({value = ValueLattice.meet [v1;v2];writable=BoolLattice.meet [w1;w2]},
                        BoolLattice.meet [e1;e2], BoolLattice.meet [c1;c2]))
          | Some (Accessor({getter=g1;setter=s1}, e1, c1)), Some(Accessor({getter=g2;setter=s2}, e2, c2)) ->
            Some (Accessor({getter = ValueLattice.meet [g1;g2]; setter = ValueLattice.meet [s1;s2]},
                        BoolLattice.meet [e1;e2], BoolLattice.meet [c1;c2]))
          | _ -> Some Unknown in
        let newProps = IdMap.merge merge p1 p2 in
        Obj (bindProps, newProps)
    in List.fold_left meet' (_Top ()) ts
  let setExtensible obj b = match obj with
    | Obj(attrs, props) -> Obj({attrs with extensible = b}, props)
    | _ -> obj
  let setKlass obj klass = match obj with
    | Obj(attrs, props) -> Obj({attrs with klass = klass}, props)
    | _ -> obj
  let setProto obj proto = match obj with
    | Obj(attrs, props) -> Obj({attrs with proto = proto}, props)
    | _ -> obj
  let setCode obj code = match obj with
    | Obj(attrs, props) -> Obj({attrs with code = code}, props)
    | _ -> obj
  let setPrimval obj primval = match obj with
    | Obj(attrs, props) -> Obj({attrs with primval = primval}, props)
    | _ -> obj
  let setWritable obj id b = match obj with
    | Obj(attrs, props) -> 
      (try 
         match (IdMap.find id props) with
         | Data(p, e, c) -> Obj(attrs, IdMap.add id (Data({p with writable = b}, e, c)) props)
         | Unknown -> Obj(attrs, IdMap.add id (Data({writable = b; value = ValueLattice._Top ()}, 
                                                    BoolLattice._Top (), BoolLattice._Top ())) props)
         | _ -> Obj(attrs, IdMap.add id PropTop props)
       with _ -> Obj(attrs, IdMap.add id (Data({writable = b; value = ValueLattice._Top ()}, 
                                               BoolLattice._Top (), BoolLattice._Top ())) props))
    | _ -> obj
  let setValue obj id v = match obj with
    | Obj(attrs, props) -> 
      (try 
         match (IdMap.find id props) with
         | Data(p, e, c) -> Obj(attrs, IdMap.add id (Data({p with value = v}, e, c)) props)
         | Unknown -> Obj(attrs, IdMap.add id (Data({writable = BoolLattice._Top (); value = v}, 
                                                    BoolLattice._Top (), BoolLattice._Top ())) props)
         | _ -> Obj(attrs, IdMap.add id PropTop props)
       with _ -> Obj(attrs, IdMap.add id (Data({writable = BoolLattice._Top (); value = v},
                                               BoolLattice._Top (), BoolLattice._Top ())) props))
    | _ -> obj
  let setGetter obj id g = match obj with
    | Obj(attrs, props) -> 
      (try 
         match (IdMap.find id props) with
         | Accessor(p, e, c) -> Obj(attrs, IdMap.add id (Accessor({p with getter = g}, e, c)) props)
         | Unknown -> Obj(attrs, IdMap.add id (Accessor({getter = g; setter = ValueLattice._Top ()}, 
                                                        BoolLattice._Top (), BoolLattice._Top ())) props)
         | _ -> Obj(attrs, IdMap.add id PropTop props)
       with _ -> Obj(attrs, IdMap.add id (Accessor({getter = g; setter = ValueLattice._Top ()},
                                                   BoolLattice._Top (), BoolLattice._Top ())) props))
    | _ -> obj
  let setSetter obj id s = match obj with
    | Obj(attrs, props) -> 
      (try 
         match (IdMap.find id props) with
         | Accessor(p, e, c) -> Obj(attrs, IdMap.add id (Accessor({p with setter = s}, e, c)) props)
         | Unknown -> Obj(attrs, IdMap.add id (Accessor({setter = s; getter = ValueLattice._Top ()}, 
                                                        BoolLattice._Top (), BoolLattice._Top ())) props)
         | _ -> Obj(attrs, IdMap.add id PropTop props)
       with _ -> Obj(attrs, IdMap.add id (Accessor({setter = s; getter = ValueLattice._Top ()},
                                                   BoolLattice._Top (), BoolLattice._Top ())) props))
    | _ -> obj
  let pretty o = match o with
    | Bot -> text "Obj:Bot"
    | Top -> text "Obj:Top"
    | Obj(attrs, props) -> text "{an object}" (* todo *)
end
and ValueLattice : sig
  type t = UndefLattice.t * NullLattice.t * BoolLattice.t * NumLattice.t * StringLattice.t
      * ObjLattice.t * AddressSetLattice.t * ClosureSetLattice.t
  type monoValue = 
    | Undef of UndefLattice.t
    | Null of NullLattice.t
    | Bool of BoolLattice.t
    | Num of NumLattice.t
    | Str of StringLattice.t
    | Obj of ObjLattice.t
    | Addrs of AddressSetLattice.t
    | Closure of ClosureSetLattice.t
    | NotMono of t
  val _Top : unit -> t
  val _Bot : unit -> t
  val meet : t list -> t
  val join : t list -> t
  val injectUndef : UndefLattice.t -> t
  val injectNull : NullLattice.t -> t
  val injectBool : BoolLattice.t -> t
  val injectNum : NumLattice.t -> t
  val injectStr : StringLattice.t -> t
  val injectObj : ObjLattice.t -> t
  val injectAddrs : AddressSetLattice.t -> t
  val injectClosure : ClosureSetLattice.t -> t
  val undefOf : t -> UndefLattice.t
  val nullOf : t -> NullLattice.t
  val boolOf : t -> BoolLattice.t
  val numOf : t -> NumLattice.t
  val strOf : t -> StringLattice.t
  val objOf : t -> ObjLattice.t
  val addrsOf : t -> AddressSetLattice.t
  val closureOf : t -> ClosureSetLattice.t
  val asMono : t -> monoValue
  val pretty : t -> FormatExt.printer
  val leq : t -> t -> bool
end = struct
  type t = UndefLattice.t * NullLattice.t * BoolLattice.t * NumLattice.t * StringLattice.t
      * ObjLattice.t * AddressSetLattice.t * ClosureSetLattice.t
  type monoValue = 
    | Undef of UndefLattice.t
    | Null of NullLattice.t
    | Bool of BoolLattice.t
    | Num of NumLattice.t
    | Str of StringLattice.t
    | Obj of ObjLattice.t
    | Addrs of AddressSetLattice.t
    | Closure of ClosureSetLattice.t
    | NotMono of t
  let _Bot () = (UndefLattice._Bot (), NullLattice._Bot (), BoolLattice._Bot (), NumLattice._Bot (), 
                 StringLattice._Bot (), ObjLattice._Bot (), AddressSetLattice._Bot (), ClosureSetLattice._Bot ())
  let _Top () = (UndefLattice._Top (), NullLattice._Top (), BoolLattice._Top (), NumLattice._Top (),
                 StringLattice._Top (), ObjLattice._Top (), AddressSetLattice._Top (), ClosureSetLattice._Top ())
  let join ts =
    let join' (u1,n1,b1,i1,s1,o1,a1,f1) (u2,n2,b2,i2,s2,o2,a2,f2) =
      (UndefLattice.join [u1; u2],
       NullLattice.join [n1; n2],
       BoolLattice.join [b1; b2],
       NumLattice.join [i1; i2],
       StringLattice.join [s1; s2],
       ObjLattice.join [o1; o2],
       AddressSetLattice.join [a1; a2],
       ClosureSetLattice.join [f1; f2]) in
    List.fold_left join' (_Bot ()) ts
  let meet ts =
    let meet' (u1,n1,b1,i1,s1,o1,a1,f1) (u2,n2,b2,i2,s2,o2,a2,f2) =
      (UndefLattice.meet [u1; u2],
       NullLattice.meet [n1; n2],
       BoolLattice.meet [b1; b2],
       NumLattice.meet [i1; i2],
       StringLattice.meet [s1; s2],
       ObjLattice.meet [o1; o2],
       AddressSetLattice.meet [a1; a2],
       ClosureSetLattice.meet [f1; f2]) in
    List.fold_left meet' (_Top ()) ts
  let injectUndef u = (u, NullLattice._Bot (), (BoolLattice._Bot ()), NumLattice._Bot (), StringLattice._Bot (),
                       ObjLattice._Bot (), AddressSetLattice._Bot (), ClosureSetLattice._Bot ())
  let injectNull n = (UndefLattice._Bot (), n, (BoolLattice._Bot ()), NumLattice._Bot (), StringLattice._Bot (),
                       ObjLattice._Bot (), AddressSetLattice._Bot (), ClosureSetLattice._Bot ())
  let injectBool b = (UndefLattice._Bot (), NullLattice._Bot (), b, NumLattice._Bot (), StringLattice._Bot (),
                       ObjLattice._Bot (), AddressSetLattice._Bot (), ClosureSetLattice._Bot ())
  let injectNum n = (UndefLattice._Bot (), NullLattice._Bot (), (BoolLattice._Bot ()), n, StringLattice._Bot (),
                       ObjLattice._Bot (), AddressSetLattice._Bot (), ClosureSetLattice._Bot ())
  let injectStr s = (UndefLattice._Bot (), NullLattice._Bot (), (BoolLattice._Bot ()), NumLattice._Bot (), s,
                       ObjLattice._Bot (), AddressSetLattice._Bot (), ClosureSetLattice._Bot ())
  let injectObj o = (UndefLattice._Bot (), NullLattice._Bot (), (BoolLattice._Bot ()), NumLattice._Bot (), StringLattice._Bot (),
                       o, AddressSetLattice._Bot (), ClosureSetLattice._Bot ())
  let injectAddrs a = (UndefLattice._Bot (), NullLattice._Bot (), (BoolLattice._Bot ()), NumLattice._Bot (), StringLattice._Bot (),
                       ObjLattice._Bot (), a, ClosureSetLattice._Bot ())
  let injectClosure c = (UndefLattice._Bot (), NullLattice._Bot (), (BoolLattice._Bot ()), NumLattice._Bot (), 
                         StringLattice._Bot (), ObjLattice._Bot (), AddressSetLattice._Bot (), c)
  let undefOf (u, n, b, i, s, o, a, c) = u
  let nullOf (u, n, b, i, s, o, a, c) = n
  let boolOf (u, n, b, i, s, o, a, c) = b
  let numOf (u, n, b, i, s, o, a, c) = i
  let strOf (u, n, b, i, s, o, a, c) = s
  let objOf (u, n, b, i, s, o, a, c) = o
  let addrsOf (u, n, b, i, s, o, a, c) = a
  let closureOf (u, n, b, i, s, o, a, c) = c
  let asMono ((u, n, b, i, s, o, a, c) as v) =
    if (meet [(injectUndef u); v] = injectUndef u) then Undef u
    else if (meet [(injectNull n); v] = injectNull n) then Null n
    else if (meet [(injectBool b); v] = injectBool b) then Bool b
    else if (meet [(injectNum i); v] = injectNum i) then Num i
    else if (meet [(injectStr s); v] = injectStr s) then Str s
    else if (meet [(injectObj o); v] = injectObj o) then Obj o
    else if (meet [(injectAddrs a); v] = injectAddrs a) then Addrs a
    else if (meet [(injectClosure c); v] = injectClosure c) then Closure c
    else NotMono v
  let pretty (u, n, b, i, s, o, a, c) =
    vert [UndefLattice.pretty u;
          NullLattice.pretty n;
          BoolLattice.pretty b;
          NumLattice.pretty i;
          StringLattice.pretty s;
          ObjLattice.pretty o;
          AddressSetLattice.pretty V.ADDRESS.pretty a;
          ClosureSetLattice.pretty CLOSURE.pretty c]
  let leq v1 v2 = join [v1;v2] = v2
end
type absStore = ValueLattice.t V.Store.t


let str s = ValueLattice.injectStr (StringLattice.inject s)
let num f = ValueLattice.injectNum (NumLattice.inject f)

exception CpsThrow of string

let bool b = match b with
  | true -> ValueLattice.injectBool BoolLattice.True 
  | false -> ValueLattice.injectBool BoolLattice.False
let unbool b = match b with
  | BoolLattice.True
  | BoolLattice.TrueTypeof _ -> true
  | BoolLattice.False
  | BoolLattice.FalseTypeof _ -> false
  | _ -> failwith ("tried to unbool a non-bool")

let typeof v _ = 
  let module VL = ValueLattice in
  let module SL = StringLattice in
  let module OL = ObjLattice in
  let vi = VL.injectStr in
  match (VL.asMono v) with
  | VL.Undef _ -> vi (SL.injectTypeof(SL.TyUndefined, v))
  | VL.Null _ -> vi (SL.injectTypeof(SL.TyNull, v))
  | VL.Str _ -> vi (SL.injectTypeof(SL.TyString, v))
  | VL.Num _ -> vi (SL.injectTypeof(SL.TyNumber, v))
  | VL.Bool _ -> vi (SL.injectTypeof(SL.TyBoolean, v))
  | VL.Obj o ->
    (match o with
    | OL.Obj({OL.code = Some _}, _) -> vi (SL.injectTypeof(SL.TyFunction, v))
    |_ -> vi (SL.injectTypeof(SL.TyObject, v)))
  | VL.Closure _ -> vi (SL.injectTypeof(SL.TyLambda, v))
  | VL.Addrs _ -> vi (SL._Bot ())
  | VL.NotMono _ -> vi (SL._Top ())

let surface_typeof v store = 
  let module VL = ValueLattice in
  let module SL = StringLattice in
  let vi = VL.injectStr in
  match (VL.asMono v) with
  | VL.Closure _ -> vi (SL._Bot ())
  | VL.Null _ ->  vi (SL.injectTypeof(SL.TyObject, v))
  | _ -> typeof v store
  
let is_primitive v _ = 
  let module VL = ValueLattice in
  let module SL = StringLattice in
  let module OL = ObjLattice in
  match (VL.asMono v) with
  | VL.Undef _
  | VL.Null _
  | VL.Str _
  | VL.Num _
  | VL.Bool _
  | _ -> bool false

let float_str n = 
  let module NL = NumLattice in
  let module SL = StringLattice in 
  match n with
  | NL.Bot -> SL._Bot ()
  | NL.PosInf -> SL.ConcreteNonUint "Infinity"
  | NL.NegInf -> SL.ConcreteNonUint "-Infinity"
  | NL.NaN -> SL.ConcreteNonUint "NaN"
  | NL.ConcreteUint i -> SL.ConcreteNonUint (string_of_int i)
  | NL.ConcreteNonUint f -> SL.ConcreteNonUint (string_of_float f)
  | _ -> SL._Top ()

let prim_to_str v store = 
  let module VL = ValueLattice in
  let module SL = StringLattice in
  let module BL = BoolLattice in
  let module OL = ObjLattice in
  match (VL.asMono v) with
  | VL.Undef _ -> str "undefined"
  | VL.Null _ -> str "null"
  | VL.Str _ -> v
  | VL.Bool b -> 
    (match b with
    | BL.True 
    | BL.TrueTypeof _ -> str "true"
    | BL.False
    | BL.FalseTypeof _ -> str "false"
    | BL.Bot -> VL.injectStr (SL._Bot ())
    | _ -> VL.injectStr (SL._Top ()))
  | VL.Num i -> 
    (match (float_str i) with
    | SL.Bot -> VL.injectStr (SL._Bot ())
    | SL.ConcreteNonUint fs ->
      let fslen = String.length fs in
      let s' =
        if String.get fs (fslen - 1) = '.' then String.sub fs 0 (fslen - 1) else
        (* This is because we don't want leading zeroes in the "-e" part.
         * For example, OCaml says 1.2345e-07, but ES5 wants 1.2345e-7 *)
          if String.contains fs '-'
          then let indx = String.index fs '-' in 
               let prefix = String.sub fs 0 (indx + 1) in
               let suffix = String.sub fs (indx + 1) (fslen - (String.length prefix)) in
               let slen = String.length suffix in
               let fixed = if slen > 1 && (String.get suffix 0 = '0') 
                 then String.sub suffix 1 (slen - 1)
                 else suffix in
               prefix ^ fixed 
          else fs in
      str s'
    | _ -> VL.injectStr (SL._Top ()))
  | _ -> VL.injectStr (SL._Bot ())


let strlen v _ =
  let module VL = ValueLattice in
  let module SL = StringLattice in
  match (VL.asMono v) with
  | VL.Str s -> 
    (match s with
    | SL.Bot -> VL.injectNum (NumLattice._Bot ())
    | SL.ConcreteNonUint s -> num (float_of_int (String.length s))
    | SL.ConcreteUint s -> num (float_of_int (String.length s))
    | _ -> VL.injectNum (NumLattice._Top ())
    )
  | _ -> VL.injectNum (NumLattice._Bot ())

(* Section 9.3, excluding objects *)
let prim_to_num v _ =
  let module VL = ValueLattice in
  let module SL = StringLattice in
  let module NL = NumLattice in
  let module BL = BoolLattice in
  let num n = VL.injectNum (NL.inject n) in
  match (VL.asMono v) with
  | VL.Undef _ -> num nan
  | VL.Null _ -> num 0.0
  | VL.Num _ -> v
  | VL.Bool b -> 
    (match b with
    | BL.True 
    | BL.TrueTypeof _ -> num 1.0
    | BL.False
    | BL.FalseTypeof _ -> num 0.0
    | BL.Bot -> VL.injectNum (NL._Bot ())
    | _ -> VL.injectNum (NL._Top ()))
  | VL.Str s -> 
    (match s with
    | SL.Bot -> VL.injectNum (NL._Bot ())
    | SL.ConcreteNonUint "" -> num 0.0
    | SL.ConcreteNonUint s -> begin try num (float_of_string s) with _ -> num nan end
    | SL.ConcreteUint s -> num (float_of_string s)
    | _ -> VL.injectNum (NL._Top ())
    )
  | _ -> VL.injectNum (NL._Bot ())
  
let prim_to_bool v _ = 
  let module VL = ValueLattice in
  let module SL = StringLattice in
  let module NL = NumLattice in
  let module BL = BoolLattice in
  match (VL.asMono v) with
  | VL.Undef _ -> bool false
  | VL.Null _ -> bool false
  | VL.Num i -> 
    (match i with
    | NL.NaN -> bool false
    | NL.ConcreteNonUint n -> bool (not (n = 0.0 || n = -0.0))
    | NL.ConcreteUint i -> bool (i != 0)
    | _ -> bool true
    )
  | VL.Bool _ -> v
  | VL.Str s -> 
    (match s with
    | SL.Bot -> VL.injectBool (BL._Bot ())
    | SL.ConcreteNonUint "" -> bool false
    | SL.ConcreteNonUint s -> bool true
    | SL.ConcreteUint "" -> bool false
    | SL.ConcreteUint s -> bool true
    | _ -> VL.injectBool (BL._Top ())
    )
  | _ -> bool true

let is_callable obj store = 
  let module VL = ValueLattice in
  let module ASL = AddressSetLattice in
  let module OL = ObjLattice in
  match (ValueLattice.addrsOf obj) with
  | ASL.Set addrs ->
    let value = VL.join (List.map (fun addr -> V.Store.find addr store)
                                     (ASL.elements addrs)) in
    (match (VL.objOf value) with
    | OL.Bot -> VL.injectBool (BoolLattice._Bot ())
    | OL.Obj ({OL.code = Some _}, _) -> bool true
    | OL.Obj _ -> bool false
    | OL.Top -> VL.injectBool (BoolLattice._Top ()))
  | _ -> bool false

let print v _ = 
  ValueLattice.injectUndef (UndefLattice._Top ()) (* abstractly, we don't have to print *)

let is_extensible obj store = 
  let module VL = ValueLattice in
  let module ASL = AddressSetLattice in
  let module OL = ObjLattice in
  match (ValueLattice.addrsOf obj) with
  | ASL.Set addrs ->
    let value = VL.meet (List.map (fun addr -> V.Store.find addr store)
                                     (ASL.elements addrs)) in
    (match (VL.objOf value) with
    | OL.Bot -> VL.injectBool (BoolLattice._Bot ())
    | OL.Obj ({OL.extensible = b}, _) -> VL.injectBool b
    | OL.Top -> VL.injectBool (BoolLattice._Top ()))
  | _ -> bool false

let prevent_extensions obj store = match (ValueLattice.addrsOf obj) with
  | AddressSetLattice.Set addrs ->
    let value = ValueLattice.join (List.map (fun addr -> V.Store.find addr store)
                                     (AddressSetLattice.elements addrs)) in
    let o = ValueLattice.objOf value in
    let o' = ObjLattice.setExtensible o BoolLattice.False in
    ValueLattice.injectObj o'
  | a -> ValueLattice.injectAddrs a
      
let get_code obj store = 
  let module VL = ValueLattice in
  let module OL = ObjLattice in
  match (VL.addrsOf obj) with
  | AddressSetLattice.Set addrs ->
    let value = VL.join (List.map (fun addr -> V.Store.find addr store)
                                     (AddressSetLattice.elements addrs)) in
    let o = VL.objOf value in
    (match o with
    | OL.Obj ({OL.code = Some v}, _) -> VL.injectClosure v
    | OL.Obj ({OL.code = None}, _) -> VL.injectNull (NullLattice._Top ())
    | OL.Bot -> VL._Bot ()
    | OL.Top -> VL.join [VL.injectNull (NullLattice._Top ()); VL.injectObj (ObjLattice._Top ())])
  | a -> ValueLattice.injectAddrs a

let get_proto obj store =
  let module VL = ValueLattice in
  let module OL = ObjLattice in
  match (VL.addrsOf obj) with
  | AddressSetLattice.Set addrs ->
    let value = VL.join (List.map (fun addr -> V.Store.find addr store)
                                     (AddressSetLattice.elements addrs)) in
    let o = VL.objOf value in
    (match o with
    | OL.Obj ({OL.proto = Some v}, _) -> v
    | OL.Obj ({OL.proto = None}, _) -> VL.injectNull (NullLattice._Top ())
    | OL.Bot -> VL._Bot ()
    | OL.Top -> VL._Top ())
  | a -> ValueLattice.injectAddrs a

let get_primval obj store =
  let module VL = ValueLattice in
  let module OL = ObjLattice in
  match (VL.addrsOf obj) with
  | AddressSetLattice.Set addrs ->
    let value = VL.join (List.map (fun addr -> V.Store.find addr store)
                                     (AddressSetLattice.elements addrs)) in
    let o = VL.objOf value in
    (match o with
    | OL.Obj ({OL.primval = Some v}, _) -> v
    | OL.Obj ({OL.primval = None}, _) -> VL._Bot ()
    | OL.Bot -> VL._Bot ()
    | OL.Top -> VL._Top ())
  | a -> ValueLattice.injectAddrs a

let get_class obj store =
  let module VL = ValueLattice in
  let module OL = ObjLattice in
  match (VL.addrsOf obj) with
  | AddressSetLattice.Set addrs ->
    let value = VL.join (List.map (fun addr -> V.Store.find addr store)
                                     (AddressSetLattice.elements addrs)) in
    let o = VL.objOf value in
    (match o with
    | OL.Obj ({OL.klass = s}, _) -> VL.injectStr s
    | OL.Bot -> VL.injectStr (StringLattice._Bot ())
    | OL.Top -> VL.injectStr (StringLattice._Top ()))
  | a -> ValueLattice.injectAddrs a

(* All the enumerable property names of an object *)
exception Pointy of ValueLattice.t
let rec get_property_names obj store =
  let module VL = ValueLattice in
  let module BL = BoolLattice in
  let module OL = ObjLattice in
  try
    match (VL.addrsOf obj) with
    | AddressSetLattice.Set addrs ->
      let value = VL.join (List.map (fun addr -> V.Store.find addr store)
                             (AddressSetLattice.elements addrs)) in
      let o = VL.objOf value in
      (match o with
      | OL.Obj (_, _) -> 
        let protos = o::(all_protos obj store) in
        let folder o set = begin match o with
	  | OL.Obj(attrs, props) -> 
	    IdMap.fold (fun k v s ->
              match enum v with
              | BoolLattice.Bot -> raise (Pointy (VL._Bot ()))
              | BoolLattice.Bool -> raise (Pointy (VL.injectObj (OL._Top ())))
              | b -> if unbool b then IdSet.add k s else s) props set
          | OL.Top -> raise (Pointy (VL._Top ()))
	  | OL.Bot -> set (* non-object prototypes don't contribute *) 
        end in
        let name_set = List.fold_right folder protos IdSet.empty in
        let name_list= IdSet.elements name_set in
        let prop_folder num name props = 
          IdMap.add (string_of_int num)
            (OL.Data ({ OL.value = str name; OL.writable = BL.inject false }, 
                      BL.inject false, BL.inject false)) props in
        let name_props = List.fold_right2 prop_folder 
          (iota (List.length name_list))
          name_list
          IdMap.empty in
        let d_attrsv = { OL.primval = None; OL.code = None; OL.proto = None; 
                         OL.extensible = BL.inject false; OL.klass = StringLattice.inject "LambdaJS interal" }
        in VL.injectObj (OL.Obj(d_attrsv, name_props))
      | OL.Bot -> VL._Bot ()
      | OL.Top -> VL.injectObj (OL._Top ()))
    | a -> ValueLattice.injectAddrs a
  with Pointy v -> v (* if anything went wrong, abort with a pointy *)


and all_protos o store : ObjLattice.t list = 
  let module VL = ValueLattice in
  let module ASL = AddressSetLattice in
  let module OL = ObjLattice in
  let fromObj = match (VL.objOf o) with
    | OL.Obj ({ OL.proto = Some p }, _) -> Some p
    | _ -> None in
  let fromAddrs = match (VL.addrsOf o) with
    | ASL.Set addrs ->
      let value = VL.join (List.map (fun addr -> V.Store.find addr store)
                             (ASL.elements addrs)) in
      (match (VL.objOf value) with
      | OL.Obj ({ OL.proto = Some p }, _) -> Some p
      | _ -> None)
    | _ -> None in
  let joined = match (fromObj, fromAddrs) with
    | None, Some o -> Some o
    | Some o, None -> Some o
    | Some o, Some a -> Some (VL.join [o; a])
    | _ -> None in
  match joined with
  | None -> []
  | Some v -> match (VL.objOf v) with
    | (OL.Obj ({OL.proto = Some p}, _) as o) -> o :: all_protos p store
    | (OL.Obj _) -> []
    | (OL.Bot) -> [OL._Bot ()]
    | (OL.Top) -> [OL._Top ()]

and enum prop = match prop with
  | ObjLattice.Accessor (_, b, _)
  | ObjLattice.Data (_, b, _) -> b
  | ObjLattice.PropTop -> BoolLattice.Bool
  | ObjLattice.Unknown -> BoolLattice.Bot

let get_own_property_names obj store =
  let module VL = ValueLattice in
  let module BL = BoolLattice in
  let module OL = ObjLattice in
  match (VL.addrsOf obj) with
  | AddressSetLattice.Set addrs ->
    let value = VL.join (List.map (fun addr -> V.Store.find addr store)
                           (AddressSetLattice.elements addrs)) in
    let o = VL.objOf value in
    (match o with
    | OL.Obj (_, props) -> 
      let add_name n x m = 
        IdMap.add (string_of_int x)
          (OL.Data ({ OL.value = str n; OL.writable = BL.inject false }, 
                    BL.inject false, BL.inject false)) m in
      let namelist = IdMap.fold (fun k _ l -> (k :: l)) props [] in
      
      let props = 
	List.fold_right2 add_name namelist (iota (List.length namelist)) IdMap.empty in
      let d = (float_of_int (List.length namelist)) in
      let final_props = 
        IdMap.add "length"
          (OL.Data ({ OL.value = num d; OL.writable = BL.inject false },
                    BL.inject false, BL.inject false)) props in 
      let d_attrsv = { OL.primval = None; OL.code = None; OL.proto = None; 
                       OL.extensible = BL.inject false; OL.klass = StringLattice.inject "LambdaJS interal" }
      in VL.injectObj (OL.Obj(d_attrsv, final_props))
    | OL.Bot -> VL._Bot ()
    | OL.Top -> VL.injectObj (OL._Top ()))
  | a -> ValueLattice.injectAddrs a


(* Implement this here because there's no need to expose the class
   property outside of the delta function *)
let object_to_string obj store = 
  let module VL = ValueLattice in
  let module OL = ObjLattice in
  let module SL = StringLattice in
  match (VL.addrsOf obj) with
  | AddressSetLattice.Set addrs ->
    let value = VL.join (List.map (fun addr -> V.Store.find addr store)
                                     (AddressSetLattice.elements addrs)) in
    let o = VL.objOf value in
    (match o with
    | OL.Obj ({OL.klass = s}, _) -> (match s with
      | SL.Bot -> VL._Bot ()
      | SL.String
      | SL.NonUintString
      | SL.UintString -> VL.injectStr (SL._Top ())
      | SL.ConcreteUint s
      | SL.ConcreteNonUint s -> str ("[object " ^ s ^ "]")
      | SL.TypeofString (t, _) -> str ("[object " ^ (SL.stringofTypeof t) ^ "]"))
    | OL.Bot -> VL._Bot ()
    | OL.Top -> VL.injectStr (SL._Top ()))
  | a -> ValueLattice.injectAddrs a

let is_array obj store =
  let module VL = ValueLattice in
  let module OL = ObjLattice in
  let module SL = StringLattice in
  match (VL.addrsOf obj) with
  | AddressSetLattice.Set addrs ->
    let value = VL.join (List.map (fun addr -> V.Store.find addr store)
                                     (AddressSetLattice.elements addrs)) in
    let o = VL.objOf value in
    (match o with
    | OL.Obj ({OL.klass = s}, _) -> 
      (match s with
      | SL.ConcreteNonUint "Array" -> bool true
      | SL.Bot -> VL._Bot ()
      | SL.String -> VL.injectBool (BoolLattice._Top ())
      | _ -> bool false)
    | OL.Bot -> VL._Bot ()
    | OL.Top -> VL.injectBool (BoolLattice._Top ()))
  | a -> ValueLattice.injectAddrs a


let to_num_fn fn v =
  let module VL = ValueLattice in
  let module NL = NumLattice in
  match (VL.numOf v) with
  | NL.Bot -> VL._Bot ()
  | NL.PosInf
  | NL.NegInf
  | NL.INF
  | NL.NaN -> num 0.
  | NL.ConcreteUint i -> num (fn (float_of_int i))
  | NL.ConcreteNonUint f -> num (fn f)
  | NL.Num
  | NL.NonUint
  | NL.Uint -> VL.injectNum (NL._Top ())

let to_int32 v _ = to_num_fn (fun n -> float_of_int (int_of_float n)) v

let nnot e _ = 
  let module VL = ValueLattice in
  match (VL.asMono e) with
  | VL.Undef _ -> bool true
  | VL.Null _ -> bool true
  | VL.Bool b -> (match b with
    | BoolLattice.Bot -> VL._Bot ()
    | BoolLattice.Bool -> VL.injectBool (BoolLattice._Top ())
    | _ -> if unbool b then bool false else bool true)
  | VL.Num d -> (match d with
    | NumLattice.Bot -> VL._Bot ()
    | NumLattice.Num -> VL.injectBool (BoolLattice._Top ())
    | NumLattice.PosInf
    | NumLattice.NegInf
    | NumLattice.INF -> bool false 
    | NumLattice.NaN -> bool true
    | NumLattice.Uint
    | NumLattice.NonUint -> VL.injectBool (BoolLattice._Top ())
    | NumLattice.ConcreteUint n -> bool (n = 0)
    | NumLattice.ConcreteNonUint f -> bool (f = 0.))
  | VL.Str s -> (match s with
    | StringLattice.ConcreteUint s
    | StringLattice.ConcreteNonUint s -> bool (s = "")
    | StringLattice.Bot -> VL._Bot ()
    | StringLattice.String -> VL._Top ()
    | StringLattice.TypeofString _ -> bool false
    | _ -> VL.injectBool (BoolLattice._Top ()))
  | VL.Obj _ -> bool false
  | VL.Closure _ -> bool false
  | VL.Addrs _ -> VL._Bot ()
  | VL.NotMono _ -> VL.injectBool (BoolLattice._Top ())

let void v _ = ValueLattice.injectUndef (UndefLattice._Top ())

let floor' n _ = to_num_fn floor n

let ceil' n _ = to_num_fn ceil n

let absolute n _ = to_num_fn abs_float n

let log' n _ = to_num_fn log n

let ascii_ntoc v _ = 
  let module VL = ValueLattice in
  let module NL = NumLattice in
  match (VL.numOf v) with
  | NL.Bot -> VL._Bot ()
  | NL.PosInf
  | NL.NegInf
  | NL.INF
  | NL.NaN -> str (String.make 1 (Char.chr 0))
  | NL.ConcreteUint i -> str (String.make 1 (Char.chr i))
  | NL.ConcreteNonUint f -> str (String.make 1 (Char.chr (int_of_float f)))
  | NL.Num
  | NL.NonUint
  | NL.Uint -> VL.injectStr (StringLattice._Top ())

let str_to_fn fn top v =
  let module VL = ValueLattice in
  let module SL = StringLattice in
  match (VL.strOf v) with
  | SL.Bot -> VL._Bot ()
  | SL.ConcreteUint s
  | SL.ConcreteNonUint s -> (fn s)
  | SL.TypeofString (t, _) -> (fn (SL.stringofTypeof t))
  | _ -> top

let str_to_str_fn fn v = str_to_fn (fun v -> str (fn v)) (ValueLattice.injectStr (StringLattice._Top ())) v

let str_to_num_fn fn v = str_to_fn (fun v -> num (fn v)) (ValueLattice.injectNum (NumLattice._Top ())) v

let ascii_cton c _ = str_to_num_fn (fun s -> (float_of_int (Char.code (String.get s 0)))) c

let to_lower s _ = str_to_str_fn (fun s -> (String.lowercase s)) s

let to_upper s _ = str_to_str_fn (fun s -> (String.uppercase s)) s

let bnot b _ = to_num_fn (fun d -> float_of_int (lnot (int_of_float d))) b

let sine n _ = to_num_fn sin n

let numstr s _ = str_to_num_fn (fun s -> (try float_of_string s with Failure _ -> nan)) s

let op1 op : ValueLattice.t -> ValueLattice.t V.Store.t -> ValueLattice.t = match op with
  | "typeof" -> typeof
  | "surface-typeof" -> surface_typeof
  | "primitive?" -> is_primitive
  | "prim->str" -> prim_to_str
  | "prim->num" -> prim_to_num
  | "prim->bool" -> prim_to_bool
  | "is-callable" -> is_callable
  | "is-extensible" -> is_extensible
  | "prevent-extensions" -> prevent_extensions
  | "print" -> print
  | "get-proto" -> get_proto
  | "get-primval" -> get_primval
  | "get-class" -> get_class
  | "get-code" -> get_code
  | "property-names" -> get_property_names
  | "own-property-names" -> get_own_property_names
  | "object-to-string" -> object_to_string
  | "strlen" -> strlen
  | "is-array" -> is_array
  | "to-int32" -> to_int32
  | "!" -> nnot
  | "void" -> void
  | "floor" -> floor'
  | "ceil" -> ceil'
  | "abs" -> absolute
  | "log" -> log'
  | "ascii_ntoc" -> ascii_ntoc
  | "ascii_cton" -> ascii_cton
  | "to-lower" -> to_lower
  | "to-upper" -> to_upper
  | "~" -> bnot
  | "sin" -> sine
  | "numstr->num" -> numstr
  | _ -> failwith ("no implementation of unary operator: " ^ op)

let num_num_to_fn f_op inf top v1 v2 =
  let module VL = ValueLattice in
  let module NL = NumLattice in
  match (VL.numOf v1, VL.numOf v2) with
  | NL.Bot, _
  | _, NL.Bot -> VL._Bot ()
  | (NL.PosInf, NL.PosInf) -> (f_op infinity infinity)
  | (NL.PosInf, NL.NegInf) -> (f_op infinity neg_infinity)
  | (NL.NegInf, NL.PosInf) -> (f_op neg_infinity infinity)
  | (NL.NegInf, NL.NegInf) -> (f_op neg_infinity neg_infinity)
  | NL.INF, _
  | _, NL.INF -> inf
  | NL.NaN, _
  | _, NL.NaN -> inf
  | NL.ConcreteUint i1, NL.ConcreteUint i2 -> (f_op (float_of_int i1) (float_of_int i2))
  | NL.ConcreteNonUint f1, NL.ConcreteUint i2 -> (f_op f1 (float_of_int i2))
  | NL.ConcreteUint i1, NL.ConcreteNonUint f2 -> (f_op (float_of_int i1) f2)
  | NL.ConcreteNonUint f1, NL.ConcreteNonUint f2 -> (f_op f1 f2)
  | NL.ConcreteUint i, NL.PosInf -> (f_op (float_of_int i) infinity)
  | NL.ConcreteUint i, NL.NegInf -> (f_op (float_of_int i) neg_infinity)
  | NL.ConcreteNonUint f, NL.PosInf -> (f_op f infinity)
  | NL.ConcreteNonUint f, NL.NegInf -> (f_op f neg_infinity)
  | NL.PosInf, NL.ConcreteUint i -> (f_op infinity (float_of_int i))
  | NL.NegInf, NL.ConcreteUint i -> (f_op neg_infinity (float_of_int i))
  | NL.PosInf, NL.ConcreteNonUint f-> (f_op infinity f)
  | NL.NegInf, NL.ConcreteNonUint f-> (f_op neg_infinity f)
  | NL.Num, _
  | _, NL.Num
  | NL.NonUint, _
  | _, NL.NonUint
  | NL.Uint, _
  | _, NL.Uint -> top

let arith s f_op v1 v2 _ = num_num_to_fn (fun v1 v2 -> num (f_op v1 v2)) (num nan) (ValueLattice.injectNum (NumLattice._Top ())) v1 v2

let compare s f_op v1 v2 _ = num_num_to_fn (fun v1 v2 -> bool (f_op v1 v2)) (ValueLattice.injectBool (BoolLattice._Top ())) (ValueLattice.injectBool (BoolLattice._Top ())) v1 v2


let arith_sum = arith "+" (+.)

let arith_sub = arith "-" (-.)

(* OCaml syntax failure! Operator section syntax lexes as a comment. *)
let arith_mul = arith "*" (fun x y -> x *. y)

let arith_div x y env = try arith "/" (/.) x y env
with Division_by_zero -> num infinity

let arith_mod x y env = try arith "mod" mod_float x y env
with Division_by_zero -> num nan

let arith_lt = compare "<" (<)

let arith_le = compare "<=" (<=)

let arith_gt = compare ">" (>)

let arith_ge = compare ">=" (>=)

let bitwise_and = arith "&" (fun v1 v2 -> (float_of_int ((truncate v1) land (truncate v2))))

let bitwise_or = arith "|" (fun v1 v2 -> (float_of_int ((truncate v1) lor (truncate v2))))

let bitwise_xor = arith "^" (fun v1 v2 -> (float_of_int ((truncate v1) lxor (truncate v2))))

let bitwise_shiftl = arith "<<" (fun v1 v2 -> (float_of_int ((truncate v1) lsl (truncate v2))))

let bitwise_zfshiftr = arith ">>" (fun v1 v2 -> (float_of_int ((truncate v1) lsr (truncate v2))))

let bitwise_shiftr = arith ">>>" (fun v1 v2 -> (float_of_int ((truncate v1) asr (truncate v2))))


let str_str_to_fn fn top v1 v2 = 
  let module VL = ValueLattice in
  let module SL = StringLattice in
  match (VL.strOf v1, VL.strOf v2) with
  | SL.Bot, _
  | _, SL.Bot -> VL._Bot ()
  | SL.ConcreteUint s1, SL.ConcreteUint s2
  | SL.ConcreteUint s1, SL.ConcreteNonUint s2
  | SL.ConcreteNonUint s1, SL.ConcreteUint s2
  | SL.ConcreteNonUint s1, SL.ConcreteNonUint s2 -> (fn s1 s2)
  | SL.TypeofString (t, _), SL.ConcreteUint s -> (fn (SL.stringofTypeof t) s)
  | SL.ConcreteUint s, SL.TypeofString (t, _) -> (fn s (SL.stringofTypeof t))
  | SL.TypeofString (t, _), SL.ConcreteNonUint s -> (fn (SL.stringofTypeof t) s)
  | SL.ConcreteNonUint s, SL.TypeofString (t, _) -> (fn s (SL.stringofTypeof t))
  | SL.TypeofString (t1, _), SL.TypeofString (t2, _) -> (fn (SL.stringofTypeof t1) (SL.stringofTypeof t2))
  | _ -> top

let str_str_to_str_fn fn v1 v2 = str_str_to_fn (fun v1 v2 -> str (fn v1 v2)) (ValueLattice.injectStr (StringLattice._Top ())) v1 v2

let str_str_to_bool_fn fn v1 v2 = str_str_to_fn (fun v1 v2 -> bool (fn v1 v2)) (ValueLattice.injectBool (BoolLattice._Top ())) v1 v2

let str_str_to_num_fn fn v1 v2 = str_str_to_fn (fun v1 v2 -> num (fn v1 v2)) (ValueLattice.injectNum (NumLattice._Top ())) v1 v2

let string_plus v1 v2 _ = str_str_to_str_fn (^) v1 v2

let string_lessthan v1 v2 _ = str_str_to_bool_fn (<) v1 v2

let stx_eq v1 v2 _ = 
  let module VL = ValueLattice in
  match (VL.asMono v1, VL.asMono v2) with
  | VL.Undef u1, VL.Undef u2 -> VL.injectBool (UndefLattice.eq u1 u2)
  | VL.Null n1, VL.Null n2 -> VL.injectBool (NullLattice.eq n1 n2)
  | VL.Bool b1, VL.Bool b2 -> VL.injectBool (BoolLattice.eq b1 b2)
  | VL.Num n1, VL.Num n2 -> VL.injectBool (NumLattice.eq n1 n2)
  | VL.Str s1, VL.Str s2 -> VL.injectBool (StringLattice.eq s1 s2)
  | VL.Obj _, VL.Obj _
  | VL.Addrs _, VL.Addrs _
  | VL.Closure _, VL.Closure _ -> bool (v1 == v2)
  | _ -> bool false


let num_to_fn fn top v =
  let module VL = ValueLattice in
  let module NL = NumLattice in
  match (VL.numOf v) with
  | NL.Bot -> VL._Bot ()
  | NL.PosInf
  | NL.NegInf
  | NL.INF
  | NL.NaN -> fn 0.
  | NL.ConcreteUint i -> (fn (float_of_int i))
  | NL.ConcreteNonUint f -> (fn f)
  | NL.Num
  | NL.NonUint
  | NL.Uint -> top

(* (\* Algorithm 11.9.3, steps 1 through 19. Steps 20 and 21 are desugared to *)
(*    access the heap. *\) *)
let abs_eq v1 v2 _ = 
  let module VL = ValueLattice in
  let boolTop = VL.injectBool (BoolLattice._Top ()) in
  match (v1, v2, VL.asMono v1, VL.asMono v2) with
  | _, _,  VL.Null _, VL.Undef _
  | _, _, VL.Undef _, VL.Null _ -> bool true
  | s, n, VL.Str _, VL.Num _
  | n, s, VL.Num _, VL.Str _ -> str_to_fn (fun s ->
    num_to_fn (fun n -> try bool (n = float_of_string s) with Failure _ -> bool false) boolTop n) boolTop s
  | n, _, VL.Num _, VL.Bool b
  | _, n, VL.Bool b, VL.Num _ -> 
    (match b with
    | BoolLattice.Bot -> VL.injectBool (BoolLattice._Bot ())
    | BoolLattice.Bool -> boolTop
    | _ -> num_to_fn (fun n -> if (unbool b) then bool (n = 1.0) else bool (n = 0.0)) boolTop n)
  | _ -> bool false


let has_property obj field store =
  let module VL = ValueLattice in
  let module SL = StringLattice in
  let module OL = ObjLattice in
  try 
    let bStr = match (VL.strOf field) with
      | SL.Bot -> raise (Pointy (VL._Bot ()))
      | SL.ConcreteUint s
      | SL.ConcreteNonUint s -> s
      | SL.TypeofString (t, _) -> (SL.stringofTypeof t)
      | _ -> raise (Pointy (VL.injectBool (BoolLattice._Top ()))) in
    let rec checkObj obj =
      match (VL.addrsOf obj) with
      | AddressSetLattice.Set addrs ->
        let value = VL.join (List.map (fun addr -> V.Store.find addr store)
                               (AddressSetLattice.elements addrs)) in
        let o = VL.objOf value in
        (match o with
        | OL.Obj ({OL.proto = p}, props) -> 
          (try 
             if (IdMap.mem bStr props) then bool true
             else (match p with None -> bool false | Some proto -> checkObj proto)
           with Not_found -> (match p with None -> bool false | Some proto -> checkObj proto))
        | OL.Bot -> raise (Pointy (VL._Bot ()))
        | OL.Top -> raise (Pointy (VL.injectBool (BoolLattice._Top ()))))
      | a -> raise (Pointy (VL.injectBool (BoolLattice._Top ()))) in
    checkObj obj
  with Pointy e -> e

let has_own_property obj field store =
  let module VL = ValueLattice in
  let module SL = StringLattice in
  let module OL = ObjLattice in
  try 
    let bStr = match (VL.strOf field) with
      | SL.Bot -> raise (Pointy (VL._Bot ()))
      | SL.ConcreteUint s
      | SL.ConcreteNonUint s -> s
      | SL.TypeofString (t, _) -> (SL.stringofTypeof t)
      | _ -> raise (Pointy (VL.injectBool (BoolLattice._Top ()))) in
    let rec checkObj obj =
      match (VL.addrsOf obj) with
      | AddressSetLattice.Set addrs ->
        let value = VL.join (List.map (fun addr -> V.Store.find addr store)
                               (AddressSetLattice.elements addrs)) in
        let o = VL.objOf value in
        (match o with
        | OL.Obj ({OL.proto = p}, props) -> 
          (try 
             bool (IdMap.mem bStr props)
           with Not_found -> bool false)
        | OL.Bot -> raise (Pointy (VL._Bot ()))
        | OL.Top -> raise (Pointy (VL.injectBool (BoolLattice._Top ()))))
      | a -> raise (Pointy (VL.injectBool (BoolLattice._Top ()))) in
    checkObj obj
  with Pointy e -> e

let base n r =
  let rec get_digits n l = match n with
    | 97 -> 'a' :: l
    | i -> get_digits (n - 1) ((Char.chr i) :: l) in
  let digits =
    ['0'; '1'; '2'; '3'; '4'; '5'; '6'; '7'; '8'; '9'] @ (get_digits 122 []) in
  let rec get_num_digits num so_far =
    if (r ** so_far) > num then so_far -. 1.0
    else get_num_digits num (so_far +. 1.0) in
  let rec convert b result len =
    let lp = r ** len in
    let index = floor (b /. lp) in
    let digit = String.make 1 (List.nth digits (int_of_float index)) in
    if len = 0.0 then result ^ digit
    else convert (b -. (index *. lp)) (result ^ digit)  (len -. 1.0) in
  let rec shift frac n = if n = 0 then frac else shift (frac *. 10.0) (n - 1) in
  let (f, integ) = modf n in
  (* TODO(joe): shifted is unused *)
  (* let shifted = shift f ((String.length (string_of_float f)) - 2) in *)
  if (f = 0.0) then
    let d = get_num_digits n 0.0 in
    convert n "" d
  else
    (* TODO: implement *)
    "non-base-10 with fractional parts NYI"

let get_base v1 v2 _ = num_num_to_fn (fun x y ->
  let result = base (abs_float x) (abs_float y) in
  str (if x < 0.0 then "-" ^ result else result)) 
  (ValueLattice.injectStr (StringLattice._Top ())) (ValueLattice.injectStr (StringLattice._Top ()))
  v1 v2

let char_at a b _ = str_to_fn (fun s ->
  num_to_fn (fun n -> str (String.make 1 (String.get s (int_of_float n)))) 
    (ValueLattice.injectStr (StringLattice._Top ())) b) 
    (ValueLattice.injectStr (StringLattice._Top ())) a

(* let char_at a b _ = match a, b with *)
(*   | String (_, _, s), Num (_, _, n) -> *)
(*     str (String.make 1 (String.get s (int_of_float n))) *)
(*   | _ -> raise (CpsThrow ( "char_at didn't get a string and a number")) *)

let locale_compare v1 v2 _ = str_str_to_fn (fun r s -> num (float_of_int (String.compare r s))) (ValueLattice.injectNum NumLattice.Uint) v1 v2

let pow = arith "**" (fun v1 v2 -> v1 ** v2)

let to_fixed v1 v2 _ = num_num_to_fn (fun x f ->
    let s = string_of_float x
    and fint = int_of_float f in
    if fint = 0
      then str (string_of_int (int_of_float x))
      else let dot_index = String.index s '.'
      and len = String.length s in
      let prefix_chars = dot_index in
      let decimal_chars = len - (prefix_chars + 1) in
      if decimal_chars = fint then str s
      else if decimal_chars > fint
        then let fixed_s = String.sub s 0 (fint - prefix_chars) in
        str (fixed_s)
      else let suffix = String.make (fint - decimal_chars) '0' in
        str (s ^ suffix)) (ValueLattice.injectStr (StringLattice._Top ())) (ValueLattice.injectStr (StringLattice._Top ())) 
  v1 v2

let is_accessor a b store =
  let module VL = ValueLattice in
  let module SL = StringLattice in
  let module OL = ObjLattice in
  try 
    let bStr = match (VL.strOf b) with
      | SL.Bot -> raise (Pointy (VL._Bot ()))
      | SL.ConcreteUint s
      | SL.ConcreteNonUint s -> s
      | SL.TypeofString (t, _) -> (SL.stringofTypeof t)
      | _ -> raise (Pointy (VL.injectBool (BoolLattice._Top ()))) in
    let rec checkObj obj =
      match (VL.addrsOf obj) with
      | AddressSetLattice.Set addrs ->
        let value = VL.join (List.map (fun addr -> V.Store.find addr store)
                               (AddressSetLattice.elements addrs)) in
        let o = VL.objOf value in
        (match o with
        | OL.Obj ({OL.proto = p}, props) -> 
          (try
             match IdMap.find bStr props with
             | OL.Accessor _ -> bool true
             | OL.Data _ -> bool false
             | _ -> raise (Pointy (VL.injectBool (BoolLattice._Top ())))
           with Not_found -> match p with None -> bool false | Some p -> checkObj p)
        | OL.Bot -> raise (Pointy (VL._Bot ()))
        | OL.Top -> raise (Pointy (VL.injectBool (BoolLattice._Top ()))))
      | a -> raise (Pointy (VL.injectBool (BoolLattice._Top ()))) in
    checkObj a
  with Pointy e -> e
       
let op2 op : ValueLattice.t -> ValueLattice.t -> ValueLattice.t V.Store.t -> ValueLattice.t = match op with
  | "+" -> arith_sum
  | "-" -> arith_sub
  | "/" -> arith_div
  | "*" -> arith_mul
  | "%" -> arith_mod
  | "&" -> bitwise_and
  | "|" -> bitwise_or
  | "^" -> bitwise_xor
  | "<<" -> bitwise_shiftl
  | ">>" -> bitwise_shiftr
  | ">>>" -> bitwise_zfshiftr
  | "<" -> arith_lt
  | "<=" -> arith_le
  | ">" -> arith_gt
  | ">=" -> arith_ge
  | "stx=" -> stx_eq
  | "abs=" -> abs_eq
  | "hasProperty" -> has_property
  | "hasOwnProperty" -> has_own_property
  | "string+" -> string_plus
  | "string<" -> string_lessthan
  | "base" -> get_base
  | "char-at" -> char_at
  | "locale-compare" -> locale_compare
  | "pow" -> pow
  | "to-fixed" -> to_fixed
  | "isAccessor" -> is_accessor
  | _ -> failwith ("no implementation of binary operator: " ^ op)
