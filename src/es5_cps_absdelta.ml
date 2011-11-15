open Prelude
module E = Es5_cps
module V = Es5_cps_values
open Es5_cps_values


module type Lattice = sig
  type t
  val _Top : t
  val _Bot : t
  val meet : t list -> t
  val join : t list -> t
end

module type SET_LATTICE = sig 
  type s
  type elt
  type t = Bot | Set of s | Top
  val _Top : t
  val _Bot : t
  val meet : t list -> t
  val join : t list -> t
  val elements : s -> elt list
end
module SetLattice (S : Set.S) : SET_LATTICE with type s = S.t with type elt = S.elt = struct
  type s = S.t
  type elt = S.elt
  type t = Bot | Set of s | Top
  let _Bot = Bot
  let _Top = Top
  let join ts = 
    let join' t1 t2 = match (t1, t2) with
      | Bot, t
      | t, Bot -> t
      | _, Top
      | Top, _ -> Top
      | Set s1, Set s2 -> Set (S.union s1 s2)
    in List.fold_left join' Bot ts
  let meet ts =
    let meet' t1 t2 = match (t1, t2) with
      | Top, t
      | t, Top -> t
      | Bot, _
      | _, Bot -> Bot
      | Set s1, Set s2 -> Set (S.inter s1 s2)
    in List.fold_left meet' Top ts
  let elements set = S.elements set
end
module CLOSURE = struct
  type t = id * id * id list * E.cps_exp * V.bindingEnv * V.retContEnv * V.exnContEnv
  let compare = Pervasives.compare
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
  val _Top : t
  val _Bot : t
  val meet : t list -> t
  val join : t list -> t
  val inject : bool -> t
  val injectTypeof : bool * ValueLattice.t * StringLattice.typeofStrings -> t
end = struct
  type t = 
    | Bot 
    | TrueTypeof of StringLattice.typeofStrings * ValueLattice.t
    | True 
    | FalseTypeof of StringLattice.typeofStrings * ValueLattice.t
    | False
    | Bool
  let _Top = Bool
  let _Bot = Bot
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
      | TrueTypeof (t1, i1), TrueTypeof (t2, i2) -> if t1 == t2 && i1 == i2 then TrueTypeof (t1, i1) else True
      | FalseTypeof (t1, i1), FalseTypeof (t2, i2) -> if t1 == t2 && i1 == i2 then FalseTypeof (t1, i1) else False
      | True, True
      | True, TrueTypeof _ 
      | TrueTypeof _, True -> True
      | False, False
      | False, FalseTypeof _
      | FalseTypeof _, False -> False
      | Bot, t
      | t, Bot -> t
    in List.fold_left join' _Bot ts
  let meet ts =
    let meet' t1 t2 = match (t1, t2) with
      | Bot, _
      | _, Bot -> Bot
      | False, False -> False
      | True, True -> True
      | TrueTypeof (t1, i1), TrueTypeof (t2, i2) -> if t1 == t2 && i1 == i2 then TrueTypeof (t1, i1) else Bot
      | FalseTypeof (t1, i1), FalseTypeof (t2, i2) -> if t1 == t2 && i1 == i2 then FalseTypeof (t1, i1) else Bot
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
    in List.fold_left meet' _Top ts
  let inject b = if b then True else False
  let injectTypeof (b, id, ty) = if b then TrueTypeof (ty, id) else FalseTypeof (ty, id)
end
and UndefLattice : sig
  type t = Bot | Undef
  val _Top : t
  val _Bot : t
  val meet : t list -> t
  val join : t list -> t
end = struct
  type t = Bot | Undef
  let _Top = Undef
  let _Bot = Bot
  let join ts =
    let join' t1 t2 = match (t1, t2) with
      | Undef, _
      | _, Undef -> Undef
      | _ -> Bot
    in List.fold_left join' _Bot ts
  let meet ts =
    let meet' t1 t2 = match (t1, t2) with
      | Bot, _
      | _, Bot -> Bot
      | _ -> Undef
    in List.fold_left meet' _Top ts
end
and NullLattice : sig
  type t = Bot | Null
  val _Top : t
  val _Bot : t
  val meet : t list -> t
  val join : t list -> t
end = struct
  type t = Bot | Null
  let _Top = Null
  let _Bot = Bot
  let join ts =
    let join' t1 t2 = match (t1, t2) with
      | Null, _
      | _, Null -> Null
      | _ -> Bot
    in List.fold_left join' _Bot ts
  let meet ts =
    let meet' t1 t2 = match (t1, t2) with
      | Bot, _
      | _, Bot -> Bot
      | _ -> Null
    in List.fold_left meet' _Top ts
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
  val _Top : t
  val _Bot : t
  val meet : t list -> t
  val join : t list -> t
  val inject : string -> t
  val injectTypeof : typeofStrings * ValueLattice.t -> t
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
  let _Top = String
  let _Bot = Bot
  let join ts =
    let join' t1 t2 = match (t1, t2) with
      | Bot, t
      | t, Bot -> t
      | ConcreteUint s1, ConcreteUint s2 -> if s1 == s2 then t1 else UintString
      | ConcreteUint _, UintString
      | UintString, ConcreteUint _ 
      | UintString, UintString -> UintString
      | ConcreteNonUint s, TypeofString (t, id)
      | TypeofString (t, id), ConcreteNonUint s -> 
        let b = (match t with
          | TyUndefined -> s == "undefined"
          | TyNull -> s == "null"
          | TyString -> s == "string"
          | TyNumber -> s == "number"
          | TyBoolean -> s == "boolean"
          | TyFunction -> s == "function"
          | TyObject -> s == "object"
          | TyLambda -> s == "lambda") in
        if b then TypeofString (t, id) else NonUintString
      | TypeofString (ty1, id1), TypeofString (ty2, id2) -> if ty1 == ty2 then t1 else NonUintString
      | TypeofString _, NonUintString
      | NonUintString, TypeofString _ -> NonUintString
      | ConcreteNonUint s1, ConcreteNonUint s2 -> if s1 == s2 then t1 else NonUintString
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
    in List.fold_left join' _Bot ts
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
        let b = (match t with
          | TyUndefined -> s == "undefined"
          | TyNull -> s == "null"
          | TyString -> s == "string"
          | TyNumber -> s == "number"
          | TyBoolean -> s == "boolean"
          | TyFunction -> s == "function"
          | TyObject -> s == "object"
          | TyLambda -> s == "lambda") in
        if b then TypeofString(t, id) else Bot
      | TypeofString (ty1, id1), TypeofString (ty2, id2) -> if ty1 == ty2 then t1 else Bot
      | UintString, ConcreteUint s
      | ConcreteUint s, UintString -> ConcreteUint s
      | ConcreteUint s1, ConcreteUint s2 -> if s1 == s2 then t1 else Bot
      | ConcreteNonUint s1, ConcreteNonUint s2 -> if s1 == s2 then t1 else Bot
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
    in List.fold_left meet' _Top ts
  let inject s =
    try
      let n = int_of_string s in
      if n >= 0 then ConcreteUint s else ConcreteNonUint s
    with _ -> ConcreteNonUint s
  let injectTypeof (t, v) = TypeofString (t, v)
end
and NumLattice : sig
  type t = Bot | PosInf | NegInf | INF | NaN 
           | ConcreteUint of int | Uint | ConcreteNonUint of float | NonUint | Num
  val _Top : t
  val _Bot : t
  val meet : t list -> t
  val join : t list -> t
  val inject : float -> t
end = struct
  type t = Bot | PosInf | NegInf | INF | NaN 
           | ConcreteUint of int | Uint | ConcreteNonUint of float | NonUint | Num
  let _Bot = Bot
  let _Top = Num
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
      | ConcreteUint n1, ConcreteUint n2 -> if n1 == n2 then t1 else Uint
      | ConcreteUint _, Uint
      | Uint, ConcreteUint _ 
      | Uint, Uint -> Uint
      | ConcreteNonUint n1, ConcreteNonUint n2 -> if n1 == n2 then t1 else NonUint
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
    in List.fold_left join' _Bot ts
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
      | ConcreteUint n1, ConcreteUint n2 -> if n1 == n2 then t1 else Bot
      | ConcreteNonUint n, NonUint
      | NonUint, ConcreteNonUint n -> ConcreteNonUint n
      | ConcreteNonUint n1, ConcreteNonUint n2 -> if n1 == n2 then t1 else Bot
      | ConcreteNonUint _, _
      | ConcreteUint _, _
      | Uint, _
      | NonUint, _ -> Bot
    in List.fold_left meet' _Top ts
  let inject f = 
    match (classify_float f) with
    | FP_nan -> NaN
    | FP_infinite -> if (f > 0.) then PosInf else NegInf
    | FP_zero -> ConcreteUint 0
    | _ ->
      try
        let n = int_of_float f in
        if (f -. (float_of_int n) < epsilon_float) && n >= 0 then ConcreteUint n else ConcreteNonUint f
      with _ -> ConcreteNonUint f
end
and AddressSetLattice : (SET_LATTICE with type s = AddressSet.t and type elt = AddressSet.elt) = SetLattice(AddressSet)
and ClosureSetLattice : (SET_LATTICE with type s = ClosureSet.t and type elt = ClosureSet.elt) = SetLattice(ClosureSet)
and ObjLattice : sig
  type bindAttrs = 
      { primval : ValueLattice.t option;
        code : ValueLattice.t option;
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
  val setCode : t -> ValueLattice.t option -> t
  val setPrimval : t -> ValueLattice.t option -> t
  val setWritable : t -> id -> BoolLattice.t -> t
  val setValue : t -> id -> ValueLattice.t -> t
  val setGetter : t -> id -> ValueLattice.t -> t
  val setSetter : t -> id -> ValueLattice.t -> t
end = struct
  type bindAttrs = 
      { primval : ValueLattice.t option;
        code : ValueLattice.t option;
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
        let c = joinOpt c1 c2 in
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
          | v, None -> Some ValueLattice._Bot
          | Some v1, Some v2 -> Some (ValueLattice.meet [v1; v2]) in
        let v = meetOpt v1 v2 in
        let c = meetOpt c1 c2 in
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
         | Unknown -> Obj(attrs, IdMap.add id (Data({writable = b; value = ValueLattice._Top}, 
                                                    BoolLattice._Top, BoolLattice._Top)) props)
         | _ -> Obj(attrs, IdMap.add id PropTop props)
       with _ -> Obj(attrs, IdMap.add id (Data({writable = b; value = ValueLattice._Top}, 
                                               BoolLattice._Top, BoolLattice._Top)) props))
    | _ -> obj
  let setValue obj id v = match obj with
    | Obj(attrs, props) -> 
      (try 
         match (IdMap.find id props) with
         | Data(p, e, c) -> Obj(attrs, IdMap.add id (Data({p with value = v}, e, c)) props)
         | Unknown -> Obj(attrs, IdMap.add id (Data({writable = BoolLattice._Top; value = v}, 
                                                    BoolLattice._Top, BoolLattice._Top)) props)
         | _ -> Obj(attrs, IdMap.add id PropTop props)
       with _ -> Obj(attrs, IdMap.add id (Data({writable = BoolLattice._Top; value = v},
                                               BoolLattice._Top, BoolLattice._Top)) props))
    | _ -> obj
  let setGetter obj id g = match obj with
    | Obj(attrs, props) -> 
      (try 
         match (IdMap.find id props) with
         | Accessor(p, e, c) -> Obj(attrs, IdMap.add id (Accessor({p with getter = g}, e, c)) props)
         | Unknown -> Obj(attrs, IdMap.add id (Accessor({getter = g; setter = ValueLattice._Top}, 
                                                        BoolLattice._Top, BoolLattice._Top)) props)
         | _ -> Obj(attrs, IdMap.add id PropTop props)
       with _ -> Obj(attrs, IdMap.add id (Accessor({getter = g; setter = ValueLattice._Top},
                                                   BoolLattice._Top, BoolLattice._Top)) props))
    | _ -> obj
  let setSetter obj id s = match obj with
    | Obj(attrs, props) -> 
      (try 
         match (IdMap.find id props) with
         | Accessor(p, e, c) -> Obj(attrs, IdMap.add id (Accessor({p with setter = s}, e, c)) props)
         | Unknown -> Obj(attrs, IdMap.add id (Accessor({setter = s; getter = ValueLattice._Top}, 
                                                        BoolLattice._Top, BoolLattice._Top)) props)
         | _ -> Obj(attrs, IdMap.add id PropTop props)
       with _ -> Obj(attrs, IdMap.add id (Accessor({setter = s; getter = ValueLattice._Top},
                                                   BoolLattice._Top, BoolLattice._Top)) props))
    | _ -> obj
end
and ValueLattice : sig
  type t = UndefLattice.t * NullLattice.t * BoolLattice.t * NumLattice.t * StringLattice.t
      * ObjLattice.t * AddressSetLattice.t * ClosureSetLattice.t
  val _Top : t
  val _Bot : t
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
end = struct
  type t = UndefLattice.t * NullLattice.t * BoolLattice.t * NumLattice.t * StringLattice.t
      * ObjLattice.t * AddressSetLattice.t * ClosureSetLattice.t
  let _Bot = (UndefLattice._Bot, NullLattice._Bot, BoolLattice._Bot, NumLattice._Bot, StringLattice._Bot,
              ObjLattice._Bot (), AddressSetLattice._Bot, ClosureSetLattice._Bot)
  let _Top = (UndefLattice._Top, NullLattice._Top, BoolLattice._Top, NumLattice._Top, StringLattice._Top,
              ObjLattice._Top (), AddressSetLattice._Top, ClosureSetLattice._Top)
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
    List.fold_left join' _Bot ts
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
    List.fold_left meet' _Top ts
  let injectUndef u = (u, NullLattice._Bot, BoolLattice._Bot, NumLattice._Bot, StringLattice._Bot,
                       ObjLattice._Bot (), AddressSetLattice._Bot, ClosureSetLattice._Bot)
  let injectNull n = (UndefLattice._Bot, n, BoolLattice._Bot, NumLattice._Bot, StringLattice._Bot,
                       ObjLattice._Bot (), AddressSetLattice._Bot, ClosureSetLattice._Bot)
  let injectBool b = (UndefLattice._Bot, NullLattice._Bot, b, NumLattice._Bot, StringLattice._Bot,
                       ObjLattice._Bot (), AddressSetLattice._Bot, ClosureSetLattice._Bot)
  let injectNum n = (UndefLattice._Bot, NullLattice._Bot, BoolLattice._Bot, n, StringLattice._Bot,
                       ObjLattice._Bot (), AddressSetLattice._Bot, ClosureSetLattice._Bot)
  let injectStr s = (UndefLattice._Bot, NullLattice._Bot, BoolLattice._Bot, NumLattice._Bot, s,
                       ObjLattice._Bot (), AddressSetLattice._Bot, ClosureSetLattice._Bot)
  let injectObj o = (UndefLattice._Bot, NullLattice._Bot, BoolLattice._Bot, NumLattice._Bot, StringLattice._Bot,
                       o, AddressSetLattice._Bot, ClosureSetLattice._Bot)
  let injectAddrs a = (UndefLattice._Bot, NullLattice._Bot, BoolLattice._Bot, NumLattice._Bot, StringLattice._Bot,
                       ObjLattice._Bot (), a, ClosureSetLattice._Bot)
  let injectClosure c = (UndefLattice._Bot, NullLattice._Bot, BoolLattice._Bot, NumLattice._Bot, 
                         StringLattice._Bot, ObjLattice._Bot (), AddressSetLattice._Bot, c)
  let undefOf (u, n, b, i, s, o, a, c) = u
  let nullOf (u, n, b, i, s, o, a, c) = n
  let boolOf (u, n, b, i, s, o, a, c) = b
  let numOf (u, n, b, i, s, o, a, c) = i
  let strOf (u, n, b, i, s, o, a, c) = s
  let objOf (u, n, b, i, s, o, a, c) = o
  let addrsOf (u, n, b, i, s, o, a, c) = a
  let closureOf (u, n, b, i, s, o, a, c) = c
end
type absStore = ValueLattice.t V.Store.t


let newLabel = Es5_cps.newLabel
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

let to_int v = match v with
  | NumLattice.ConcreteUint i -> i
  | NumLattice.ConcreteNonUint f -> int_of_float f
  | _ -> raise (CpsThrow "expected number in es5_cps_absdelta.to_int")

let typeof ((u, n, b, i, s, o, a, c) as v) _ = 
  let module VL = ValueLattice in
  let module SL = StringLattice in
  let module OL = ObjLattice in
  let vi = VL.injectStr in
  if (VL.join [(VL.injectUndef u); v] == VL.injectUndef u) then vi (SL.injectTypeof(SL.TyUndefined, v))
  else if (VL.join [(VL.injectNull n); v] == VL.injectNull n) then vi (SL.injectTypeof(SL.TyNull, v))
  else if (VL.join [(VL.injectStr s); v] == VL.injectStr s) then vi (SL.injectTypeof(SL.TyString, v))
  else if (VL.join [(VL.injectNum i); v] == VL.injectNum i) then vi (SL.injectTypeof(SL.TyNumber, v))
  else if (VL.join [(VL.injectBool b); v] == VL.injectBool b) then vi (SL.injectTypeof(SL.TyBoolean, v))
  else if (VL.join [(VL.injectObj o); v] == VL.injectObj o) then 
    (match o with
    | OL.Obj({OL.code = Some _}, _) -> vi (SL.injectTypeof(SL.TyFunction, v))
    |_ -> vi (SL.injectTypeof(SL.TyObject, v)))
  else if (VL.join [(VL.injectClosure c); v] == VL.injectClosure c) then vi (SL.injectTypeof(SL.TyLambda, v))
  else if (VL.join [(VL.injectAddrs a); v] == VL.injectAddrs a) then VL._Bot
  else VL._Top

let surface_typeof ((u, n, b, i, s, o, a, c) as v) store = 
  let module VL = ValueLattice in
  let module SL = StringLattice in
  let vi = VL.injectStr in
  if (VL.join [(VL.injectClosure c); v] == VL.injectClosure c) then VL._Bot
  else if (VL.join [(VL.injectNull n); v] == VL.injectNull n) then vi (SL.injectTypeof(SL.TyObject, v))
  else typeof v store
  
let is_primitive ((u, n, b, i, s, o, a, c) as v) _ = 
  let module VL = ValueLattice in
  let module SL = StringLattice in
  let module OL = ObjLattice in
  if (VL.join [(VL.injectUndef u); v] == VL.injectUndef u) then bool true
  else if (VL.join [(VL.injectNull n); v] == VL.injectNull n) then bool true
  else if (VL.join [(VL.injectStr s); v] == VL.injectStr s) then bool true
  else if (VL.join [(VL.injectNum i); v] == VL.injectNum i) then bool true
  else if (VL.join [(VL.injectBool b); v] == VL.injectBool b) then bool true
  else bool false

let float_str n = 
  let module NL = NumLattice in
  let module SL = StringLattice in 
  match n with
  | NL.Bot -> SL._Bot
  | NL.PosInf -> SL.ConcreteNonUint "Infinity"
  | NL.NegInf -> SL.ConcreteNonUint "-Infinity"
  | NL.NaN -> SL.ConcreteNonUint "NaN"
  | NL.ConcreteUint i -> SL.ConcreteNonUint (string_of_int i)
  | NL.ConcreteNonUint f -> SL.ConcreteNonUint (string_of_float f)
  | _ -> SL._Top

let prim_to_str ((u, n, b, i, s, o, a, c) as v) store = 
  let module VL = ValueLattice in
  let module SL = StringLattice in
  let module BL = BoolLattice in
  let module OL = ObjLattice in
  if (VL.join [(VL.injectUndef u); v] == VL.injectUndef u) then str "undefined"
  else if (VL.join [(VL.injectNull n); v] == VL.injectNull n) then str "null"
  else if (VL.join [(VL.injectStr s); v] == VL.injectStr s) then v
  else if (VL.join [(VL.injectBool b); v] == VL.injectBool b) then 
    (match b with
    | BL.True 
    | BL.TrueTypeof _ -> str "true"
    | BL.False
    | BL.FalseTypeof _ -> str "false"
    | BL.Bot -> VL._Bot
    | _ -> VL._Top)
  else if (VL.join [(VL.injectNum i); v] == VL.injectNum i) then 
    (match (float_str i) with
    | SL.Bot -> VL._Bot
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
    | _ -> VL._Top)
  else VL._Bot


let strlen ((u, n, b, i, s, o, a, c) as v) _ =
  let module VL = ValueLattice in
  let module SL = StringLattice in
  if (VL.join [(VL.injectStr s); v] == VL.injectStr s) then 
    (match s with
    | SL.Bot -> VL._Bot
    | SL.ConcreteNonUint s -> num (float_of_int (String.length s))
    | SL.ConcreteUint s -> num (float_of_int (String.length s))
    | _ -> VL._Top
    )
  else VL._Bot

(* Section 9.3, excluding objects *)
let prim_to_num ((u, n, b, i, s, o, a, c) as v) _ =
  let module VL = ValueLattice in
  let module SL = StringLattice in
  let module NL = NumLattice in
  let module BL = BoolLattice in
  let num n = VL.injectNum (NL.inject n) in
  if (VL.join [(VL.injectUndef u); v] == VL.injectUndef u) then num nan
  else if (VL.join [(VL.injectNull n); v] == VL.injectNull n) then num 0.0
  else if (VL.join [(VL.injectNum i); v] == VL.injectNum i) then v
  else if (VL.join [(VL.injectBool b); v] == VL.injectBool b) then 
    (match b with
    | BL.True 
    | BL.TrueTypeof _ -> num 1.0
    | BL.False
    | BL.FalseTypeof _ -> num 0.0
    | BL.Bot -> VL._Bot
    | _ -> VL._Top)
  else if (VL.join [(VL.injectStr s); v] == VL.injectStr s) then 
    (match s with
    | SL.Bot -> VL._Bot
    | SL.ConcreteNonUint "" -> num 0.0
    | SL.ConcreteNonUint s -> begin try num (float_of_string s) with _ -> num nan end
    | SL.ConcreteUint s -> num (float_of_string s)
    | _ -> VL._Top
    )
  else VL._Bot
  
let prim_to_bool ((u, n, b, i, s, o, a, c) as v) _ = 
  let module VL = ValueLattice in
  let module SL = StringLattice in
  let module NL = NumLattice in
  let module BL = BoolLattice in
  if (VL.join [(VL.injectUndef u); v] == VL.injectUndef u) then bool false
  else if (VL.join [(VL.injectNull n); v] == VL.injectNull n) then bool false
  else if (VL.join [(VL.injectNum i); v] == VL.injectNum i) then 
    (match i with
    | NL.NaN -> bool false
    | NL.ConcreteNonUint n -> bool (not (n = 0.0 || n = -0.0))
    | NL.ConcreteUint i -> bool (i != 0)
    | _ -> bool true
    )
  else if (VL.join [(VL.injectBool b); v] == VL.injectBool b) then v
  else if (VL.join [(VL.injectStr s); v] == VL.injectStr s) then 
    (match s with
    | SL.Bot -> VL._Bot
    | SL.ConcreteNonUint "" -> bool false
    | SL.ConcreteNonUint s -> bool true
    | SL.ConcreteUint "" -> bool false
    | SL.ConcreteUint s -> bool true
    | _ -> VL._Top
    )
  else bool true

let is_callable obj store = 
  let module VL = ValueLattice in
  let module ASL = AddressSetLattice in
  let module OL = ObjLattice in
  match (ValueLattice.addrsOf obj) with
  | ASL.Set addrs ->
    let value = VL.join (List.map (fun addr -> Store.find addr store)
                                     (ASL.elements addrs)) in
    (match (VL.objOf value) with
    | OL.Bot -> VL._Bot
    | OL.Obj ({OL.code = Some _}, _) -> bool true
    | OL.Obj _ -> bool false
    | OL.Top -> VL._Top)
  | _ -> bool false

let print v _ = match v with
  | String (_, _, s) -> 
      printf "%S\n%!" s; Undefined (dummy_pos, newLabel())
  | Num (_, _, n) -> let s = string_of_float n in printf "%S\n" s; Undefined (dummy_pos, newLabel())
  | _ -> failwith ("[cps-interp] Print received non-string: " ^ (pretty_bind v))

let is_extensible obj store = 
  let module VL = ValueLattice in
  let module ASL = AddressSetLattice in
  let module OL = ObjLattice in
  match (ValueLattice.addrsOf obj) with
  | ASL.Set addrs ->
    let value = VL.join (List.map (fun addr -> Store.find addr store)
                                     (ASL.elements addrs)) in
    (match (VL.objOf value) with
    | OL.Bot -> VL._Bot
    | OL.Obj ({OL.extensible = b}, _) -> VL.injectBool b
    | OL.Top -> VL._Top)
  | _ -> bool false

let prevent_extensions obj store = match (ValueLattice.addrsOf obj) with
  | AddressSetLattice.Set addrs ->
    let value = ValueLattice.join (List.map (fun addr -> Store.find addr store)
                                     (AddressSetLattice.elements addrs)) in
    let (u, n, b, i, s, o, a, c) = value in
    let o' = ObjLattice.setExtensible o BoolLattice.False in
    (u, n, b, i, s, o', a, c)
  | _ -> obj
      
let get_code obj store = match obj with
  | VarCell(_, _, a) -> (match (Store.find a store) with
    | Object (_, _, { code = Some v }, _) -> v
    | Object (_, _, { code = None }, _) -> Null (dummy_pos, newLabel())
    | _ -> raise (CpsThrow ( "get-code: " ^ (pretty_bind obj))))
  | _ -> raise (CpsThrow ( "get-code: " ^ (pretty_bind obj)))

let get_proto obj store = match obj with
  | VarCell(_, _, a) -> (match (Store.find a store) with
    | Object (_, _, { proto = Some p }, _) -> p
    | Object (_, _, { proto = None }, _) -> Null (dummy_pos, newLabel())
    | v -> raise (CpsThrow ( ("cps-get-proto got a non-object:"  ^ (pretty_bind obj)))))
  | v -> raise (CpsThrow ( ("cps-get-proto got a non-VarCell:"  ^ (pretty_bind obj))))

let get_primval obj store = match obj with
  | VarCell(_, _, a) -> (match (Store.find a store) with
    | Object (_, _, { primval = Some v }, _) -> v
    | Object (_, _, { primval = None }, _) -> raise (CpsThrow ( "get-primval on an object with no prim val"))
    | _ -> raise (CpsThrow ( "cps-get-primval: " ^ (pretty_bind obj))))
  | _ -> raise (CpsThrow ( "cps-get-primval: " ^ (pretty_bind obj)))

let get_class obj store = match obj with
  | VarCell(_, _, a) -> (match (Store.find a store) with
    | Object (_, _, { klass = s }, _) -> str s
    | _ -> raise (CpsThrow ( "cps-get-class: " ^ (pretty_bind obj))))
  | _ -> raise (CpsThrow ( "cps-get-class: " ^ (pretty_bind obj)))

(* All the enumerable property names of an object *)
let rec get_property_names obj store = match obj with
  | VarCell(_, _, a) -> (match (Store.find a store) with
    | Object _ ->
      let protos = obj::(all_protos obj store) in
      let folder o set = begin match o with
	| Object(_, _, attrs, props) ->
	  List.fold_left (fun s (k, v) -> 
            if enum v then IdSet.add k s else s) set props
	| _ -> set (* non-object prototypes don't contribute *) 
      end in
      let name_set = List.fold_right folder protos IdSet.empty in
      let name_list= IdSet.elements name_set in
      let prop_folder num name props = 
	((string_of_int num),
          (Data ({ value = String(dummy_pos, newLabel(), name); writable = false; }, false, false)))::props in
      let name_props = List.fold_right2 prop_folder 
        (iota (List.length name_list))
        name_list
        [] in
      let d_attrsv = { primval = None; code = None; proto = None; extensible = false; klass = "LambdaJS interal" }
      in Object(dummy_pos, newLabel(),d_attrsv, name_props)
    | _ -> raise (CpsThrow ( "get-property-names: " ^ (pretty_bind obj))))
  | _ -> raise (CpsThrow ( "get-property-names: " ^ (pretty_bind obj)))

and all_protos o store = 
  match o with
  | Object (_, _, { proto = Some p }, _) -> p::(all_protos p store)
  | VarCell (_, _, a) -> all_protos (Store.find a store) store
  | _ -> []

and enum prop = match prop with
  | Accessor (_, b, _)
  | Data (_, b, _) -> b

let get_own_property_names obj store = match obj with
  | VarCell(_, _, a) -> (match (Store.find a store) with
    | Object (_, _, _, props) ->
      let add_name n x m = 
        ((string_of_int x),
         (Data ({ value = String (dummy_pos, newLabel(), n); writable = false; }, false, false))) :: m in
      let namelist = List.fold_left (fun l (k, v) -> (k :: l)) [] props in
      let props = 
	List.fold_right2 add_name namelist (iota (List.length namelist)) []
      in
      let d = (float_of_int (List.length namelist)) in
      let final_props = 
        ("length",
         (Data ({ value = Num (dummy_pos, newLabel(), d); writable = false; }, false, false)))::props in 
      let d_attrsv = { primval = None; code = None; proto = None; 
                       extensible = false; klass = "LambdaJS interal" }
      in Object(dummy_pos, newLabel(), d_attrsv, final_props)
    | _ -> raise (CpsThrow ( "own-property-names: " ^ (pretty_bind obj))))
  | _ -> raise (CpsThrow ( "own-property-names: " ^ (pretty_bind obj)))

(* Implement this here because there's no need to expose the class
   property outside of the delta function *)
let object_to_string obj store = match obj with
  | VarCell(_, _, a) -> (match (Store.find a store) with
    | Object(_, _, {klass=s},_) -> str ("[object " ^ s ^ "]")
    | _ -> raise (CpsThrow ( "object-to-string, wasn't given object: " ^ (pretty_bind obj))))
  | _ -> raise (CpsThrow ( "object-to-string, wasn't given VarCell: " ^ (pretty_bind obj)))

let is_array obj store = match obj with
  | VarCell(_, _, a) -> (match (Store.find a store) with
    | Object(_, _, {klass="Array"},_) -> bool true
    | Object _ -> bool false
    | _ -> raise (CpsThrow ( "is-array: " ^ (pretty_bind obj))))
  | _ -> raise (CpsThrow ( "is-array: " ^ (pretty_bind obj)))


let to_int32 v _ = match v with
  | Num (_,_,d) -> Num(dummy_pos, newLabel(), (float_of_int (int_of_float d)))
  | _ -> raise (CpsThrow ( "to-int: " ^ (pretty_bind v)))

let nnot e _ = match e with
  | Undefined _ -> bool true
  | Null _ -> bool true
  | True _ -> bool false
  | False _ -> bool true
  | Num (_, _, d) -> if (d = 0.) || (d <> d) then bool true else bool false
  | String (_, _, s) -> if s = "" then bool true else bool false
  | Object _ -> bool false
  | Closure _ -> bool false
  | VarCell _ -> failwith "[cps-interp] Can't get nnot VarCell!"

let void v _ = Undefined (dummy_pos, newLabel())

let floor' n _ = match n with Num (_, _, d) -> num (floor d) | _ -> raise (CpsThrow ( "floor"))

let ceil' n _ = match n with Num (_, _, d) -> num (ceil d) | _ -> raise (CpsThrow ( "ceil"))

let absolute n _ = match n with Num (_, _, d) -> num (abs_float d) | _ -> raise (CpsThrow ( "abs"))

let log' n _ = match n with Num (_, _, d) -> num (log d ) | _ -> raise (CpsThrow ( "log"))

let ascii_ntoc n _ = match n with
  | Num (_, _, d) -> str (String.make 1 (Char.chr (int_of_float d)))
  | _ -> raise (CpsThrow ( "ascii_ntoc"))

let ascii_cton c _ = match c with
  | String (_, _, s) -> num (float_of_int (Char.code (String.get s 0)))
  | _ -> raise (CpsThrow ( "ascii_cton"))

let to_lower s _ = match s with
  | String (_, _, s) -> str (String.lowercase s)
  | _ -> raise (CpsThrow ( "to_lower"))

let to_upper s _ = match s with
  | String (_, _, s) -> str (String.uppercase s)
  | _ -> raise (CpsThrow ( "to_lower"))

let bnot b _ = match b with
  | Num (_, _, d) -> num (float_of_int (lnot (int_of_float d)))
  | _ -> raise (CpsThrow ( "bnot"))

let sine n _ = match n with
  | Num (_, _, d) -> num (sin d)
  | _ -> raise (CpsThrow ( "sin"))

let numstr s _ = match s with
  | String (_, _, s) -> num (try float_of_string s with Failure _ -> nan)
  | _ -> raise (CpsThrow ( "numstr"))

let op1 op : ValueLattice.t -> ValueLattice.t Store.t -> ValueLattice.t = match op with
  | "typeof" -> typeof
  | "surface-typeof" -> surface_typeof
  | "primitive?" -> is_primitive
  | "prim->str" -> prim_to_str
  | "prim->num" -> prim_to_num
  | "prim->bool" -> prim_to_bool
  | "is-callable" -> is_callable
  | "is-extensible" -> is_extensible
  | "prevent-extensions" -> prevent_extensions
  (* | "print" -> print *)
  (* | "get-proto" -> get_proto *)
  (* | "get-primval" -> get_primval *)
  (* | "get-class" -> get_class *)
  (* | "get-code" -> get_code *)
  (* | "property-names" -> get_property_names *)
  (* | "own-property-names" -> get_own_property_names *)
  (* | "object-to-string" -> object_to_string *)
  | "strlen" -> strlen
  (* | "is-array" -> is_array *)
  (* | "to-int32" -> to_int32 *)
  (* | "!" -> nnot *)
  (* | "void" -> void *)
  (* | "floor" -> floor' *)
  (* | "ceil" -> ceil' *)
  (* | "abs" -> absolute *)
  (* | "log" -> log' *)
  (* | "ascii_ntoc" -> ascii_ntoc *)
  (* | "ascii_cton" -> ascii_cton *)
  (* | "to-lower" -> to_lower *)
  (* | "to-upper" -> to_upper *)
  (* | "~" -> bnot *)
  (* | "sin" -> sine *)
  (* | "numstr->num" -> numstr *)
  | _ -> failwith ("no implementation of unary operator: " ^ op)

(* let arith s f_op v1 v2 _ = match v1, v2 with *)
(*   | Num (_, _, x), Num (_, _, y) -> num (f_op x y) *)
(*   | v1, v2 -> raise (CpsThrow ( ("arithmetic operator: " ^ s ^ " got non-numbers, " ^ *)
(*                                    "perhaps something wasn't desugared fully?"))) *)

(* let compare s f_op v1 v2 _ = match v1, v2 with *)
(*   | Num (_, _, x), Num (_, _, y) -> bool (f_op x y) *)
(*   | v1, v2 -> raise (CpsThrow ( ("compare operator: " ^ s ^ " got non-numbers, " ^ *)
(*                                    "perhaps something wasn't desugared fully?"))) *)

(* let arith_sum = arith "+" (+.) *)

(* let arith_sub = arith "-" (-.) *)

(* (\* OCaml syntax failure! Operator section syntax lexes as a comment. *\) *)
(* let arith_mul = arith "*" (fun x y -> x *. y) *)

(* let arith_div x y env = try arith "/" (/.) x y env *)
(* with Division_by_zero -> num infinity *)

(* let arith_mod x y env = try arith "mod" mod_float x y env *)
(* with Division_by_zero -> num nan *)

(* let arith_lt = compare "<" (<)  *)

(* let arith_le = compare "<=" (<=)  *)

(* let arith_gt = compare ">" (>)  *)

(* let arith_ge = compare ">=" (>=)  *)

(* let bitwise_and v1 v2 _ = num (float_of_int ((to_int v1) land (to_int v2))) *)

(* let bitwise_or v1 v2 _ = num (float_of_int ((to_int v1) lor (to_int v2))) *)

(* let bitwise_xor v1 v2 _ = num (float_of_int ((to_int v1) lxor (to_int v2))) *)

(* let bitwise_shiftl v1 v2 _ = num (float_of_int ((to_int v1) lsl (to_int v2))) *)

(* let bitwise_zfshiftr v1 v2 _ = num (float_of_int ((to_int v1) lsr (to_int v2))) *)

(* let bitwise_shiftr v1 v2 _ = num (float_of_int ((to_int v1) asr (to_int v2))) *)

(* let string_plus v1 v2 _ = match v1, v2 with *)
(*   | String (_, _, s1), String (_, _, s2) -> *)
(*       str (s1 ^ s2) *)
(*   | _ -> raise (CpsThrow ( "string concatenation")) *)

(* let string_lessthan v1 v2 _ = match v1, v2 with *)
(*   | String (_, _, s1), String (_, _, s2) -> bool (s1 < s2) *)
(*   | _ -> raise (CpsThrow ( "string less than")) *)

(* let stx_eq v1 v2 _ = bool begin match v1, v2 with *)
(*   | Num (_, _, x1), Num (_, _, x2) -> x1 = x2 *)
(*   | String (_, _, x1), String (_, _, x2) -> x1 = x2 *)
(*   | Undefined _, Undefined _ -> true *)
(*   | Null _, Null _ -> true *)
(*   | True _, True _ -> true *)
(*   | False _, False _ -> true *)
(*   | _ -> v1 == v2 (\* otherwise, pointer equality *\) *)
(* end *)

(* (\* Algorithm 11.9.3, steps 1 through 19. Steps 20 and 21 are desugared to *)
(*    access the heap. *\) *)
(* let abs_eq v1 v2 _ = bool begin *)
(*   if v1 = v2 then (\* works correctly on floating point values *\) *)
(*     true *)
(*   else match v1, v2 with *)
(*     | Null _, Undefined _ *)
(*     | Undefined _, Null _ -> true *)
(*     | String (_, _, s), Num (_, _, x) *)
(*     | Num (_, _, x), String (_, _, s) -> *)
(*           (try x = float_of_string s with Failure _ -> false) *)
(*     | Num (_, _, x), True _ | True _, Num (_, _, x) -> x = 1.0 *)
(*     | Num (_, _, x), False _ | False _, Num (_, _, x) -> x = 0.0 *)
(*     | _ -> false *)
(* (\* TODO: are these all the cases? *\) *)
(* end *)

(* let rec has_property obj field store = match obj with *)
(*   | VarCell (_, _, a) -> (match (Store.find a store), field with *)
(*     | Object(_, _, {proto=p}, props), String (_, _, s) ->  *)
(*       if List.mem_assoc s props  *)
(*       then bool true *)
(*       else (match p with None -> bool false | Some proto -> has_property proto field store) *)
(*     | _ -> bool false) *)
(*   | _ -> bool false *)

(* let has_own_property obj field store = match obj with *)
(*   | VarCell (_, _, a) -> (match (Store.find a store), field with *)
(*     | Object(_, _, {proto=p}, props), String (_, _, s) -> bool (List.mem_assoc s props) *)
(*     | Object _, _ -> raise (CpsThrow ( "has-own-property: field not a string")) *)
(*     | _, String (_, _, s) -> raise (CpsThrow ( ("has-own-property: obj not an object for field " ^ s))) *)
(*     | _ -> raise (CpsThrow ( "has-own-property: neither an object nor a string"))) *)
(*   | _ -> raise (CpsThrow ("[cps-interp] has-own-property didn't get a VarCell")) *)

(* let base n r =  *)
(*   let rec get_digits n l = match n with *)
(*     | 97 -> 'a' :: l *)
(*     | i -> get_digits (n - 1) ((Char.chr i) :: l) in *)
(*   let digits =  *)
(*     ['0'; '1'; '2'; '3'; '4'; '5'; '6'; '7'; '8'; '9'] @ (get_digits 122 []) in *)
(*   let rec get_num_digits num so_far = *)
(*     if (r ** so_far) > num then so_far -. 1.0 *)
(*     else get_num_digits num (so_far +. 1.0) in *)
(*   let rec convert b result len =  *)
(*     let lp = r ** len in *)
(*     let index = floor (b /. lp) in *)
(*     let digit = String.make 1 (List.nth digits (int_of_float index)) in *)
(*     if len = 0.0 then result ^ digit *)
(*     else convert (b -. (index *. lp)) (result ^ digit)  (len -. 1.0) in *)
(*   let rec shift frac n = if n = 0 then frac else shift (frac *. 10.0) (n - 1) in *)
(*   let (f, integ) = modf n in *)
(*   (\* TODO(joe): shifted is unused *\) *)
(*   (\* let shifted = shift f ((String.length (string_of_float f)) - 2) in *\) *)
(*   if (f = 0.0) then *)
(*     let d = get_num_digits n 0.0 in *)
(*     convert n "" d *)
(*   else *)
(*     (\* TODO: implement *\) *)
(*     "non-base-10 with fractional parts NYI" *)

(* let get_base n r _ = match n, r with *)
(*   | Num (_, _, x), Num (_, _, y) ->  *)
(*     let result = base (abs_float x) (abs_float y) in *)
(*     str (if x < 0.0 then "-" ^ result else result) *)
(*   | _ -> raise (CpsThrow ( "base got non-numbers")) *)

(* let char_at a b _ = match a, b with *)
(*   | String (_, _, s), Num (_, _, n) -> *)
(*     str (String.make 1 (String.get s (int_of_float n))) *)
(*   | _ -> raise (CpsThrow ( "char_at didn't get a string and a number")) *)

(* let locale_compare a b _ = match a, b with *)
(*   | String (_, _, r), String (_, _, s) -> *)
(*     num (float_of_int (String.compare r s)) *)
(*   | _ -> raise (CpsThrow ( "locale_compare didn't get 2 strings")) *)

(* let pow a b _ = match a, b with *)
(*   | Num (_, _, base), Num (_, _, exp) -> num (base ** exp) *)
(*   | _ -> raise (CpsThrow ( "pow didn't get 2 numbers")) *)

(* let to_fixed a b _ = match a, b with *)
(*   | Num (_, _, x), Num (_, _, f) ->  *)
(*     let s = string_of_float x *)
(*     and fint = int_of_float f in *)
(*     if fint = 0  *)
(*       then str (string_of_int (int_of_float x))  *)
(*       else let dot_index = String.index s '.' *)
(*       and len = String.length s in *)
(*       let prefix_chars = dot_index in *)
(*       let decimal_chars = len - (prefix_chars + 1) in *)
(*       if decimal_chars = fint then str s *)
(*       else if decimal_chars > fint *)
(*         then let fixed_s = String.sub s 0 (fint - prefix_chars) in *)
(*         str (fixed_s) *)
(*       else let suffix = String.make (fint - decimal_chars) '0' in *)
(*         str (s ^ suffix) *)
(*   | _ -> raise (CpsThrow ( "to-fixed didn't get 2 numbers")) *)

(* let rec is_accessor a b store = match a with *)
(*   | VarCell (_, _, a) -> (match (Store.find a store), b with *)
(*     | Object(_, _, {proto = p}, props), String (_, _, s) -> *)
(*       (try *)
(*          match List.assoc s props with *)
(*          | Data _ -> bool false *)
(*          | Accessor _ -> bool true *)
(*        with Not_found -> *)
(*          match p with None -> bool false | Some pr -> is_accessor pr b store) *)
(*     | Null _, String (_, _, s) -> raise (CpsThrow ( "isAccessor topped out")) *)
(*     | _ -> raise (CpsThrow ( "isAccessor"))) *)
(*   | _ -> raise (CpsThrow ("[cps-interp] isAccessor didn't get a VarCell")) *)
      
(* let op2 op = match op with *)
(*   | "+" -> arith_sum *)
(*   | "-" -> arith_sub *)
(*   | "/" -> arith_div *)
(*   | "*" -> arith_mul *)
(*   | "%" -> arith_mod *)
(*   | "&" -> bitwise_and *)
(*   | "|" -> bitwise_or *)
(*   | "^" -> bitwise_xor *)
(*   | "<<" -> bitwise_shiftl *)
(*   | ">>" -> bitwise_shiftr *)
(*   | ">>>" -> bitwise_zfshiftr *)
(*   | "<" -> arith_lt *)
(*   | "<=" -> arith_le *)
(*   | ">" -> arith_gt *)
(*   | ">=" -> arith_ge *)
(*   | "stx=" -> stx_eq *)
(*   | "abs=" -> abs_eq *)
(*   | "hasProperty" -> has_property *)
(*   | "hasOwnProperty" -> has_own_property *)
(*   | "string+" -> string_plus *)
(*   | "string<" -> string_lessthan *)
(*   | "base" -> get_base *)
(*   | "char-at" -> char_at *)
(*   | "locale-compare" -> locale_compare *)
(*   | "pow" -> pow *)
(*   | "to-fixed" -> to_fixed *)
(*   | "isAccessor" -> is_accessor *)
(*   | _ -> failwith ("no implementation of binary operator: " ^ op) *)
