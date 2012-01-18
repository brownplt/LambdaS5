open Prelude
open Ljs_syntax
open Ljs_sym_values

let undef = Undefined
let null = Null
let str s = String s
let num f = Num f

exception PrimError of string

let bool b = match b with
  | true -> True
  | false -> False

let to_int store v = match v with
  | Num x -> int_of_float x
  | _ -> raise (PrimError ("expected number, got " ^ Ljs_sym_pretty.to_string v store))

let typeof store v = (str begin match v with
  | Undefined -> "undefined"
  | Null -> "null"
  | String _ -> "string"
  | Num _ -> "number"
  | True 
  | False -> "boolean"
  | ObjCell o -> begin match (Store.lookup o store) with
    | ObjLit ({ code = Some cexp }, _) -> "function"
    | ObjLit _ -> "object"
    | Value _ -> failwith "[delta] Somehow storing a Value through an ObjCell"
  end
  | Closure _ -> "lambda"
  | VarCell _ -> failwith "[delta] typeof got a variable"
  | Sym _ -> failwith "prim got a symbolic exp"
end, store)

let surface_typeof store v = begin match v with
  | Closure _ -> raise (PrimError "surface_typeof got lambda")
  | Null -> (str "object", store)
  | _ -> typeof store v
end
  
let is_primitive store v = match v with
  | Undefined 
  | Null
  | String _
  | Num _
  | True | False -> (True, store)
  | Sym _ -> failwith "prim got a symbolic exp"
  | _ -> (False, store)

let float_str store n = 
  let s = 
    if n == nan then "NaN"
    else
      if n == infinity then "Infinity"
      else if n == neg_infinity then "-Infinity"
      else
        if float_of_int (int_of_float n) = n
        then string_of_int (int_of_float n) 
        else string_of_float n
  in (s, store)

let prim_to_str store v = 
  let s = str begin match v with
    | Undefined -> "undefined"
    | Null -> "null"
    | String s -> s
    | Num n -> 
      let (fs, _) = float_str store n in (* the new store is irrelevant here *)
      let fslen = String.length fs in
      if String.get fs (fslen - 1) = '.' 
      then String.sub fs 0 (fslen - 1) 
      else
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
        else fs
    | True -> "true"
    | False -> "false"
    | Sym _ -> failwith "prim got a symbolic exp"
    | _ -> raise (PrimError "prim_to_num")
  end in
  (s, store)

let strlen store s = match s with
  | String s -> (Num (float_of_int (String.length s)), store)
  | Sym _ -> failwith "prim got a symbolic exp"
  | _ -> raise (PrimError "strlen")

(* Section 9.3, excluding objects *)
let prim_to_num store v = (num begin match v with
  | Undefined -> nan 
  | Null -> 0.0
  | True -> 1.0
  | False -> 0.0
  | Num x -> x
  | String "" -> 0.0
  | String s -> begin try float_of_string s
    with Failure _ -> nan end
  | Sym _ -> failwith "prim got a symbolic exp"
  | _ -> raise (PrimError "prim_to_num")
end, store)
  
let prim_to_bool store v = (bool begin match v with
  | True -> true
  | False -> false
  | Undefined -> false
  | Null -> false
  | Num x -> not (x == nan || x = 0.0 || x = -0.0)
  | String s -> not (String.length s = 0)
  | Sym _ -> failwith "prim got a symbolic exp"
  | _ -> true
end, store)

let is_callable store obj = (bool begin match obj with
  | ObjCell o -> begin match (Store.lookup o store) with
    | ObjLit ({ code = Some (Closure c); }, _) -> true
    | ObjLit ({ code = Some (Sym _); }, _) -> failwith "prim got a symbolic exp"
    | ObjLit _ -> false
    | Value _ -> failwith "[delta] Somehow storing a Value through an ObjCell"
  end
  | Sym _ -> failwith "prim got a symbolic exp"
  | _ -> false
end, store)

let print store v = 
  let ret = match v with
    | String s -> 
      printf "%S\n%!" s; Undefined
    | Num n -> let s = string_of_float n in printf "%S\n" s; Undefined
    | Sym _ -> failwith "prim got a symbolic exp"
    | _ -> failwith ("[interp] Print received non-string: " ^ Ljs_sym_pretty.to_string v store)
  in (ret, store)

let is_extensible store obj = (begin
  match obj with
  | ObjCell o -> begin match Store.lookup o store with
    | ObjLit ({ extensible = true; }, _) -> True
    | ObjLit _ -> False
    | Value _ -> failwith "[delta] Somehow storing a Value through an ObjCell"
  end
  | Sym _ -> failwith "prim got a symbolic exp"
  | _ -> raise (PrimError "is-extensible")
end, store)
  
let prevent_extensions store obj = match obj with
  | ObjCell o -> begin
    match Store.lookup o store with
    | ObjLit (attrs, props) ->
      let newO = ObjLit ({attrs with extensible = false}, props) in
      (obj, Store.update o newO store)
    | Value _ -> failwith "[delta] Somehow storing a Value through an ObjCell"
    end
  | Sym _ -> failwith "prim got a symbolic exp"
  | _ -> raise (PrimError "prevent-extensions")
    
let get_code store obj = (begin
  match obj with
  | ObjCell o -> begin match Store.lookup o store with
    | ObjLit ({ code = Some v; }, _) -> v
    | ObjLit ({ code = None; }, _) -> Null
    | Value _ -> failwith "[delta] Somehow storing a Value through an ObjCell"
  end
  | Sym _ -> failwith "prim got a symbolic exp"
  | _ -> raise (PrimError "get-code")
end, store)

let get_proto store obj = (begin
  match obj with
  | ObjCell o -> begin match Store.lookup o store with 
    | ObjLit ({ proto = pvalue; }, _) -> pvalue
    | Value _ -> failwith "[delta] Somehow storing a Value through an ObjCell"
  end
  | Sym _ -> failwith "prim got a symbolic exp"
  | v -> raise (PrimError ("get-proto got: " ^ Ljs_sym_pretty.to_string v store))
end, store)

let get_primval store obj = (begin 
  match obj with
  | ObjCell o -> begin match Store.lookup o store with
    | ObjLit ({ primval = Some v; }, _) -> v
    | ObjLit _ -> raise (PrimError "get-primval on an object with no prim val")
    | Value _ -> failwith "[delta] Somehow storing a Value through an ObjCell"
  end
  | Sym _ -> failwith "prim got a symbolic exp"
  | _ -> raise (PrimError "get-primval")
end , store)

let get_class store obj = (begin
  match obj with
  | ObjCell o -> begin match Store.lookup o store with
    | ObjLit ({ klass = s; }, _) -> String (s)
    | Value _ -> failwith "[delta] Somehow storing a Value through an ObjCell"
  end
  | Sym _ -> failwith "prim got a symbolic exp"
  | _ -> raise (PrimError "get-class")
end, store)

(* All the enumerable property names of an object *)
let rec get_property_names store obj = match obj with
  | ObjCell o ->
    let protos = obj::(all_protos store obj) in
    let folder o set = begin match o with
      | ObjCell o' -> begin
	match Store.lookup o' store with
        | ObjLit (attrs, props) ->
	  IdMap.fold (fun k v s -> 
	    if enum v then IdSet.add k s else s) props set
        | Value _ -> failwith "[delta] Somehow storing a Value through an ObjCell"
      end
      | _ -> set (* non-object prototypes don't contribute *) 
    end in
    let name_set = List.fold_right folder protos IdSet.empty in
    let name_list= IdSet.elements name_set in
    let prop_folder num name props = 
      IdMap.add (string_of_int num) 
        (Data ({ value = String name; writable = false; }, false, false))
        props in
    let name_props = List.fold_right2 prop_folder 
      (iota (List.length name_list))
      name_list
      IdMap.empty in
    let (newLoc, store') = Store.alloc (ObjLit (d_attrsv, name_props)) store in
    (ObjCell newLoc, store')
  | Sym _ -> failwith "prim got a symbolic exp"
  | _ -> raise (PrimError "get-property-names")

and all_protos store o = 
  match o with
  | ObjCell c -> begin match Store.lookup c store with 
    | ObjLit ({ proto = pvalue; }, _) -> pvalue::(all_protos store pvalue)
    | Value _ -> failwith "[delta] Somehow storing a Value through an ObjCell"
  end
  | Sym _ -> failwith "prim got a symbolic exp"
  | _ -> []

and enum prop = match prop with
  | Accessor (_, b, _)
  | Data (_, b, _) -> b

let get_own_property_names store obj = match obj with
  | ObjCell o -> begin
    match Store.lookup o store with
    | ObjLit (_, props) ->
      let add_name n x m = 
        IdMap.add (string_of_int x) 
          (Data ({ value = String n; writable = false; }, false, false)) 
          m in
      let namelist = IdMap.fold (fun k v l -> (k :: l)) props [] in
      let props = 
        List.fold_right2 add_name namelist (iota (List.length namelist)) IdMap.empty
      in
      let d = (float_of_int (List.length namelist)) in
      let final_props = 
        IdMap.add "length" 
          (Data ({ value = Num d; writable = false; }, false, false))
          props 
      in
      let (newLoc, store') = Store.alloc (ObjLit (d_attrsv, final_props)) store in
      (ObjCell newLoc, store')
    | Value _ -> failwith "[delta] Somehow storing a Value through an ObjCell"
  end
  | Sym _ -> failwith "prim got a symbolic exp"
  | _ -> raise (PrimError "own-property-names")

(* Implement this here because there's no need to expose the class
   property outside of the delta function *)
let object_to_string store obj = (begin
  match obj with
  | ObjCell o -> begin match Store.lookup o store with
    | ObjLit ({ klass = s }, _) -> str ("[object " ^ s ^ "]")
    | Value _ -> failwith "[delta] Somehow storing a Value through an ObjCell"
  end
  | Sym _ -> failwith "prim got a symbolic exp"
  | _ -> raise (PrimError "object-to-string, wasn't given object")
end, store)

let is_array store obj = (begin
  match obj with
  | ObjCell o -> begin match Store.lookup o store with
    | ObjLit ({ klass = "Array"; }, _) -> True
    | ObjLit _ -> False
    | Value _ -> failwith "[delta] Somehow storing a Value through an ObjCell"
  end
  | Sym _ -> failwith "prim got a symbolic exp"
  | _ -> raise (PrimError "is-array")
end, store)


let to_int32 store v = (begin
  match v with
  | Num d -> Num (float_of_int (int_of_float d))
  | Sym _ -> failwith "prim got a symbolic exp"
  | _ -> raise (PrimError "to-int")
end, store)

let nnot store e = (begin
  match e with
  | Undefined -> True
  | Null -> True
  | True -> False
  | False -> True
  | Num d -> if (d = 0.) || (d <> d) then True else False
  | String s -> if s = "" then True else False
  | ObjCell _ -> False
  | Closure _ -> False
  | Sym _ -> failwith "prim got a symbolic exp"
  | _ -> failwith ("Fatal: ! operator on " ^ (Ljs_sym_pretty.to_string e store))
end, store)

let void store v = (Undefined, store)

let floor' store = function Num d -> (num (floor d), store)
  | Sym _ -> failwith "prim got a symbolic exp"
  | _ -> raise (PrimError "floor")

let ceil' store = function Num d -> (num (ceil d), store)
  | Sym _ -> failwith "prim got a symbolic exp"
  | _ -> raise (PrimError "ceil")

let absolute store = function Num d -> (num (abs_float d), store)
  | Sym _ -> failwith "prim got a symbolic exp"
  | _ -> raise (PrimError "abs")

let log' store = function Num d -> (num (log d ), store)
  | Sym _ -> failwith "prim got a symbolic exp"
  | _ -> raise (PrimError "log")

let ascii_ntoc store n = match n with
  | Num d -> (str (String.make 1 (Char.chr (int_of_float d))), store)
  | Sym _ -> failwith "prim got a symbolic exp"
  | _ -> raise (PrimError "ascii_ntoc")

let ascii_cton store c = match c with
  | String s -> (Num (float_of_int (Char.code (String.get s 0))), store)
  | Sym _ -> failwith "prim got a symbolic exp"
  | _ -> raise (PrimError "ascii_cton")

let to_lower store = function
  | String s -> (String (String.lowercase s), store)
  | Sym _ -> failwith "prim got a symbolic exp"
  | _ -> raise (PrimError "to_lower")

let to_upper store = function
  | String s -> (String (String.uppercase s), store)
  | Sym _ -> failwith "prim got a symbolic exp"
  | _ -> raise (PrimError "to_lower")

let bnot store = function
  | Num d -> (Num (float_of_int (lnot (int_of_float d))), store)
  | Sym _ -> failwith "prim got a symbolic exp"
  | _ -> raise (PrimError "bnot")

let sine store = function
  | Num d -> (Num (sin d), store)
  | Sym _ -> failwith "prim got a symbolic exp"
  | _ -> raise (PrimError "sin")

let numstr store = function
  | String s -> (Num (try float_of_string s with Failure _ -> nan), store)
  | Sym _ -> failwith "prim got a symbolic exp"
  | _ -> raise (PrimError "numstr")

let op1 (op : string) (store : cell Store.t) : value -> value * cell Store.t = match op with
  | "typeof" -> typeof store
  | "surface-typeof" -> surface_typeof store
  | "primitive?" -> is_primitive store
  | "prim->str" -> prim_to_str store
  | "prim->num" -> prim_to_num store
  | "prim->bool" -> prim_to_bool store
  | "is-callable" -> is_callable store
  | "is-extensible" -> is_extensible store
  | "prevent-extensions" -> prevent_extensions store
  | "print" -> print store
  | "get-proto" -> get_proto store
  | "get-primval" -> get_primval store
  | "get-class" -> get_class store
  | "get-code" -> get_code store
  | "property-names" -> get_property_names store
  | "own-property-names" -> get_own_property_names store
  | "object-to-string" -> object_to_string store
  | "strlen" -> strlen store
  | "is-array" -> is_array store
  | "to-int32" -> to_int32 store
  | "!" -> nnot store
  | "void" -> void store
  | "floor" -> floor' store
  | "ceil" -> ceil' store
  | "abs" -> absolute store
  | "log" -> log' store
  | "ascii_ntoc" -> ascii_ntoc store
  | "ascii_cton" -> ascii_cton store
  | "to-lower" -> to_lower store
  | "to-upper" -> to_upper store
  | "~" -> bnot store
  | "sin" -> sine store
  | "numstr->num" -> numstr store
  | _ -> failwith ("no implementation of unary operator: " ^ op)
let typeofOp1 op = match op with
  | "NOT" -> (TBool, TBool)
  | "typeof" -> (TAny, TString)
  | "surface-typeof" -> (TAny, TString)
  | "primitive?" -> (TAny, TBool)
  | "prim->str" -> (TAny, TString)
  | "prim->num" -> (TAny, TNum)
  | "prim->bool" -> (TAny, TBool)
  | "is-callable" -> (TAny, TBool)
  | "is-extensible" -> (TObj, TBool)
  | "prevent-extensions" -> (TObj, TObj)
  | "print" -> (TAny, TUndef)
  | "get-proto" -> (TObj, TAny)
  | "get-primval" -> (TObj, TAny)
  | "get-class" -> (TObj, TString)
  | "get-code" -> (TObj, TAny)
  | "property-names" -> (TObj, TObj)
  | "own-property-names" -> (TObj, TObj)
  | "object-to-string" -> (TObj, TString)
  | "strlen" -> (TString, TNum)
  | "is-array" -> (TAny, TBool)
  | "to-int32" -> (TAny, TNum)
  | "!" -> (TAny, TBool)
  | "void" -> (TAny, TUndef)
  | "floor" -> (TNum, TNum)
  | "ceil" -> (TNum, TNum)
  | "abs" -> (TNum, TNum)
  | "log" -> (TNum, TNum)
  | "ascii_ntoc" -> (TNum, TString)
  | "ascii_cton" -> (TString, TNum)
  | "to-lower" -> (TString, TString)
  | "to-upper" -> (TString, TString)
  | "~" -> (TNum, TNum)
  | "sin" -> (TNum, TNum)
  | "numstr->num" -> (TString, TNum)
  | _ -> failwith ("no implementation of unary operator: " ^ op)


let arith store s i_op f_op v1 v2 = match v1, v2 with
  | Num x, Num y -> (Num (f_op x y), store)
  | v1, v2 -> raise (PrimError ("arithmetic operator: " ^ s ^ " got non-numbers: " ^
                                   (Ljs_sym_pretty.to_string v1 store) ^ ", " ^ 
                                   (Ljs_sym_pretty.to_string v2 store) ^
                                   "perhaps something wasn't desugared fully?"))

let arith_sum store = arith store "+" (+) (+.)

let arith_sub store = arith store "-" (-) (-.)

(* OCaml syntax failure! Operator section syntax lexes as a comment. *)
let arith_mul store = arith store "*" (fun m n -> m * n) (fun x y -> x *. y)

let arith_div store x y = try arith store "/" (/) (/.) x y
  with Division_by_zero -> ((Num infinity), store)

let arith_mod store x y = try arith store "mod" (mod) mod_float x y
  with Division_by_zero -> (Num nan, store)

let arith_lt store x y = (bool (x < y), store)

let arith_le store x y = (bool (x <= y), store)

let arith_gt store x y = (bool (x > y), store)

let arith_ge store x y = (bool (x >= y), store)

let bitwise_and store v1 v2 = (Num (float_of_int ((to_int store v1) land (to_int store v2))), store)

let bitwise_or store v1 v2 = (Num (float_of_int ((to_int store v1) lor (to_int store v2))), store)

let bitwise_xor store v1 v2 = (Num (float_of_int ((to_int store v1) lxor (to_int store v2))), store)

let bitwise_shiftl store v1 v2 = (Num (float_of_int ((to_int store v1) lsl (to_int store v2))), store)

let bitwise_zfshiftr store v1 v2 = (Num (float_of_int ((to_int store v1) lsr (to_int store v2))), store)

let bitwise_shiftr store v1 v2 = (Num (float_of_int ((to_int store v1) asr (to_int store v2))), store)

let string_plus store v1 v2 = match v1, v2 with
  | String s1, String s2 ->
    (String (s1 ^ s2), store)
  | Sym _, _ 
  | _, Sym _ -> failwith "prim got a symbolic exp"
  | _ -> raise (PrimError "string concatenation")

let string_lessthan store v1 v2 = match v1, v2 with
  | String s1, String s2 -> (bool (s1 < s2), store)
  | Sym _, _ 
  | _, Sym _ -> failwith "prim got a symbolic exp"
  | _ -> raise (PrimError "string less than")

let stx_eq store v1 v2 = (bool begin match v1, v2 with
  | Num x1, Num x2 -> x1 = x2
  | String x1, String x2 -> x1 = x2
  | Undefined, Undefined -> true
  | Null, Null -> true
  | True, True -> true
  | False, False -> true
  | Sym _, _ 
  | _, Sym _ -> failwith "prim got a symbolic exp"
  | _ -> v1 == v2 (* otherwise, pointer equality *)
end, store)

(* Algorithm 11.9.3, steps 1 through 19. Steps 20 and 21 are desugared to
   access the heap. *)
let abs_eq store v1 v2 = (bool begin
  if v1 = v2 then (* works correctly on floating point values *)
    true
  else match v1, v2 with
  | Null, Undefined
  | Undefined, Null -> true
  | String s, Num x
  | Num x, String s ->
    (try x = float_of_string s with Failure _ -> false)
  | Num x, True | True, Num x -> x = 1.0
  | Num x, False | False, Num x -> x = 0.0
  | Sym _, _ 
  | _, Sym _ -> failwith "prim got a symbolic exp"
  | _ -> false
(* TODO: are these all the cases? *)
end, store)

let rec has_property store obj field = match obj, field with
  | ObjCell o, String s -> begin match Store.lookup o store, s with
    | ObjLit ({ proto = pvalue; }, props), s ->
      if (IdMap.mem s props) then (bool true, store)
      else has_property store pvalue field
    | Value _, _ -> failwith "[delta] Somehow storing a Value through an ObjCell"
  end
  | Sym _, _ 
  | _, Sym _ -> failwith "prim got a symbolic exp"
  | _ -> (bool false, store)

let has_own_property store obj field = match obj, field with
  | ObjCell o, String s -> begin
    match Store.lookup o store with
    | ObjLit (attrs, props) -> (bool (IdMap.mem s props), store)
    | Value _ -> failwith "[delta] Somehow storing a Value through an ObjCell"
  end
  | ObjCell o, _ -> raise (PrimError "has-own-property: field not a string")
  | _, String s -> raise (PrimError ("has-own-property: obj not an object for field " ^ s))
  | Sym _, _ 
  | _, Sym _ -> failwith "prim got a symbolic exp"
  | _ -> raise (PrimError "has-own-property: neither an object nor a string")

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

let get_base store n r = match n, r with
  | Num x, Num y -> 
    let result = base (abs_float x) (abs_float y) in
    (str (if x < 0.0 then "-" ^ result else result), store)
  | Sym _, _ 
  | _, Sym _ -> failwith "prim got a symbolic exp"
  | _ -> raise (PrimError "base got non-numbers")

let char_at store a b  = match a, b with
  | String s, Num n ->
    (String (String.make 1 (String.get s (int_of_float n))), store)
  | Sym _, _ 
  | _, Sym _ -> failwith "prim got a symbolic exp"
  | _ -> raise (PrimError "char_at didn't get a string and a number")

let locale_compare store a b = match a, b with
  | String r, String s ->
    (Num (float_of_int (String.compare r s)), store)
  | Sym _, _ 
  | _, Sym _ -> failwith "prim got a symbolic exp"
  | _ -> raise (PrimError "locale_compare didn't get 2 strings")

let pow store a b = match a, b with
  | Num base, Num exp -> (Num (base ** exp), store)
  | Sym _, _ 
  | _, Sym _ -> failwith "prim got a symbolic exp"
  | _ -> raise (PrimError "pow didn't get 2 numbers")

let to_fixed store a b = (begin
  match a, b with
  | Num x, Num f -> 
    let s = string_of_float x
    and fint = int_of_float f in
    if fint = 0 
    then String (string_of_int (int_of_float x)) 
    else let dot_index = String.index s '.'
    and len = String.length s in
         let prefix_chars = dot_index in
         let decimal_chars = len - (prefix_chars + 1) in
         if decimal_chars = fint then String s
         else if decimal_chars > fint
         then let fixed_s = String.sub s 0 (fint - prefix_chars) in
              String (fixed_s)
         else let suffix = String.make (fint - decimal_chars) '0' in
              String (s ^ suffix)
  | Sym _, _ 
  | _, Sym _ -> failwith "prim got a symbolic exp"
  | _ -> raise (PrimError "to-fixed didn't get 2 numbers")
end, store)

let rec is_accessor store a b = match a, b with
  | ObjCell o, String s -> begin
    match Store.lookup o store with
    | ObjLit (attrs, props) -> 
      if IdMap.mem s props
      then let prop = IdMap.find s props in
           match prop with
           | Data _ -> (False, store)
           | Accessor _ -> (True, store)
      else let pr = match attrs with { proto = p } -> p in
           is_accessor store pr b
    | Value _ -> failwith "[delta] Somehow storing a Value through an ObjCell"
  end
  | Null, String s -> raise (PrimError "isAccessor topped out")
  | Sym _, _ 
  | _, Sym _ -> failwith "prim got a symbolic exp"
  | _ -> raise (PrimError "isAccessor")

let op2 store op = match op with
  | "+" -> arith_sum store
  | "-" -> arith_sub store
  | "/" -> arith_div store
  | "*" -> arith_mul store
  | "%" -> arith_mod store
  | "&" -> bitwise_and store
  | "|" -> bitwise_or store
  | "^" -> bitwise_xor store
  | "<<" -> bitwise_shiftl store
  | ">>" -> bitwise_shiftr store
  | ">>>" -> bitwise_zfshiftr store
  | "<" -> arith_lt store
  | "<=" -> arith_le store
  | ">" -> arith_gt store
  | ">=" -> arith_ge store
  | "stx=" -> stx_eq store
  | "abs=" -> abs_eq store
  | "hasProperty" -> has_property store
  | "hasOwnProperty" -> has_own_property store
  | "string+" -> string_plus store
  | "string<" -> string_lessthan store
  | "base" -> get_base store
  | "char-at" -> char_at store
  | "locale-compare" -> locale_compare store
  | "pow" -> pow store
  | "to-fixed" -> to_fixed store
  | "isAccessor" -> is_accessor store
  | _ -> failwith ("no implementation of binary operator: " ^ op)
let typeofOp2 op = match op with
  | "get_field" -> (TObj, TString, TAny)
  | "+" -> (TNum, TNum, TNum)
  | "-" -> (TNum, TNum, TNum)
  | "/" -> (TNum, TNum, TNum)
  | "*" -> (TNum, TNum, TNum)
  | "%" -> (TNum, TNum, TNum)
  | "&" -> (TNum, TNum, TNum)
  | "|" -> (TNum, TNum, TNum)
  | "^" -> (TNum, TNum, TNum)
  | "<<" -> (TNum, TNum, TNum)
  | ">>" -> (TNum, TNum, TNum)
  | ">>>" -> (TNum, TNum, TNum)
  | "<" -> (TNum, TNum, TBool)
  | "<=" -> (TNum, TNum, TBool)
  | ">" -> (TNum, TNum, TBool)
  | ">=" -> (TNum, TNum, TBool)
  | "stx=" -> (TAny, TAny, TBool)
  | "abs=" -> (TAny, TAny, TBool)
  | "hasProperty" -> (TObj, TString, TBool)
  | "hasOwnProperty" -> (TObj, TString, TBool)
  | "string+" -> (TString, TString, TString)
  | "string<" -> (TString, TString, TBool)
  | "base" -> (TNum, TNum, TString)
  | "char-at" -> (TString, TNum, TString)
  | "locale-compare" -> (TString, TString, TNum)
  | "pow" -> (TNum, TNum, TNum)
  | "to-fixed" -> (TNum, TNum, TString)
  | "isAccessor" -> (TObj, TString, TBool)
  | _ -> failwith ("no implementation of binary operator: " ^ op)
