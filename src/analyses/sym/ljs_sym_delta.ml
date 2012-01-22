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

let to_int ctx v = match v with
  | Num x -> int_of_float x
  | _ -> raise (PrimError ("expected number, got " ^ Ljs_sym_pretty.to_string v ctx.store))

let typeof ctx v = add_const_str ctx (begin match v with
  | Undefined -> "undefined"
  | Null -> "null"
  | String _ -> "string"
  | Num _ -> "number"
  | True 
  | False -> "boolean"
  | ObjCell o -> begin match (sto_lookup o ctx) with
    | ObjLit ({ code = Some cexp }, _), _ -> "function"
    | ObjLit _, _ -> "object"
    | Value _, _ -> failwith "[delta] Somehow storing a Value through an ObjCell"
  end
  | Closure _ -> "lambda"
  | VarCell _ -> failwith "[delta] typeof got a variable"
  | Sym _ -> failwith "prim got a symbolic exp"
end)

let surface_typeof ctx v = begin match v with
  | Closure _ -> raise (PrimError "surface_typeof got lambda")
  | Null -> add_const_str ctx "object"
  | _ -> typeof ctx v
end
  
let is_primitive ctx v = match v with
  | Undefined 
  | Null
  | String _
  | Num _
  | True | False -> (True, ctx)
  | Sym _ -> failwith "prim got a symbolic exp"
  | _ -> (False, ctx)

let float_str ctx n = 
  let s = 
    if n == nan then "NaN"
    else
      if n == infinity then "Infinity"
      else if n == neg_infinity then "-Infinity"
      else
        if float_of_int (int_of_float n) = n
        then string_of_int (int_of_float n) 
        else string_of_float n
  in (s, ctx)

let prim_to_str ctx v = 
  add_const_str ctx begin match v with
  | Undefined -> "undefined"
  | Null -> "null"
  | String s -> s
  | Num n -> 
    let (fs, _) = float_str ctx n in (* the new store is irrelevant here *)
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
  end 

let strlen ctx s = match s with
  | String s -> (Num (float_of_int (String.length s)), ctx)
  | Sym _ -> failwith "prim got a symbolic exp"
  | _ -> raise (PrimError "strlen")

(* Section 9.3, excluding objects *)
let prim_to_num ctx v = (num begin match v with
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
end, ctx)
  
let prim_to_bool ctx v = (bool begin match v with
  | True -> true
  | False -> false
  | Undefined -> false
  | Null -> false
  | Num x -> not (x == nan || x = 0.0 || x = -0.0)
  | String s -> not (String.length s = 0)
  | Sym _ -> failwith "prim got a symbolic exp"
  | _ -> true
end, ctx)

let is_callable ctx obj = (bool begin match obj with
  | ObjCell o -> begin match (sto_lookup o ctx) with
    | ObjLit ({ code = Some (Closure c); }, _), _ -> true
    | ObjLit ({ code = Some (Sym _); }, _), _ -> failwith "prim got a symbolic exp"
    | ObjLit _, _ -> false
    | Value _, _ -> failwith "[delta] Somehow storing a Value through an ObjCell"
  end
  | Sym _ -> failwith "prim got a symbolic exp"
  | _ -> false
end, ctx)

let print ctx v = 
  let ret = match v with
    | String s -> 
      printf "%S\n%!" s; Undefined
    | Num n -> let s = string_of_float n in printf "%S\n" s; Undefined
    | Sym _ -> failwith "prim got a symbolic exp"
    | _ -> failwith ("[interp] Print received non-string: " ^ Ljs_sym_pretty.to_string v ctx.store)
  in (ret, ctx)

let is_extensible ctx obj = (begin
  match obj with
  | ObjCell o -> begin match sto_lookup o ctx with
    | ObjLit ({ extensible = true; }, _), _ -> True
    | ObjLit _, _ -> False
    | Value _, _ -> failwith "[delta] Somehow storing a Value through an ObjCell"
  end
  | Sym _ -> failwith "prim got a symbolic exp"
  | _ -> raise (PrimError "is-extensible")
end, ctx)
  
let prevent_extensions ctx obj = match obj with
  | ObjCell o -> begin
    match sto_lookup o ctx with
    | ObjLit (attrs, props), ctx ->
      let newO = ObjLit ({attrs with extensible = false}, props) in
      (obj, sto_update o newO ctx )
    | Value _, _ -> failwith "[delta] Somehow storing a Value through an ObjCell"
    end
  | Sym _ -> failwith "prim got a symbolic exp"
  | _ -> raise (PrimError "prevent-extensions")
    
let get_code ctx obj = (begin
  match obj with
  | ObjCell o -> begin match sto_lookup o ctx with
    | ObjLit ({ code = Some v; }, _), _ -> v
    | ObjLit ({ code = None; }, _), _ -> Null
    | Value _, _ -> failwith "[delta] Somehow storing a Value through an ObjCell"
  end
  | Sym _ -> failwith "prim got a symbolic exp"
  | _ -> raise (PrimError "get-code")
end, ctx)

let get_proto ctx obj = (begin
  match obj with
  | ObjCell o -> begin match sto_lookup o ctx with 
    | ObjLit ({ proto = pvalue; }, _), _ -> pvalue
    | Value _, _ -> failwith "[delta] Somehow storing a Value through an ObjCell"
  end
  | Sym _ -> failwith "prim got a symbolic exp"
  | v -> raise (PrimError ("get-proto got: " ^ Ljs_sym_pretty.to_string v ctx.store))
end, ctx)

let get_primval ctx obj = (begin 
  match obj with
  | ObjCell o -> begin match sto_lookup o ctx with
    | ObjLit ({ primval = Some v; }, _), _ -> v
    | ObjLit _, _ -> raise (PrimError "get-primval on an object with no prim val")
    | Value _, _ -> failwith "[delta] Somehow storing a Value through an ObjCell"
  end
  | Sym _ -> failwith "prim got a symbolic exp"
  | _ -> raise (PrimError "get-primval")
end , ctx)

let get_class ctx obj = (begin
  match obj with
  | ObjCell o -> begin match sto_lookup o ctx with
    | ObjLit ({ klass = s; }, _), _ -> String (s)
    | Value _, _ -> failwith "[delta] Somehow storing a Value through an ObjCell"
  end
  | Sym _ -> failwith "prim got a symbolic exp"
  | _ -> raise (PrimError "get-class")
end, ctx)

(* All the enumerable property names of an object *)
let rec get_property_names ctx obj = match obj with
  | ObjCell o ->
    let protos = obj::(all_protos ctx obj) in
    let folder o set = begin match o with
      | ObjCell o' -> begin
	match sto_lookup o' ctx with
        | ObjLit (attrs, props), _ ->
	  IdMap.fold (fun k v s -> 
	    if enum v then IdSet.add k s else s) props set
        | Value _, _ -> failwith "[delta] Somehow storing a Value through an ObjCell"
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
    let (newLoc, ctx') = sto_alloc (ObjLit (d_attrsv, name_props)) ctx in
    (ObjCell newLoc, ctx')
  | Sym _ -> failwith "prim got a symbolic exp"
  | _ -> raise (PrimError "get-property-names")

and all_protos ctx o = 
  match o with
  | ObjCell c -> begin match sto_lookup c ctx with 
    | ObjLit ({ proto = pvalue; }, _), ctx -> pvalue::(all_protos ctx pvalue)
    | Value _, _ -> failwith "[delta] Somehow storing a Value through an ObjCell"
  end
  | Sym _ -> failwith "prim got a symbolic exp"
  | _ -> []

and enum prop = match prop with
  | Accessor (_, b, _)
  | Data (_, b, _) -> b

let get_own_property_names ctx obj = match obj with
  | ObjCell o -> begin
    match sto_lookup o ctx with
    | ObjLit (_, props), ctx ->
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
      let (newLoc, ctx') = sto_alloc (ObjLit (d_attrsv, final_props)) ctx in
      (ObjCell newLoc, ctx')
    | Value _, _ -> failwith "[delta] Somehow storing a Value through an ObjCell"
  end
  | Sym _ -> failwith "prim got a symbolic exp"
  | _ -> raise (PrimError "own-property-names")

(* Implement this here because there's no need to expose the class
   property outside of the delta function *)
let object_to_string ctx obj = add_const_str ctx begin
  match obj with
  | ObjCell o -> begin match sto_lookup o ctx with
    | ObjLit ({ klass = s }, _), _ -> "[object " ^ s ^ "]"
    | Value _, _ -> failwith "[delta] Somehow storing a Value through an ObjCell"
  end
  | Sym _ -> failwith "prim got a symbolic exp"
  | _ -> raise (PrimError "object-to-string, wasn't given object")
end

let is_array ctx obj = (begin
  match obj with
  | ObjCell o -> begin match sto_lookup o ctx with
    | ObjLit ({ klass = "Array"; }, _), _ -> True
    | ObjLit _, _ -> False
    | Value _, _ -> failwith "[delta] Somehow storing a Value through an ObjCell"
  end
  | Sym _ -> failwith "prim got a symbolic exp"
  | _ -> raise (PrimError "is-array")
end, ctx)


let to_int32 ctx v = (begin
  match v with
  | Num d -> Num (float_of_int (int_of_float d))
  | Sym _ -> failwith "prim got a symbolic exp"
  | _ -> raise (PrimError "to-int")
end, ctx)

let nnot ctx e = (begin
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
  | _ -> failwith ("Fatal: ! operator on " ^ (Ljs_sym_pretty.to_string e ctx.store))
end, ctx)

let void ctx v = (Undefined, ctx)

let floor' ctx = function Num d -> (num (floor d), ctx)
  | Sym _ -> failwith "prim got a symbolic exp"
  | _ -> raise (PrimError "floor")

let ceil' ctx = function Num d -> (num (ceil d), ctx)
  | Sym _ -> failwith "prim got a symbolic exp"
  | _ -> raise (PrimError "ceil")

let absolute ctx = function Num d -> (num (abs_float d), ctx)
  | Sym _ -> failwith "prim got a symbolic exp"
  | _ -> raise (PrimError "abs")

let log' ctx = function Num d -> (num (log d ), ctx)
  | Sym _ -> failwith "prim got a symbolic exp"
  | _ -> raise (PrimError "log")

let ascii_ntoc ctx n = match n with
  | Num d -> add_const_str ctx (String.make 1 (Char.chr (int_of_float d)))
  | Sym _ -> failwith "prim got a symbolic exp"
  | _ -> raise (PrimError "ascii_ntoc")

let ascii_cton ctx c = match c with
  | String s -> (Num (float_of_int (Char.code (String.get s 0))), ctx)
  | Sym _ -> failwith "prim got a symbolic exp"
  | _ -> raise (PrimError "ascii_cton")

let to_lower ctx = function
  | String s -> (String (String.lowercase s), ctx)
  | Sym _ -> failwith "prim got a symbolic exp"
  | _ -> raise (PrimError "to_lower")

let to_upper ctx = function
  | String s -> (String (String.uppercase s), ctx)
  | Sym _ -> failwith "prim got a symbolic exp"
  | _ -> raise (PrimError "to_lower")

let bnot ctx = function
  | Num d -> (Num (float_of_int (lnot (int_of_float d))), ctx)
  | Sym _ -> failwith "prim got a symbolic exp"
  | _ -> raise (PrimError "bnot")

let sine ctx = function
  | Num d -> (Num (sin d), ctx)
  | Sym _ -> failwith "prim got a symbolic exp"
  | _ -> raise (PrimError "sin")

let numstr ctx = function
  | String s -> (Num (try float_of_string s with Failure _ -> nan), ctx)
  | Sym _ -> failwith "prim got a symbolic exp"
  | _ -> raise (PrimError "numstr")

let op1 ctx op : value -> value * ctx = match op with
  | "typeof" -> typeof ctx
  | "surface-typeof" -> surface_typeof ctx
  | "primitive?" -> is_primitive ctx
  | "prim->str" -> prim_to_str ctx
  | "prim->num" -> prim_to_num ctx
  | "prim->bool" -> prim_to_bool ctx
  | "is-callable" -> is_callable ctx
  | "is-extensible" -> is_extensible ctx
  | "prevent-extensions" -> prevent_extensions ctx
  | "print" -> print ctx
  | "get-proto" -> get_proto ctx
  | "get-primval" -> get_primval ctx
  | "get-class" -> get_class ctx
  | "get-code" -> get_code ctx
  | "property-names" -> get_property_names ctx
  | "own-property-names" -> get_own_property_names ctx
  | "object-to-string" -> object_to_string ctx
  | "strlen" -> strlen ctx
  | "is-array" -> is_array ctx
  | "to-int32" -> to_int32 ctx
  | "!" -> nnot ctx
  | "void" -> void ctx
  | "floor" -> floor' ctx
  | "ceil" -> ceil' ctx
  | "abs" -> absolute ctx
  | "log" -> log' ctx
  | "ascii_ntoc" -> ascii_ntoc ctx
  | "ascii_cton" -> ascii_cton ctx
  | "to-lower" -> to_lower ctx
  | "to-upper" -> to_upper ctx
  | "~" -> bnot ctx
  | "sin" -> sine ctx
  | "numstr->num" -> numstr ctx
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


let arith ctx s i_op f_op v1 v2 = match v1, v2 with
  | Num x, Num y -> (Num (f_op x y), ctx)
  | v1, v2 -> raise (PrimError ("arithmetic operator: " ^ s ^ " got non-numbers: " ^
                                   (Ljs_sym_pretty.to_string v1 ctx.store) ^ ", " ^ 
                                   (Ljs_sym_pretty.to_string v2 ctx.store) ^
                                   "perhaps something wasn't desugared fully?"))

let arith_sum ctx = arith ctx "+" (+) (+.)

let arith_sub ctx = arith ctx "-" (-) (-.)

(* OCaml syntax failure! Operator section syntax lexes as a comment. *)
let arith_mul ctx = arith ctx "*" (fun m n -> m * n) (fun x y -> x *. y)

let arith_div ctx x y = try arith ctx "/" (/) (/.) x y
  with Division_by_zero -> ((Num infinity), ctx)

let arith_mod ctx x y = try arith ctx "mod" (mod) mod_float x y
  with Division_by_zero -> (Num nan, ctx)

let arith_lt ctx x y = (bool (x < y), ctx)

let arith_le ctx x y = (bool (x <= y), ctx)

let arith_gt ctx x y = (bool (x > y), ctx)

let arith_ge ctx x y = (bool (x >= y), ctx)

let bitwise_and ctx v1 v2 = (Num (float_of_int ((to_int ctx v1) land (to_int ctx v2))), ctx)

let bitwise_or ctx v1 v2 = (Num (float_of_int ((to_int ctx v1) lor (to_int ctx v2))), ctx)

let bitwise_xor ctx v1 v2 = (Num (float_of_int ((to_int ctx v1) lxor (to_int ctx v2))), ctx)

let bitwise_shiftl ctx v1 v2 = (Num (float_of_int ((to_int ctx v1) lsl (to_int ctx v2))), ctx)

let bitwise_zfshiftr ctx v1 v2 = (Num (float_of_int ((to_int ctx v1) lsr (to_int ctx v2))), ctx)

let bitwise_shiftr ctx v1 v2 = (Num (float_of_int ((to_int ctx v1) asr (to_int ctx v2))), ctx)

let string_plus ctx v1 v2 = match v1, v2 with
  | String s1, String s2 ->
    (String (s1 ^ s2), ctx)
  | Sym _, _ 
  | _, Sym _ -> failwith "prim got a symbolic exp"
  | _ -> raise (PrimError "string concatenation")

let string_lessthan ctx v1 v2 = match v1, v2 with
  | String s1, String s2 -> (bool (s1 < s2), ctx)
  | Sym _, _ 
  | _, Sym _ -> failwith "prim got a symbolic exp"
  | _ -> raise (PrimError "string less than")

let stx_eq ctx v1 v2 = (bool begin match v1, v2 with
  | Num x1, Num x2 -> x1 = x2
  | String x1, String x2 -> x1 = x2
  | Undefined, Undefined -> true
  | Null, Null -> true
  | True, True -> true
  | False, False -> true
  | Sym _, _ 
  | _, Sym _ -> failwith "prim got a symbolic exp"
  | _ -> v1 == v2 (* otherwise, pointer equality *)
end, ctx)

(* Algorithm 11.9.3, steps 1 through 19. Steps 20 and 21 are desugared to
   access the heap. *)
let abs_eq ctx v1 v2 = (bool begin
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
end, ctx)

let rec has_property ctx obj field = match obj, field with
  | ObjCell o, String s -> begin match sto_lookup o ctx with
    | ObjLit ({ proto = pvalue; }, props), ctx ->
      if (IdMap.mem s props) then (bool true, ctx)
      else has_property ctx pvalue field
    | Value _, _ -> failwith "[delta] Somehow storing a Value through an ObjCell"
  end
  | Sym _, _ 
  | _, Sym _ -> failwith "prim got a symbolic exp"
  | _ -> (bool false, ctx)

let has_own_property ctx obj field = match obj, field with
  | ObjCell o, String s -> begin
    match sto_lookup o ctx with
    | ObjLit (attrs, props), ctx -> (bool (IdMap.mem s props), ctx)
    | Value _, _ -> failwith "[delta] Somehow storing a Value through an ObjCell"
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

let get_base ctx n r = match n, r with
  | Num x, Num y -> 
    let result = base (abs_float x) (abs_float y) in
    add_const_str ctx (if x < 0.0 then "-" ^ result else result)
  | Sym _, _ 
  | _, Sym _ -> failwith "prim got a symbolic exp"
  | _ -> raise (PrimError "base got non-numbers")

let char_at ctx a b  = match a, b with
  | String s, Num n ->
    (String (String.make 1 (String.get s (int_of_float n))), ctx)
  | Sym _, _ 
  | _, Sym _ -> failwith "prim got a symbolic exp"
  | _ -> raise (PrimError "char_at didn't get a string and a number")

let locale_compare ctx a b = match a, b with
  | String r, String s ->
    (Num (float_of_int (String.compare r s)), ctx)
  | Sym _, _ 
  | _, Sym _ -> failwith "prim got a symbolic exp"
  | _ -> raise (PrimError "locale_compare didn't get 2 strings")

let pow ctx a b = match a, b with
  | Num base, Num exp -> (Num (base ** exp), ctx)
  | Sym _, _ 
  | _, Sym _ -> failwith "prim got a symbolic exp"
  | _ -> raise (PrimError "pow didn't get 2 numbers")

let to_fixed ctx a b = (begin
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
end, ctx)

let rec is_accessor ctx a b = match a, b with
  | ObjCell o, String s -> begin
    match sto_lookup o ctx with
    | ObjLit (attrs, props), ctx -> 
      if IdMap.mem s props
      then let prop = IdMap.find s props in
           match prop with
           | Data _ -> (False, ctx)
           | Accessor _ -> (True, ctx)
      else let pr = match attrs with { proto = p } -> p in
           is_accessor ctx pr b
    | Value _, _ -> failwith "[delta] Somehow storing a Value through an ObjCell"
  end
  | Null, String s -> raise (PrimError "isAccessor topped out")
  | Sym _, _ 
  | _, Sym _ -> failwith "prim got a symbolic exp"
  | _ -> raise (PrimError "isAccessor")

let op2 ctx op = match op with
  | "+" -> arith_sum ctx
  | "-" -> arith_sub ctx
  | "/" -> arith_div ctx
  | "*" -> arith_mul ctx
  | "%" -> arith_mod ctx
  | "&" -> bitwise_and ctx
  | "|" -> bitwise_or ctx
  | "^" -> bitwise_xor ctx
  | "<<" -> bitwise_shiftl ctx
  | ">>" -> bitwise_shiftr ctx
  | ">>>" -> bitwise_zfshiftr ctx
  | "<" -> arith_lt ctx
  | "<=" -> arith_le ctx
  | ">" -> arith_gt ctx
  | ">=" -> arith_ge ctx
  | "stx=" -> stx_eq ctx
  | "abs=" -> abs_eq ctx
  | "hasProperty" -> has_property ctx
  | "hasOwnProperty" -> has_own_property ctx
  | "string+" -> string_plus ctx
  | "string<" -> string_lessthan ctx
  | "base" -> get_base ctx
  | "char-at" -> char_at ctx
  | "locale-compare" -> locale_compare ctx
  | "pow" -> pow ctx
  | "to-fixed" -> to_fixed ctx
  | "isAccessor" -> is_accessor ctx
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
