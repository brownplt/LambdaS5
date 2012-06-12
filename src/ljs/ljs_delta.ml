open Prelude
open Ljs_syntax
open Ljs_values

exception PrimErr of exp list * value

let undef = Undefined
let null = Null
let str s = String s
let num f = Num f

let bool b = match b with
  | true -> True
  | false -> False

let to_int v = match v with
  | Num x -> int_of_float x
  | _ -> raise (PrimErr ([], str ("expected number, got " ^ pretty_value v)))

let typeof store v = str begin match v with
  | Undefined -> "undefined"
  | Null -> "null"
  | String _ -> "string"
  | Num _ -> "number"
  | True 
  | False -> "boolean"
  | ObjLoc loc -> begin match get_obj store loc with
      | ({ code = Some cexp }, _) -> "function"
      | _ -> "object"
  end
  | Closure _ -> raise (PrimErr ([], str "typeof got lambda"))
end

let is_primitive store v = match v with
  | Undefined 
  | Null
  | String _
  | Num _
  | True | False -> True
  | _ -> False

let float_str n = 
  if not (n <= n || n >= n) then "NaN"
  else
    if n == infinity then "Infinity"
    else if n == neg_infinity then "-Infinity"
    else
      if float_of_int (int_of_float n) = n
      then string_of_int (int_of_float n) 
      else string_of_float n

let prim_to_str store v = str begin match v with
  | Undefined -> "undefined"
  | Null -> "null"
  | String s -> s
  | Num n -> let fs = float_str n in let fslen = String.length fs in
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
        else fs
  | True -> "true"
  | False -> "false"
  | _ -> raise (PrimErr ([], str "prim_to_str"))
end

let strlen store s = match s with
  | String s -> Num (float_of_int (String.length s))
  | _ -> raise (PrimErr ([], str "strlen"))

(* Section 9.3, excluding objects *)
let prim_to_num store v = num begin match v with
  | Undefined -> nan 
  | Null -> 0.0
  | True -> 1.0
  | False -> 0.0
  | Num x -> x
  | String "" -> 0.0
  | String s -> begin try float_of_string s
    with Failure _ -> nan end
  | _ -> raise (PrimErr ([], str "prim_to_num"))
end
  
let prim_to_bool store v = bool begin match v with
  | True -> true
  | False -> false
  | Undefined -> false
  | Null -> false
  | Num x -> not (x == nan || x = 0.0 || x = -0.0)
  | String s -> not (String.length s = 0)
  | _ -> true
end

let print store v = match v with
  | String s -> 
      printf "%s\n%!" s; Undefined
  | Num n -> let s = string_of_float n in printf "%S\n" s; Undefined
  | _ -> failwith ("[interp] Print received non-string: " ^ pretty_value v)

let is_extensible store obj = match obj with
  | ObjLoc loc -> begin match get_obj store loc with
      | ({ extensible = true; }, _) -> True
      | _ -> False
  end
  | _ -> raise (PrimErr ([], str "is-extensible"))

(* Implement this here because there's no need to expose the class
   property outside of the delta function *)
let object_to_string store obj = match obj with
  | ObjLoc loc -> begin match get_obj store loc with
      | ({ klass = s }, _) -> str ("[object " ^ s ^ "]")
  end
  | _ -> raise (PrimErr ([], str "object-to-string, wasn't given object"))	

let is_array store obj = match obj with
  | ObjLoc loc -> begin match get_obj store loc with
      | ({ klass = "Array"; }, _) -> True
      | _ -> False
    end
  | _ -> raise (PrimErr ([], str "is-array"))	


let to_int32 store v = match v with
  | Num d -> Num (float_of_int (int_of_float d))
  | _ -> raise (PrimErr ([], str "to-int"))

let nnot store e = match e with
  | Undefined -> True
  | Null -> True
  | True -> False
  | False -> True
  | Num d -> if (d = 0.) || (d <> d) then True else False
  | String s -> if s = "" then True else False
  | ObjLoc _ -> False
  | Closure _ -> False

let void store v = Undefined

let floor' store = function Num d -> num (floor d) | _ -> raise (PrimErr ([], str "floor"))

let ceil' store= function Num d -> num (ceil d) | _ -> raise (PrimErr ([], str "ceil"))

let absolute store = function Num d -> num (abs_float d) | _ -> raise (PrimErr ([], str "abs"))

let log' store = function Num d -> num (log d ) | _ -> raise (PrimErr ([], str "log"))

let ascii_ntoc store n = match n with
  | Num d -> str (String.make 1 (Char.chr (int_of_float d)))
  | _ -> raise (PrimErr ([], str "ascii_ntoc")) 
let ascii_cton store c = match c with
  | String s -> Num (float_of_int (Char.code (String.get s 0)))
  | _ -> raise (PrimErr ([], str "ascii_cton"))

let to_lower store = function
  | String s -> String (String.lowercase s)
  | _ -> raise (PrimErr ([], str "to_lower"))

let to_upper store = function
  | String s -> String (String.uppercase s)
  | _ -> raise (PrimErr ([], str "to_lower"))

let bnot store = function
  | Num d -> Num (float_of_int (lnot (int_of_float d)))
  | _ -> raise (PrimErr ([], str "bnot"))

let sine store = function
  | Num d -> Num (sin d)
  | _ -> raise (PrimErr ([], str "sin"))

let numstr store = function
  | String "" -> Num 0.
  | String s -> Num (try float_of_string s with Failure _ -> nan)
  | _ -> raise (PrimErr ([], str "numstr"))

let current_utc store = function
  | _ -> Num (Unix.gettimeofday ())

let op1 store op = match op with
  | "typeof" -> typeof store
  | "primitive?" -> is_primitive store
  | "prim->str" -> prim_to_str store
  | "prim->num" -> prim_to_num store
  | "prim->bool" -> prim_to_bool store
  | "print" -> print store
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
  | "current-utc-millis" -> current_utc store
  | _ -> raise (PrimErr ([], String ("no implementation of unary operator: " ^ op)))

let arith store s i_op f_op v1 v2 = match v1, v2 with
  | Num x, Num y -> Num (f_op x y)
  | v1, v2 -> raise (PrimErr ([], str ("arithmetic operator: " ^ s ^ " got non-numbers: " ^
                                 (pretty_value v1) ^ ", " ^ (pretty_value v2) ^
                                   "perhaps something wasn't desugared fully?")))

let arith_sum store = arith store "+" (+) (+.)

let arith_sub store = arith store "-" (-) (-.)

(* OCaml syntax failure! Operator section syntax lexes as a comment. *)
let arith_mul store = arith store "*" (fun m n -> m * n) (fun x y -> x *. y)

let arith_div store x y = try arith store "/" (/) (/.) x y
with Division_by_zero -> Num infinity

let arith_mod store x y = try arith store "mod" (mod) mod_float x y
with Division_by_zero -> Num nan

let arith_lt store x y = bool (x < y)

let arith_le store x y = bool (x <= y)

let arith_gt store x y = bool (x > y)

let arith_ge store x y = bool (x >= y)

let bitwise_and store v1 v2 = Num (float_of_int ((to_int v1) land (to_int v2)))

let bitwise_or store v1 v2 = Num (float_of_int ((to_int v1) lor (to_int v2)))

let bitwise_xor store v1 v2 = Num (float_of_int ((to_int v1) lxor (to_int v2)))

let bitwise_shiftl store v1 v2 = Num (float_of_int ((to_int v1) lsl (to_int v2)))

let bitwise_zfshiftr store v1 v2 = Num (float_of_int ((to_int v1) lsr (to_int v2)))

let bitwise_shiftr store v1 v2 = Num (float_of_int ((to_int v1) asr (to_int v2)))

let string_plus store v1 v2 = match v1, v2 with
  | String s1, String s2 ->
      String (s1 ^ s2)
  | _ -> raise (PrimErr ([], str "string concatenation"))

let string_lessthan store v1 v2 = match v1, v2 with
  | String s1, String s2 -> bool (s1 < s2)
  | _ -> raise (PrimErr ([], str "string less than"))

let stx_eq store v1 v2 = bool begin match v1, v2 with
  | Num x1, Num x2 -> x1 = x2
  | String x1, String x2 -> x1 = x2
  | Undefined, Undefined -> true
  | Null, Null -> true
  | True, True -> true
  | False, False -> true
  | _ -> v1 == v2 (* otherwise, pointer equality *)
end

(* Algorithm 11.9.3, steps 1 through 19. Steps 20 and 21 are desugared to
   access the heap. *)
let abs_eq store v1 v2 = bool begin
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
    | _ -> false
(* TODO: are these all the cases? *)
end

let rec has_property store obj field = match obj, field with
  | ObjLoc loc, String s -> begin match get_obj store loc, s with
      ({ proto = pvalue; }, props), s ->
        if (IdMap.mem s props) then bool true
        else has_property store pvalue field
  end
  | _ -> bool false

let has_own_property store obj field = match obj, field with
  | ObjLoc loc, String s -> 
      let (attrs, props) = get_obj store loc in
        bool (IdMap.mem s props)
  | ObjLoc loc, _ -> raise (PrimErr ([], str "has-own-property: field not a string"))
  | _, String s -> raise (PrimErr ([], str ("has-own-property: obj not an object for field " ^ s)))
  | _ -> raise (PrimErr ([], str "has-own-property: neither an object nor a string"))

let base store n r = 
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
    let result = base store (abs_float x) (abs_float y) in
    str (if x < 0.0 then "-" ^ result else result)
  | _ -> raise (PrimErr ([], str "base got non-numbers"))

let char_at store a b  = match a, b with
  | String s, Num n ->
    String (String.make 1 (String.get s (int_of_float n)))
  | _ -> raise (PrimErr ([], str "char_at didn't get a string and a number"))

let locale_compare store a b = match a, b with
  | String r, String s ->
    Num (float_of_int (String.compare r s))
  | _ -> raise (PrimErr ([], str "locale_compare didn't get 2 strings"))

let pow store a b = match a, b with
  | Num base, Num exp -> Num (base ** exp)
  | _ -> raise (PrimErr ([], str "pow didn't get 2 numbers"))

let to_fixed store a b = match a, b with
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
  | _ -> raise (PrimErr ([], str "to-fixed didn't get 2 numbers"))

let rec is_accessor store a b = match a, b with
  | ObjLoc loc, String s ->
    let (attrs, props) = get_obj store loc in
    if IdMap.mem s props
    then let prop = IdMap.find s props in
      match prop with
        | Data _ -> False
        | Accessor _ -> True
    else let pr = match attrs with { proto = p } -> p in
      is_accessor store pr b
  | Null, String s -> raise (PrimErr ([], str "isAccessor topped out"))
  | _ -> raise (PrimErr ([], str "isAccessor"))

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
  | _ -> raise (PrimErr ([], String ("no implementation of binary operator: " ^ op)))
