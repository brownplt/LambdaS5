open Prelude
open Ljs_syntax

let str pos v = String (pos, v)
let num pos v = Num (pos, v)
let bool pos v = match v with
  | true -> True pos
  | false -> False pos

exception PrimError of string

let typeof e = 
  match e with
  | Undefined p -> "undefined"
  | Null p -> "null"
  | String (p, _) -> "string"
  | Num (p, _) -> "number"
  | True p
  | False p -> "boolean"
  (* TODO: missing "function" and "object" *)
  | _ -> raise (PrimError "typeof")

let to_int e = match e with
  | Num (_, x) -> int_of_float x
  | _ -> raise (PrimError "to_int")

(* TODO: check *)
let is_closure e = match e with
  | Lambda (_, _, _) -> true
  | _ -> false

let is_primitive e = match e with
  | Undefined _
  | Null _
  | String (_, _)
  | Num (_, _)
  | True _ | False _ -> true
  | _ -> false

let float_str n = 
  if not (n <= n || n >= n) then "NaN"
  else
    if n == infinity then "Infinity"
    else if n == neg_infinity then "-Infinity"
    else
      if float_of_int (int_of_float n) = n
      then string_of_int (int_of_float n) 
      else string_of_float n

let prim_to_str e = match e with
  | Undefined _ -> "undefined"
  | Null _ -> "null"
  | String (_, s) -> s
  | Num (_, n) -> let fs = float_str n in let fslen = String.length fs in
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
  | True _ -> "true"
  | False _ -> "false"
  | _ -> raise (PrimError "prim_to_str")

let strlen e = match e with
  | String (_, s) -> float_of_int (String.length s)
  | _ -> raise (PrimError "strlen")

(* Section 9.3, excluding objects *)
let prim_to_num e = match e with
  | Undefined _-> nan
  | Null _ -> 0.0
  | True _ -> 1.0
  | False _ -> 0.0
  | Num (_, x) -> x
  | String (_, "") -> 0.0
  | String (_, s) -> 
     begin try float_of_string s
           with Failure _ -> nan end
  | _ -> raise (PrimError "prim_to_num")
  
let prim_to_bool e = match e with
  | True _ -> true
  | False _ -> false
  | Undefined _ -> false
  | Null _ -> false
  | Num (_, x) -> not (x == nan || x = 0.0 || x = -0.0)
  | String (_, s) -> not (String.length s = 0)
  | _ -> true

(* TODO: is_extensible *)
(* TODO: object_to_string *)
(* TODO: is_array *)

let to_int32 e = match e with
  | Num (_, d) -> (float_of_int (int_of_float d))
  | _ -> raise (PrimError "to_int32")

let nnot e = match e with
  | Undefined _ -> true
  | Null _ -> true
  | True _ -> false
  | False _ -> true
  | Num (_,d) -> if (d = 0.) || (d <> d) then true else false
  | String (_,s) -> if s = "" then true else false
  | _ -> false

let floor' e = match e with
  | Num (_, d) -> (floor d)
  | _ -> raise (PrimError "floor'")

let ceil' e = match e with
  | Num (_, d) -> (ceil d)
  | _ -> raise (PrimError "ceil'")

let absolute e = match e with
  | Num (_, d) -> (abs_float d)
  | _ -> raise (PrimError "absolute")

let log' e = match e with
  | Num (_, d) -> (log d)
  | _ -> raise (PrimError "log'")

let ascii_ntoc e = match e with
  | Num (_, d) -> String.make 1 (Char.chr (int_of_float d))
  | _ -> raise (PrimError "ascii_ntoc")

let ascii_cton e = match e with
  | String (_, s) -> float_of_int (Char.code (String.get s 0))
  | _ -> raise (PrimError "ascii_cton")

let to_lower e = match e with
  | String (_, s) ->  String.lowercase s
  | _ -> raise (PrimError "to_lower")

let to_upper e = match e with
  | String (p, s) -> String.uppercase s
  | _ -> raise (PrimError "to_upper")

let bnot e = match e with
  | Num (_, d) -> float_of_int (lnot (int_of_float d))
  | _ -> raise (PrimError "bnot")

let sine e = match e with
  | Num (_, d) -> sin d
  | _ -> raise (PrimError "sine")

let numstr e = match e with
  | String (_, "") -> 0.
  | String (_, s) -> begin try float_of_string s
                           with Failure _ -> nan end
  | _ -> raise (PrimError "numstr")

let arith s i_op f_op v1 v2 = match v1, v2 with
  | Num (_, x), Num (_, y) -> f_op x y
  | v1, v2 -> raise (PrimError "arith")

let arith_sum = arith "+" (+) (+.)

let arith_sub = arith "-" (-) (-.)

(* OCaml syntax failure! Operator section syntax lexes as a comment. *)
let arith_mul = arith "*" (fun m n -> m * n) (fun x y -> x *. y)

let arith_div x y = try arith "/" (/) (/.) x y
                    with Division_by_zero -> infinity

let arith_mod x y = try arith "mod" (mod) mod_float x y
                    with Division_by_zero -> nan

let arith_lt x y = x < y

let arith_le x y = x <= y

let arith_gt x y = x > y

let arith_ge x y = x >= y

let bitwise_and v1 v2 = float_of_int ((to_int v1) land (to_int v2))

let bitwise_or v1 v2 = float_of_int ((to_int v1) lor (to_int v2))

let bitwise_xor v1 v2 = float_of_int ((to_int v1) lxor (to_int v2))

let bitwise_shiftl v1 v2 = float_of_int ((to_int v1) lsl (to_int v2))

let bitwise_zfshiftr v1 v2 = float_of_int ((to_int v1) lsr (to_int v2))

let bitwise_shiftr v1 v2 = float_of_int ((to_int v1) asr (to_int v2))

let string_plus v1 v2 = match v1, v2 with
  | String (_, s1), String (_, s2) -> s1 ^ s2
  | _ -> raise (PrimError "string_plus")

let string_lessthan v1 v2 = match v1, v2 with
  | String (_,s1), String (_,s2) -> s1 < s2
  | _ -> raise (PrimError "string_lessthan")

let stx_eq v1 v2 = match v1, v2 with
  | Num (_,x1), Num (_,x2) -> x1 = x2
  | String (_,x1), String (_,x2) -> x1 = x2
  | Undefined _, Undefined _ -> true
  | Null _, Null _-> true
  | True _, True _-> true
  | False _, False _ -> true
  | _ -> v1 == v2 (* otherwise, pointer equality *)

(* Algorithm 11.9.3, steps 1 through 19. Steps 20 and 21 are desugared to
   access the heap. *)
let abs_eq v1 v2 =
  if v1 = v2 then (* works correctly on floating point values *)
    true
  else match v1, v2 with
    | Null _, Undefined _
    | Undefined _, Null _ -> true
    | String (_,s), Num (_,x)
    | Num (_,x), String (_,s) ->
          (try x = float_of_string s with Failure _ -> false)
    | Num (_,x), True _ 
    | True _, Num (_,x) -> x = 1.0
    | Num (_,x), False _ 
    | False _, Num (_,x) -> x = 0.0
    | _ -> false
(* TODO: are these all the cases? *)


(* Algorithm 9.12, the SameValue algorithm.
   This gives "nan = nan" and "+0 != -0". *)
let same_value v1 v2 = 
  match v1, v2 with
  | Num (_,x), Num (_,y) ->
    if x = 0. && y = 0.
    then 1. /. x = 1. /. y
    else compare x y = 0
  | _ -> compare v1 v2 = 0

(* TODO: has_property *)
(* TODO: has_own_property *)

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

let get_base n r = match n, r with
  | Num (_, x), Num (_,y) -> 
    let result = base (abs_float x) (abs_float y) in
    if x < 0.0 then "-" ^ result else result
  | _ -> raise (PrimError "get_base")

let char_at a b  = match a, b with
  | String (_,s), Num (_,n) ->
    String.make 1 (String.get s (int_of_float n))
  | _ -> raise (PrimError "char_at")

let locale_compare a b = match a, b with
  | String (_,r), String (_,s) ->
    float_of_int (String.compare r s)
  | _ -> raise (PrimError "locale_compare")

let pow a b = match a, b with
  | Num (_,base), Num (_,exp) -> base ** exp
  | _ -> raise (PrimError "pow")

let to_fixed a b = match a, b with
  | Num (_,x), Num (_,f) -> 
    let s = string_of_float x
    and fint = int_of_float f in
    if fint = 0 
    then string_of_int (int_of_float x)
    else let dot_index = String.index s '.'
         and len = String.length s in
         let prefix_chars = dot_index in
         let decimal_chars = len - (prefix_chars + 1) in
         if decimal_chars = fint 
         then s
         else 
           if decimal_chars > fint
           then let fixed_s = String.sub s 0 (fint - prefix_chars) in
                fixed_s
           else let suffix = String.make (fint - decimal_chars) '0' in
                s ^ suffix
  | _ -> raise (PrimError "to_fixed")

(* TODO: is_accessor *)

let op1 pos op e = 
  let apply op exp type_func= 
    try let v = op exp in
        Some (type_func pos v)
    with Failure _ -> None in

  match op with
  | "typeof" -> apply typeof e str
  | "closure?" -> apply is_closure e bool
  | "primitive?" -> apply is_primitive e bool
  | "prim->str" ->  apply prim_to_str e str
  | "prim->num" -> apply prim_to_num e num
  | "prim->bool" -> apply prim_to_bool e bool
  | "object-to-string" -> None
  | "strlen" -> apply strlen e num
  | "is-array" -> None
  | "to-int32" -> apply to_int32 e num
  | "!" -> apply nnot e bool
  | "void" -> Some (Undefined pos)
  | "floor" -> apply floor' e num
  | "ceil" -> apply ceil' e num
  | "abs" -> apply absolute e num
  | "log" -> apply log' e num
  | "ascii_ntoc" -> apply ascii_ntoc e str
  | "ascii_cton" -> apply ascii_cton e num
  | "to-lower" -> apply to_lower e str
  | "to-upper" -> apply to_upper e str
  | "~" -> apply bnot e num
  | "sin" -> apply sine e num
  | "numstr->num" -> apply numstr e num
  | _ -> None

let op2 pos op e1 e2 = 
  let apply op e1 e2 type_func = 
    try let v = op e1 e2 in
        Some (type_func pos v)
    with Failure _ -> None in
  match op with
  | "+" -> apply arith_sum e1 e2 num 
  | "-" -> apply arith_sub e1 e2 num
  | "/" -> apply arith_div e1 e2 num
  | "*" -> apply arith_mul e1 e2 num
  | "%" -> apply arith_mod e1 e2 num
  | "&" -> apply bitwise_and e1 e2 num
  | "|" -> apply bitwise_or e1 e2 num
  | "^" -> apply bitwise_xor e1 e2 num
  | "<<" -> apply bitwise_shiftl e1 e2 num
  | ">>" -> apply bitwise_shiftr e1 e2 num
  | ">>>" -> apply bitwise_zfshiftr e1 e2 num
  | "<" -> apply arith_lt e1 e2 bool
  | "<=" -> apply arith_le e1 e2 bool
  | ">" -> apply arith_gt e1 e2 bool
  | ">=" -> apply arith_ge e1 e2 bool
  | "stx=" -> apply stx_eq e1 e2 bool
  | "abs=" -> apply abs_eq e1 e2 bool
  | "sameValue" -> apply same_value e1 e2 bool
  | "hasProperty" -> None
  | "hasOwnProperty" -> None
  | "string+" -> apply string_plus e1 e2 str
  | "string<" -> apply string_lessthan e1 e2 bool
  | "base" -> apply get_base e1 e2 str
  | "char-at" -> apply char_at e1 e2 str
  | "locale-compare" -> apply locale_compare e1 e2 num
  | "pow" -> apply pow e1 e2 num
  | "to-fixed" -> apply to_fixed e1 e2 str
  | "isAccessor" -> None
  | _ -> None

