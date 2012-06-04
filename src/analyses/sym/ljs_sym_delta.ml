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
    
let unbool b = match b with
  | True -> true
  | False -> false
  | _ -> failwith ("tried to unbool a non-bool" ^ (Ljs_sym_pretty.val_to_string b))

let symbool b = match b with
  | true -> BTrue
  | false -> BFalse

let symboolv b = match b with
  | True -> BTrue
  | False -> BFalse
  | SymScalar id -> BSym id
  | _ -> failwith ("tried to symboolv a non-bool: " ^ Ljs_sym_pretty.val_to_string b)

let to_int ctx v = match v with
  | Num x -> int_of_float x
  | _ -> raise (PrimError ("expected number, got " ^ Ljs_sym_pretty.val_to_string v))

let typeof ctx v = 
  let typestr = match v with
  | Undefined -> "undefined"
  | Null -> "null"
  | String _ -> "string"
  | Num _ -> "number"
  | True 
  | False -> "boolean"
  | ObjPtr loc -> begin match sto_lookup_obj loc ctx with
    | ConObj { attrs = { code = Some _ }} 
    | SymObj { attrs = { code = Some _ }} -> "function"
    | NewSymObj _ -> failwith "typeof got NewSymObj"
    | _ -> "object"
  end
  | Closure _ -> raise (PrimError "typeof got lambda")
  | NewSym _ | SymScalar _ -> failwith "prim got a symbolic exp"
  in 
  (String typestr, add_const_string typestr ctx)

let is_primitive ctx v = match v with
  | Undefined 
  | Null
  | String _
  | Num _
  | True | False -> (True, ctx)
  | NewSym _ | SymScalar _ -> failwith "prim got a symbolic exp"
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
  let primstr = match v with
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
  | SymScalar _ -> failwith "prim got a symbolic exp"
  | _ -> raise (PrimError "prim_to_num")
  in
  (String primstr, add_const_string primstr ctx)

let strlen ctx s = match s with
  | String s -> (Num (float_of_int (String.length s)), ctx)
  | SymScalar _ -> failwith "prim got a symbolic exp"
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
  | SymScalar _ -> failwith "prim got a symbolic exp"
  | _ -> raise (PrimError "prim_to_num")
end, ctx)
  
let prim_to_bool ctx v = (bool begin match v with
  | True -> true
  | False -> false
  | Undefined -> false
  | Null -> false
  | Num x -> not (x == nan || x = 0.0 || x = -0.0)
  | String s -> not (String.length s = 0)
  | SymScalar _ -> failwith "prim got a symbolic exp"
  | _ -> true
end, ctx)

let print ctx v = 
  let ret = match v with
    | String s -> 
      printf "%S\n%!" s; Undefined
    | Num n -> let s = string_of_float n in printf "%S\n" s; Undefined
    | SymScalar _ -> failwith "prim got a symbolic exp"
    | _ -> failwith ("[interp] Print received non-string: " ^ Ljs_sym_pretty.val_to_string v)
  in (ret, ctx)

(* Implement this here because there's no need to expose the class
   property outside of the delta function *)
let rec object_to_string ctx obj = begin
  match obj with
  | ObjPtr loc -> begin match sto_lookup_obj loc ctx with
    | ConObj { attrs = {klass = symk} }
    | SymObj { attrs = {klass = symk} } ->
      let objstr = match symk with
      | SString s -> "[object " ^ s ^ "]"
      (* TODO: add constraint relating id and this result *)
      | SSym id -> "[object " ^ id ^ "]"
      in return (String objstr) (add_const_string objstr ctx)
    | NewSymObj locs ->
      bind (init_sym_obj locs loc "object_to_string init_sym_obj" ctx) 
        (fun (_, ctx) -> object_to_string ctx obj)
  end
  | SymScalar _ -> failwith "prim got a symbolic exp"
  | _ -> raise (PrimError "object-to-string, wasn't given object")
end

let rec is_array ctx obj = begin
  match obj with
  | ObjPtr loc -> begin match sto_lookup_obj loc ctx with
    | ConObj { attrs = {klass = symk} }
    | SymObj { attrs = {klass = symk} } ->
      begin match symk with
      | SString s -> return (bool (s = "Array")) ctx
      | SSym id -> 
        let (arrStr, ctx) = const_string "Array" ctx in
        return True (add_assert (is_equal (SId id) (SId arrStr)) ctx)
        (* TODO false branch? *)
      end
    | NewSymObj locs -> bind (init_sym_obj locs loc "" ctx) 
      (fun (_, ctx) -> is_array ctx obj)
  end
  | SymScalar _ -> failwith "prim got a symbolic exp"
  | _ -> raise (PrimError "is-array")
  end


let to_int32 ctx v = (begin
  match v with
  | Num d -> Num (float_of_int (int_of_float d))
  | SymScalar _ -> failwith "prim got a symbolic exp"
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
  | ObjPtr _ -> False
  | Closure _ -> False
  | NewSym _ | SymScalar _ -> failwith "prim got a symbolic exp"
end, ctx)

let void ctx v = (Undefined, ctx)

let floor' ctx = function Num d -> (num (floor d), ctx)
  | NewSym _ | SymScalar _ -> failwith "prim got a symbolic exp"
  | _ -> raise (PrimError "floor")

let ceil' ctx = function Num d -> (num (ceil d), ctx)
  | NewSym _ | SymScalar _ -> failwith "prim got a symbolic exp"
  | _ -> raise (PrimError "ceil")

let absolute ctx = function Num d -> (num (abs_float d), ctx)
  | NewSym _ | SymScalar _ -> failwith "prim got a symbolic exp"
  | _ -> raise (PrimError "abs")

let log' ctx = function Num d -> (num (log d ), ctx)
  | NewSym _ | SymScalar _ -> failwith "prim got a symbolic exp"
  | _ -> raise (PrimError "log")

let ascii_ntoc ctx n = match n with
  | Num d ->
    let str = String.make 1 (Char.chr (int_of_float d)) in
    (String str, add_const_string str ctx)
  | NewSym _ | SymScalar _ -> failwith "prim got a symbolic exp"
  | _ -> raise (PrimError "ascii_ntoc")

let ascii_cton ctx c = match c with
  | String s -> (Num (float_of_int (Char.code (String.get s 0))), ctx)
  | NewSym _ | SymScalar _ -> failwith "prim got a symbolic exp"
  | _ -> raise (PrimError "ascii_cton")

let to_lower ctx = function
  | String s -> (String (String.lowercase s), ctx)
  | NewSym _ | SymScalar _ -> failwith "prim got a symbolic exp"
  | _ -> raise (PrimError "to_lower")

let to_upper ctx = function
  | String s -> (String (String.uppercase s), ctx)
  | NewSym _ | SymScalar _ -> failwith "prim got a symbolic exp"
  | _ -> raise (PrimError "to_lower")

let bnot ctx = function
  | Num d -> (Num (float_of_int (lnot (int_of_float d))), ctx)
  | NewSym _ | SymScalar _ -> failwith "prim got a symbolic exp"
  | _ -> raise (PrimError "bnot")

let sine ctx = function
  | Num d -> (Num (sin d), ctx)
  | NewSym _ | SymScalar _ -> failwith "prim got a symbolic exp"
  | _ -> raise (PrimError "sin")

let numstr ctx = function
  | String s -> (Num (try float_of_string s with Failure _ -> nan), ctx)
  | NewSym _ | SymScalar _ -> failwith "prim got a symbolic exp"
  | _ -> raise (PrimError "numstr")

let op1 ctx op v : (result list * exresult list) =
  let r f ctx v = uncurry return (f ctx v) in
  let op1_fun = match op with
  | "typeof" -> r typeof
  | "primitive?" -> r is_primitive
  | "prim->str" -> r prim_to_str
  | "prim->num" -> r prim_to_num
  | "prim->bool" -> r prim_to_bool
  | "print" -> r print
  | "object-to-string" -> object_to_string
  | "strlen" -> r strlen
  | "is-array" -> is_array
  | "to-int32" -> r to_int32
  | "!" -> r nnot
  | "void" -> r void
  | "floor" -> r floor'
  | "ceil" -> r ceil'
  | "abs" -> r absolute
  | "log" -> r log'
  | "ascii_ntoc" -> r ascii_ntoc
  | "ascii_cton" -> r ascii_cton
  | "to-lower" -> r to_lower
  | "to-upper" -> r to_upper
  | "~" -> r bnot
  | "sin" -> r sine
  | "numstr->num" -> r numstr
  | _ -> failwith ("no implementation of unary operator: " ^ op)
  in op1_fun ctx v

(* Since this is used to create new sym vars,
 * we use the TSymString, not TString. *)
let typeofOp1 op = match op with
  | "NOT" -> (TBool, TBool)
  | "typeof" -> (TAny, TSymString)
  | "primitive?" -> (TAny, TBool)
  | "prim->str" -> (TAny, TSymString)
  | "prim->num" -> (TAny, TNum)
  | "prim->bool" -> (TAny, TBool)
  | "print" -> (TAny, TUndef)
  | "object-to-string" -> (TObj, TSymString)
  | "strlen" -> (TSymString, TNum)
  | "is-array" -> (TAny, TBool)
  | "to-int32" -> (TAny, TNum)
  | "!" -> (TAny, TBool)
  | "void" -> (TAny, TUndef)
  | "floor" -> (TNum, TNum)
  | "ceil" -> (TNum, TNum)
  | "abs" -> (TNum, TNum)
  | "log" -> (TNum, TNum)
  | "ascii_ntoc" -> (TNum, TSymString)
  | "ascii_cton" -> (TSymString, TNum)
  | "to-lower" -> (TSymString, TSymString)
  | "to-upper" -> (TSymString, TSymString)
  | "~" -> (TNum, TNum)
  | "sin" -> (TNum, TNum)
  | "numstr->num" -> (TSymString, TNum)
  | _ -> failwith ("no implementation of unary operator: " ^ op)


let arith ctx s i_op f_op v1 v2 = match v1, v2 with
  | Num x, Num y -> (Num (f_op x y), ctx)
  | v1, v2 -> raise (PrimError ("arithmetic operator: " ^ s ^ " got non-numbers: " ^
                                   (Ljs_sym_pretty.val_to_string v1) ^ ", " ^ 
                                   (Ljs_sym_pretty.val_to_string v2) ^
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
  | NewSym _, _ | _, NewSym _
  | SymScalar _, _ 
  | _, SymScalar _ -> failwith "prim got a symbolic exp"
  | _ -> raise (PrimError "string concatenation")

let string_lessthan ctx v1 v2 = match v1, v2 with
  | String s1, String s2 -> (bool (s1 < s2), ctx)
  | NewSym _, _ | _, NewSym _
  | SymScalar _, _ 
  | _, SymScalar _ -> failwith "prim got a symbolic exp"
  | _ -> raise (PrimError "string less than")

let stx_eq ctx v1 v2 = (bool begin match v1, v2 with
  | Num x1, Num x2 -> x1 = x2
  | String x1, String x2 -> x1 = x2
  | Undefined, Undefined -> true
  | Null, Null -> true
  | True, True -> true
  | False, False -> true
  | ObjPtr loc1, ObjPtr loc2 -> loc1 = loc2
  | NewSym _, _ | _, NewSym _ -> failwith "prim got a newsym"
  | SymScalar _, _ 
  | _, SymScalar _ -> failwith "prim got a symbolic exp"
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
  | NewSym _, _ | _, NewSym _
  | SymScalar _, _ 
  | _, SymScalar _ -> failwith "prim got a symbolic exp"
  | _ -> false
(* TODO: are these all the cases? *)
end, ctx)

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
    let prefix = if x < 0.0 then "-"  else "" in
    let result = prefix ^ (base (abs_float x) (abs_float y)) in
    (String result, add_const_string result ctx)
  | NewSym _, _ | _, NewSym _
  | SymScalar _, _ 
  | _, SymScalar _ -> failwith "prim got a symbolic exp"
  | _ -> raise (PrimError "base got non-numbers")

let char_at ctx a b  = match a, b with
  | String s, Num n ->
    (String (String.make 1 (String.get s (int_of_float n))), ctx)
  | NewSym _, _ | _, NewSym _
  | SymScalar _, _ 
  | _, SymScalar _ -> failwith "prim got a symbolic exp"
  | _ -> raise (PrimError "char_at didn't get a string and a number")

let locale_compare ctx a b = match a, b with
  | String r, String s ->
    (Num (float_of_int (String.compare r s)), ctx)
  | SymScalar _, _ 
  | _, SymScalar _ -> failwith "prim got a symbolic exp"
  | _ -> raise (PrimError "locale_compare didn't get 2 strings")

let pow ctx a b = match a, b with
  | Num base, Num exp -> (Num (base ** exp), ctx)
  | NewSym _, _ | _, NewSym _
  | SymScalar _, _ 
  | _, SymScalar _ -> failwith "prim got a symbolic exp"
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
  | NewSym _, _ | _, NewSym _
  | SymScalar _, _ 
  | _, SymScalar _ -> failwith "prim got a symbolic exp"
  | _ -> raise (PrimError "to-fixed didn't get 2 numbers")
end, ctx)

let op2 ctx op a b =
  let op2_fun = match op with
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
  | "string+" -> string_plus
  | "string<" -> string_lessthan
  | "base" -> get_base
  | "char-at" -> char_at
  | "locale-compare" -> locale_compare
  | "pow" -> pow
  | "to-fixed" -> to_fixed
  | _ -> failwith ("no implementation of binary operator: " ^ op)
  in op2_fun ctx a b
let typeofOp2 op = match op with
  | "get_field" -> (TObj, TSymString, TAny)
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
  | "hasProperty" -> (TObj, TSymString, TBool)
  | "hasOwnProperty" -> (TObj, TSymString, TBool)
  | "string+" -> (TSymString, TSymString, TSymString)
  | "string<" -> (TSymString, TSymString, TBool)
  | "base" -> (TNum, TNum, TSymString)
  | "char-at" -> (TSymString, TNum, TSymString)
  | "locale-compare" -> (TSymString, TSymString, TNum)
  | "pow" -> (TNum, TNum, TNum)
  | "to-fixed" -> (TNum, TNum, TSymString)
  | "isAccessor" -> (TObj, TSymString, TBool)
  | _ -> failwith ("no implementation of binary operator: " ^ op)
