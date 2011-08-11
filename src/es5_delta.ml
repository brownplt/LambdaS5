open Prelude
open Es5_syntax
open Es5_values

let undef = Undefined
let null = Null
let str s = String s
let num f = Num f

let bool b = match b with
  | true -> True
  | false -> False

let to_int v = match v with
  | Num x -> int_of_float x
  | _ -> raise (Throw (str ("expected number, got " ^ pretty_value v)))

let typeof v = str begin match v with
  | Undefined -> "undefined"
  | Null -> "null"
  | String _ -> "string"
  | Num _ -> "number"
  | True 
  | False -> "boolean"
  | ObjCell o -> begin match !o with
      | ({ code = Some cexp }, _) -> "function"
      | _ -> "object"
  end
  | Closure _ -> "lambda"
  | VarCell _ -> failwith "[delta] typeof got a variable"
  | Fail s -> 
    failwith (sprintf "[delta] typeof got a fail: %s" s)
end

let surface_typeof v = begin match v with
  | Closure _ -> raise (Throw (str "surface_typeof got lambda"))
  | Null -> str "object"
  | _ -> typeof v
end
  
let is_primitive v = match v with
  | Undefined 
  | Null
  | String _
  | Num _
  | True | False -> True
  | _ -> False

let float_str n = 
  if n == nan then "NaN"
  else
    if n == infinity then "Infinity"
    else
      if float_of_int (int_of_float n) = n
      then string_of_int (int_of_float n) 
      else string_of_float n

let prim_to_str v = str begin match v with
  | Undefined -> "undefined"
  | Null -> "null"
  | String s -> s
  | Num n -> let open String in let fs = float_str n in let fslen = length fs in
    if get fs (fslen - 1) = '.' then sub fs 0 (fslen - 1) else
      (* This is because we don't want leading zeroes in the "-e" part.
       * For example, OCaml says 1.2345e-07, but ES5 wants 1.2345e-7 *)
      if contains fs '-'
        then let indx = index fs '-' in 
          let prefix = sub fs 0 (indx + 1) in
          let suffix = sub fs (indx + 1) (fslen - (length prefix)) in
          let slen = length suffix in
          let fixed = if slen > 1 && (get suffix 0 = '0') 
            then sub suffix 1 (slen - 1)
            else suffix in
          prefix ^ fixed 
        else fs
  | True -> "true"
  | False -> "false"
  | _ -> raise (Throw (str "prim_to_num"))
end

let strlen s = match s with
  | String s -> Num (float_of_int (String.length s))
  | _ -> raise (Throw (str "strlen"))

let index_of_helper obj =
  let start = match obj with
    | ObjCell o -> begin match !o with
      | (_, props) -> let prop = IdMap.find "0" props in
      match prop with | Data ({ value = Num d; _ }, _, _) -> int_of_float d
      end
    | _ -> raise (Throw (str "index_of_helper"))
  and searchlen = match obj with
    | ObjCell o -> begin match !o with
      | (_, props) -> let prop = IdMap.find "1" props in
      match prop with | Data ({ value = Num d; _ }, _, _) -> int_of_float d
      end
      | _ -> raise (Throw (str "index_of_helper"))
  and len = match obj with
    | ObjCell o -> begin match !o with
      | (_, props) -> let prop = IdMap.find "2" props in
      match prop with | Data ({ value = Num d; _ }, _, _) -> int_of_float d
      end
      | _ -> raise (Throw (str "index_of_helper"))
  and s = match obj with
    | ObjCell o -> begin match !o with
      | (_, props) -> let prop = IdMap.find "3" props in
      match prop with | Data ({ value = String d; _ }, _, _) -> d
      end
      | _ -> raise (Throw (str "index_of_helper"))
  and searchstr = match obj with
    | ObjCell o -> begin match !o with
      | (_, props) -> let prop = IdMap.find "4" props in
      match prop with | Data ({ value = String d; _ }, _, _) -> d
      end
      | _ -> raise (Throw (str "index_of_helper")) in
  let rec checkall j = 
    if j == searchlen then true
    else if (String.get s j) != (String.get searchstr j) then false
    else checkall (j + 1)
  and range i j = if i > j then [] else i :: (range (i+1) j) in
  let results = 
    List.filter (fun n -> checkall n) (range start (start + (min len searchlen))) in
  match results with 
    | [] -> Num (-1.0)
    | l -> 
      let result_int = fold_right (fun a b -> if a < b then a else b) l max_int in
      let result_float = float_of_int result_int in
      Num result_float
  
(* Section 9.3, excluding objects *)
let prim_to_num v = num begin match v with
  | Undefined -> nan 
  | Null -> 0.0
  | True -> 1.0
  | False -> 0.0
  | Num x -> x
  | String "" -> 0.0
  | String s -> begin try float_of_string s
    with Failure _ -> nan end
  | _ -> raise (Throw (str "prim_to_num"))
end
  
let prim_to_bool v = bool begin match v with
  | True -> true
  | False -> false
  | Undefined -> false
  | Null -> false
  | Num x -> not (x == nan || x = 0.0 || x = -0.0)
  | String s -> not (String.length s = 0)
  | _ -> true
end

let is_callable obj = bool begin match obj with
  | ObjCell o -> begin match !o with
      | ({ code = Some (Closure c); }, _) -> true
      | _ -> false
  end
  | _ -> false
end

let print v = match v with
  | String s -> 
      printf "%S\n%!" s; Undefined
  | Num n -> let s = string_of_float n in printf "%S\n" s; Undefined
  | _ -> failwith ("[interp] Print received non-string: " ^ pretty_value v)

let is_extensible obj = match obj with
  | ObjCell o -> begin match !o with
      | ({ extensible = true; }, _) -> True
      | _ -> False
  end
  | _ -> raise (Throw (str "is-extensible"))

let prevent_extensions obj = match obj with
  | ObjCell o -> 
      let (attrs, props) = !o in begin
	  o := ({attrs with extensible = true}, props);
	  obj
	end
  | _ -> raise (Throw (str "prevent-extensions"))
      
let get_code obj = match obj with
  | ObjCell o -> begin match !o with
    | ({ code = Some v; }, _) -> v
    | ({ code = None; }, _) -> Null
  end
    | _ -> raise (Throw (str "get-code"))

let get_proto obj = match obj with
  | ObjCell o -> begin match !o with 
      | ({ proto = pvalue; }, _) -> pvalue
  end
  | _ -> raise (Throw (str "get-proto"))

let get_primval obj = match obj with
  | ObjCell o -> begin match !o with
      | ({ primval = Some v; }, _) -> v
      | _ -> raise (Throw (str "get-primval on an object with no prim val"))
  end
  | _ -> raise (Throw (str "get-primval"))

let get_class obj = match obj with
  | ObjCell o -> begin match !o with
      | ({ klass = s; }, _) -> String (s)
  end
  | _ -> raise (Throw (str "get-class"))

(* All the enumerable property names of an object *)
let rec get_property_names obj = match obj with
  | ObjCell o ->
      let protos = obj::(all_protos obj) in
      let folder o set = begin match o with
	| ObjCell o' ->
	    let (attrs, props) = !o' in
	      IdMap.fold (fun k v s -> 
			    if enum v then IdSet.add k s else s) props set
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
        ObjCell (ref (d_attrsv, name_props))
  | _ -> raise (Throw (str "get-property-names"))

and all_protos o = 
  match o with
    | ObjCell c -> begin match !c with 
        | ({ proto = pvalue; }, _) -> pvalue::(all_protos pvalue)
    end
    | _ -> []

and enum prop = match prop with
  | Accessor (_, b, _)
  | Data (_, b, _) -> b

let get_own_property_names obj = match obj with
  | ObjCell o ->
      let (_, props) = !o in
      let add_name n x m = 
	IdMap.add (string_of_int x) 
          (Data ({ value = String n; writable = false; }, false, false)) 
          m in
      let namelist = IdMap.fold (fun k v l -> (k :: l)) props [] in
      let props = 
	List.fold_right2 add_name namelist (iota (List.length namelist)) IdMap.empty
      in
	ObjCell (ref (d_attrsv, props))
  | _ -> raise (Throw (str "own-property-names"))

(* Implement this here because there's no need to expose the class
   property outside of the delta function *)
let object_to_string obj = match obj with
  | ObjCell o -> begin match !o with
      | ({ klass = s }, _) -> str ("[object " ^ s ^ "]")
  end
  | _ -> raise (Throw (str "object-to-string, wasn't given object"))	

let is_array obj = match obj with
  | ObjCell o -> begin match !o with
      | ({ klass = "Array"; }, _) -> True
      | _ -> False
    end
  | _ -> raise (Throw (str "is-array"))	


let to_int32 v = match v with
  | Num d -> Num (float_of_int (int_of_float d))
  | _ -> raise (Throw (str "to-int"))

let fail v = match v with
  | Fail _ -> True
  | _ -> False

let nnot e = match e with
  | Undefined -> True
  | Null -> True
  | True -> False
  | False -> True
  | Num d -> if d = 0. then True else False
  | String s -> if s = "" then True else False
  | ObjCell _ -> False

let void v = Undefined

let floor' = function Num d -> num (floor d) | _ -> raise (Throw (str "floor"))

let absolute = function Num d -> num (abs_float d) | _ -> raise (Throw (str "abs"))

let ascii_ntoc n = match n with
  | Num d -> str (String.make 1 (Char.chr (int_of_float d)))
  | _ -> raise (Throw (str "ascii_ntoc"))

let ascii_cton c = match c with
  | String s -> Num (float_of_int (Char.code (String.get s 0)))
  | _ -> raise (Throw (str "ascii_cton"))

let prim_strlen = function
  | String s -> Num (float_of_int (String.length s))
  | _ -> raise (Throw (str "prim_strlen"))

let op1 op = match op with
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
  | "indexofhelper" -> index_of_helper
  | "is-array" -> is_array
  | "to-int32" -> to_int32
  | "fail?" -> fail
  | "!" -> nnot
  | "void" -> void
  | "floor" -> floor'
  | "abs" -> absolute
  | "ascii_ntoc" -> ascii_ntoc
  | "ascii_cton" -> ascii_cton
  | "strlen" -> prim_strlen
  | _ -> failwith ("no implementation of unary operator: " ^ op)

let arith i_op f_op v1 v2 = match v1, v2 with
  | Num x, Num y -> Num (f_op x y)
  | v1, v2 -> raise (Throw (str ("arithmetic operator got non-numbers: " ^
                                 (pretty_value v1) ^ ", " ^ (pretty_value v2) ^
                                   "perhaps something wasn't desugared fully?")))

let arith_sum = arith (+) (+.)

let arith_sub = arith (-) (-.)

(* OCaml syntax failure! Operator section syntax lexes as a comment. *)
let arith_mul = arith (fun m n -> m * n) (fun x y -> x *. y)

let arith_div x y = try arith (/) (/.) x y
with Division_by_zero -> Num infinity

let arith_mod x y = try arith (mod) mod_float x y
with Division_by_zero -> Num nan

let arith_lt x y = bool (x < y)

let arith_le x y = bool (x <= y)

let arith_gt x y = bool (x > y)

let arith_ge x y = bool (x >= y)

let bitwise_and v1 v2 = Num (float_of_int ((to_int v1) land (to_int v2)))

let bitwise_or v1 v2 = Num (float_of_int ((to_int v1) lor (to_int v2)))

let bitwise_xor v1 v2 = Num (float_of_int ((to_int v1) lxor (to_int v2)))

let bitwise_shiftl v1 v2 = Num (float_of_int ((to_int v1) lsl (to_int v2)))

let bitwise_zfshiftr v1 v2 = Num (float_of_int ((to_int v1) lsr (to_int v2)))

let bitwise_shiftr v1 v2 = Num (float_of_int ((to_int v1) asr (to_int v2)))

let string_plus v1 v2 = match v1, v2 with
  | String s1, String s2 ->
      String (s1 ^ s2)
  | _ -> raise (Throw (str "string concatenation"))

let string_lessthan v1 v2 = match v1, v2 with
  | String s1, String s2 -> bool (s1 < s2)
  | _ -> raise (Throw (str "string less than"))

let stx_eq v1 v2 = bool begin match v1, v2 with
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
let abs_eq v1 v2 = bool begin
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

let rec has_property obj field = match obj, field with
  | ObjCell o, String s -> begin match !o, s with
      ({ proto = pvalue; }, props), s ->
        if (IdMap.mem s props) then bool true
        else has_property pvalue field
  end
  | _ -> bool false

let has_own_property obj field = match obj, field with
  | ObjCell o, String s -> 
      let (attrs, props) = !o in
        bool (IdMap.mem s props)
  | _ -> raise (Throw (str "has-own-property?"))

let base n r = let open String in let open Char in let open List in
  let rec get_digits n l = match n with
    | 97 -> 'a' :: l
    | i -> get_digits (n - 1) ((chr i) :: l) in
  let digits = 
    ['0'; '1'; '2'; '3'; '4'; '5'; '6'; '7'; '8'; '9'] @ (get_digits 122 []) in
  let rec get_num_digits num so_far =
    if (r ** so_far) > num then so_far -. 1.0
    else get_num_digits num (so_far +. 1.0) in
  let rec convert b result len = 
    let lp = r ** len in
    let index = floor (b /. lp) in
    let digit = make 1 (nth digits (int_of_float index)) in
    if len = 0.0 then result ^ digit
    else convert (b -. (index *. lp)) (result ^ digit)  (len -. 1.0) in
  let rec shift frac n = if n = 0 then frac else shift (frac *. 10.0) (n - 1) in
  let (f, integ) = modf n in
  let shifted = shift f ((String.length (string_of_float f)) - 2) in
  if (f = 0.0) then
    let d = get_num_digits n 0.0 in
    convert n "" d
  else
    (* TODO: implement *)
    "non-base-10 with fractional parts NYI"

let get_base n r = match n, r with
  | Num x, Num y -> 
    let result = base (abs_float x) (abs_float y) in
    str (if x < 0.0 then "-" ^ result else result)
  | _ -> raise (Throw (str "base got non-numbers"))

let char_at a b  = match a, b with
  | String s, Num n ->
    let open String in
    String (make 1 (get s (int_of_float n)))
  | _ -> raise (Throw (str "char_at didn't get a string and a number"))

let op2 op = match op with
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
  | _ -> failwith ("no implementation of binary operator: " ^ op)

let op3 op = match op with
  | _ -> failwith ("no ternary operators yet, so what's this: " ^ op)
