open Prelude
open Es5_syntax
open JavaScript_syntax
open Es5_values

let undef = Const JavaScript_syntax.CUndefined

let str s = Const (JavaScript_syntax.CString s)

let num f = Const (JavaScript_syntax.CNum f)

let bool b = Const (JavaScript_syntax.CBool b)

let get_const v = match v with
  | Const c -> c
  | _ -> raise (Throw (str "expected primtive constant"))

let to_int v = match v with
  | Const (CInt n) -> n
  | Const (CNum x) -> int_of_float x
  | _ -> raise (Throw (str ("expected number, got " ^ pretty_value v)))

let to_float v = match v with
  | Const (CInt n) -> float_of_int n
  | Const (CNum x) -> x
  | _ -> raise (Throw (str ("expected number, got " ^ pretty_value v)))

let typeof v = str begin match v with
  | Const c -> begin match c with
      | CUndefined -> "undefined"
      | CNull -> "null"
      | CString _ -> "string"
      | CNum _ -> "number"
      | CInt _ -> "number"
      | CBool _ -> "boolean"
    end
  | ObjCell _ -> "object"
  | Closure _ -> "lambda"
end

let surface_typeof v = str begin match v with
  | Const c -> begin match c with
      | CUndefined -> "undefined"
      | CNull -> "null"
      | CString _ -> "string"
      | CNum _ -> "number"
      | CInt _ -> "number"
      | CBool _ -> "boolean"
    end
  | ObjCell o -> let (attrs, _) = !o in
      if (IdMap.mem "code" attrs) then "function" else "object"
  | _ -> raise (Throw (str "surface_typeof"))
end
  
let is_primitive v = match v with
  | Const _ -> Const (CBool true)
  | _ -> Const (CBool false)

let float_str n = 
  if n == nan then "NaN"
  else
    if n == infinity then "Infinity"
    else
      if float_of_int (int_of_float n) = n
      then string_of_int (int_of_float n) 
      else string_of_float n


let prim_to_str v = str begin match v with
  | Const c -> begin match c with
      | CUndefined -> "undefined"
      | CNull -> "null"
      | CString s -> s
      | CNum n -> float_str n
      | CInt n -> string_of_int n
      | CBool b -> string_of_bool b
    end
  | _ -> raise (Throw (str "prim_to_str"))
end

(* Section 9.3, excluding objects *)
let prim_to_num v = num begin match v with
  | Const c -> begin match c with
      | CUndefined -> nan 
      | CNull -> 0.0
      | CBool true -> 1.0
      | CBool false -> 0.0
      | CNum x -> x
      | CInt n -> float_of_int n
      | CString s -> begin try float_of_string s
        with Failure _ -> nan end
    end
  | _ -> raise (Throw (str "prim_to_str"))
end
  
let prim_to_bool v = bool begin match v with
  | Const c -> begin match c with
      | CBool b -> b
      | CUndefined -> false
      | CNull -> false
      | CNum x -> not (x == nan || x = 0.0 || x = -0.0)
      | CInt n -> not (n = 0)
      | CString s -> not (String.length s = 0)
    end
  | _ -> true
end

let is_callable obj = bool begin match obj with
  | ObjCell o -> let (attrs, props) = !o in begin try
      match IdMap.find "code" attrs with
	| Closure c -> true
	| _ -> false
    with Not_found -> false
    end
  | _ -> false
end

let print v = match v with
  | Const (CString s) -> 
      printf "%S\n" s; Const CUndefined
  | _ -> failwith ("[interp] Print received non-string: " ^ pretty_value v)

let is_extensible obj = match obj with
  | ObjCell o ->
      let (attrs, props) = !o in begin try
	  bool (IdMap.find "extensible" attrs =
	      bool true)
	with Not_found -> bool false
	end
  | _ -> raise (Throw (str "is-extensible"))

let prevent_extensions obj = match obj with
  | ObjCell o ->
      let (attrs, props) = !o in begin
	  o := (IdMap.add "extensible" (bool false) attrs, props);
	  obj
	end
  | _ -> raise (Throw (str "prevent-extensions"))
      

let get_proto obj = match obj with
  | ObjCell o -> 
      let (attrs, _) = !o in begin try
	  IdMap.find "proto" attrs
	with Not_found -> undef
	end
  | _ -> raise (Throw (str "get-proto"))


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
	  (AttrMap.add Value (Const (CString name)) AttrMap.empty) props in
      let name_props = List.fold_right2 prop_folder 
        (iota (List.length name_list))
        name_list
        IdMap.empty in
        ObjCell (ref (IdMap.empty, name_props))
  | _ -> raise (Throw (str "get-property-names"))

and all_protos o = 
  match o with
    | ObjCell c ->
	let (attrs, props) = !c in begin try
	    let proto = (IdMap.find "proto" attrs) in
	      proto::(all_protos proto)
	  with Not_found -> []
	  end
    | _ -> []

and enum prop = AttrMap.mem Enum prop && 
  (AttrMap.find Enum prop = Const (CBool true))

let get_own_property_names obj = match obj with
  | ObjCell o ->
      let (_, props) = !o in
      let add_name n x m = 
	IdMap.add (string_of_int x) (AttrMap.add Value (str n) AttrMap.empty) m in
      let namelist = IdMap.fold (fun k v l -> (k :: l)) props [] in
      let props = 
	List.fold_right2 add_name namelist (iota (List.length namelist)) IdMap.empty
      in
	ObjCell (ref (IdMap.empty, props))
  | _ -> raise (Throw (str "own-property-names"))

(* Implement this here because there's no need to expose the class
   property outside of the delta function *)
let object_to_string obj = match obj with
  | ObjCell o -> let (attrs, props) = !o in begin try
      match IdMap.find "class" attrs with
	| Const (CString s) -> str ("[object " ^ s ^ "]")
	| _ -> raise (Throw (str "object-to-string, class wasn't a string"))	
    with Not_found -> raise (Throw (str "object-to-string, didn't find class"))
    end
  | _ -> raise (Throw (str "object-to-string, wasn't given object"))	

let is_array obj = match obj with
  | ObjCell o -> let (attrs, props) = !o in begin try
      match IdMap.find "class" attrs with
	| Const (CString "Array") -> Const (CBool true)
	| _ -> Const (CBool false)
    with Not_found -> raise (Throw (str "is-array"))
    end
  | _ -> raise (Throw (str "is-array"))	


let to_int32 v = match v with
  | Const (CInt d) -> v
  | Const (CNum d) -> Const (CInt (int_of_float d))
  | _ -> raise (Throw (str "to-int"))

let fail v = match v with
  | Fail _ -> Const (CBool true)
  | _ -> Const (CBool false)

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
  | "property-names" -> get_property_names
  | "own-property-names" -> get_own_property_names
  | "object-to-string" -> object_to_string
  | "is-array" -> is_array
  | "to-int32" -> to_int32
  | "fail?" -> fail
  | _ -> failwith ("no implementation of unary operator: " ^ op)

let arith i_op f_op v1 v2 = match v1, v2 with
  | Const (CInt m), Const (CInt n) -> Const (CInt (i_op m n))
  | Const (CNum x), Const (CNum y) -> Const (CNum (f_op x y))
  | Const (CNum x), Const (CInt n) -> Const (CNum (f_op x (float_of_int n)))
  | Const (CInt m), Const (CNum y) -> Const (CNum (f_op (float_of_int m) y))
  | _ -> raise (Throw (str "arithmetic operator"))

let arith_sum = arith (+) (+.)

let arith_sub = arith (-) (-.)

(* OCaml syntax failure! Operator section syntax lexes as a comment. *)
let arith_mul = arith (fun m n -> m * n) (fun x y -> x *. y)

let arith_div x y = try arith (/) (/.) x y
with Division_by_zero -> Const (CNum infinity)

let arith_mod x y = try arith (mod) mod_float x y
with Division_by_zero -> Const (CNum nan)

let arith_lt x y = bool (to_float x < to_float y)

let arith_le x y = bool (to_float x <= to_float y)

let arith_gt x y = bool (to_float x > to_float y)

let arith_ge x y = bool (to_float x >= to_float y)

let bitwise_and v1 v2 = Const (CInt ((to_int v1) land (to_int v2)))

let bitwise_or v1 v2 = Const (CInt ((to_int v1) lor (to_int v2)))

let bitwise_xor v1 v2 = Const (CInt ((to_int v1) lxor (to_int v2)))

let bitwise_shiftl v1 v2 = Const (CInt ((to_int v1) lsl (to_int v2)))

let bitwise_zfshiftr v1 v2 = Const (CInt ((to_int v1) lsr (to_int v2)))

let bitwise_shiftr v1 v2 = Const (CInt ((to_int v1) asr (to_int v2)))

let string_plus v1 v2 = match v1, v2 with
  | Const (CString s1), Const (CString s2) ->
      Const (CString (s1 ^ s2))
  | _ -> raise (Throw (str "string concatenation"))

let stx_eq v1 v2 = bool begin match v1, v2 with
  | Const (CNum x1), Const (CInt x2) 
  | Const (CInt x2), Const (CNum x1) -> 
      float_of_int x2 = x1
  | Const c1, Const c2 -> c1 = c2 (* syntactic on primitives *)
  | _ -> v1 == v2 (* otherwise, pointer equality *)
end

(* Algorithm 11.9.3, steps 1 through 19. Steps 20 and 21 are desugared to
   access the heap. *)
let abs_eq v1 v2 = bool begin
  let c1 = get_const v1 in
  let c2 = get_const v2 in
    if c1 = c2 then (* works correctly on floating point values *)
      true
    else match c1, c2 with
      | CNull, CUndefined
      | CUndefined, CNull -> true
      | CString s, CNum x
      | CNum x, CString s ->
          (try x = float_of_string s with Failure _ -> false)
      | CString s, CInt n
      | CInt n, CString s ->
          (try float_of_int n = float_of_string s with Failure _ -> false)
      | CNum x, CBool b
      | CBool b, CNum x -> x = (if b then 1.0 else 0.0)
      | CInt n, CBool b
      | CBool b, CInt n -> n = (if b then 1 else 0)
      | CNum x1, CInt x2
      | CInt x2, CNum x1 -> float_of_int x2 = x1
      | _ -> false
end

let rec has_property obj field = match obj, field with
  | ObjCell o, Const (CString s) ->
      let (attrs, props) = !o in
        if (IdMap.mem s props) then bool true
        else begin try
          let proto = IdMap.find "proto" attrs in
            has_property proto field 
        with Not_found -> bool false
        end
  | _ -> bool false

let has_own_property obj field = match obj, field with
  | ObjCell o, Const (CString s) -> 
      let (attrs, props) = !o in
        bool (IdMap.mem s props)
  | _ -> raise (Throw (str "has-own-property?"))

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
  | "has-property?" -> has_property
  | "has-own-property?" -> has_own_property
  | "string+" -> string_plus
  | _ -> failwith ("no implementation of binary operator: " ^ op)

let op3 op = match op with
  | _ -> failwith ("no ternary operators yet, so what's this: " ^ op)
