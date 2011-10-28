open Prelude
open Es5_cps

module ADDRESS = struct
  type t = int
  let newAddr =
    let nextAddr = ref 0 in
    (fun () -> incr nextAddr; !nextAddr)
  let compare = Pervasives.compare
end
type retContEnv = ADDRESS.t IdMap.t
type exnContEnv = ADDRESS.t IdMap.t
type bindingEnv = ADDRESS.t IdMap.t



type bind_value =
  | Null of pos * label
  | Undefined of pos * label
  | String of pos * label * string
  | Num of pos * label * float
  | True of pos * label
  | False of pos * label
  | Object of pos * label * bind_attrs * (string * bind_prop) list
  | Closure of pos * label * id * id * id list * cps_exp * bindingEnv * retContEnv * exnContEnv
and bind_attrs =
    { primval : bind_value option;
      code : bind_value option;
      proto : bind_value option;
      klass : string;
      extensible : bool; }
and bind_prop =
  | Data of data_bind_value * bool * bool
  | Accessor of accessor_bind_value * bool * bool
and data_bind_value =       
    {value : bind_value;
     writable : bool; }
and accessor_bind_value =       
    {getter : bind_value;
     setter : bind_value; }



let rec pretty_bind v = match v with 
  | Num (_, _, d) -> string_of_float d
  | String (_, _, s) -> "\"" ^ s ^ "\""
  | True _ -> "true"
  | False _ -> "false"
  | Undefined _ -> "undefined"
  | Null _ -> "null"
  | Closure (_, _, ret, exn, args, body, _,_,_) -> "Closure(Ret " ^ ret ^ " , Exn " ^ exn ^ " ; " 
        ^ String.concat " , " args ^ ") { ... }"
  | Object (_, _, _, props) -> "{" ^ String.concat ", " (List.map (fun (k, p) ->
    match p with
    | Data({value = v}, _, _) -> k ^ ": " ^ (pretty_bind v) 
    | Accessor _ -> k ^ ": get/set"
  ) props) ^ "}"


module BINDING = struct
  type t = bind_value
  let compare = Pervasives.compare
end
module BindingSet = Set.Make (BINDING)
module Store = Map.Make (ADDRESS)

type retCont = 
  | Answer
  | RetCont of label * id * cps_exp * bindingEnv * retContEnv * exnContEnv
type exnCont = 
  | Error
  | ExnCont of label * id * id * cps_exp * bindingEnv * retContEnv * exnContEnv
module RET_CONT = struct
  type t = retCont
  let compare = Pervasives.compare
end
module RetContSet = Set.Make (RET_CONT)
module EXN_CONT = struct
  type t = exnCont
  let compare = Pervasives.compare
end
module ExnContSet = Set.Make (EXN_CONT)

type retContStore = RET_CONT.t Store.t
type exnContStore = EXN_CONT.t Store.t
type bindingStore = BINDING.t Store.t  (* for now these are not sets *)
