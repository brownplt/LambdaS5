open Prelude
open Es5_cps
module F = Format
module FX = FormatExt

module ADDRESS : sig
  type t
  val newAddr : unit -> t
  val compare : t -> t -> int
  val addrForContour : Label.t list -> t
  val resetForContour : Label.t list -> unit
  val pretty : t -> FX.printer
  val toString : t -> string
end = struct
  module IntList = struct
    type t = int list
    let compare = Pervasives.compare
  end
  module IntListMap = Map.Make(IntList)
  type t = (int list * int)
  let nextAddr : int ref IntListMap.t ref = ref IntListMap.empty
  let compare = Pervasives.compare
  let takeFst l = match l with
    | [] -> []
    | hd::_ -> [hd]
  let addrForContour c = 
    let truncC = takeFst c in
    let nextAddrRef = 
      try
        IntListMap.find truncC !nextAddr 
      with Not_found ->
        let addr = ref 0 in
        nextAddr := IntListMap.add truncC addr !nextAddr;
        addr in
    (incr nextAddrRef;
     (truncC, !nextAddrRef))
  let newAddr () = addrForContour []
  let resetForContour c = 
    let truncC = takeFst c in
    try
      let addr = IntListMap.find truncC !nextAddr in
      addr := 0
    with Not_found -> ()
  let pretty (c, n) = FX.horz [FX.squish [FX.brackets (FX.horz (List.map FX.int c)); FX.text ";"; FX.int n]]
  let toString a = pretty a F.str_formatter; F.flush_str_formatter()
end
type retContEnv = ADDRESS.t IdMap.t
type exnContEnv = ADDRESS.t IdMap.t
type bindingEnv = ADDRESS.t IdMap.t



type bind_value =
  | Null of pos * Label.t
  | Undefined of pos * Label.t
  | String of pos * Label.t * string
  | Num of pos * Label.t * float
  | True of pos * Label.t
  | False of pos * Label.t
  | VarCell of pos * Label.t * ADDRESS.t
  | Object of pos * Label.t * bind_attrs * (string * bind_prop) list
  | Closure of pos * Label.t * id * id * id list * cps_exp * bindingEnv * retContEnv * exnContEnv
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
  | VarCell (_, _, a) -> "*<" ^ (ADDRESS.toString a) ^ ">"
  | Object (_, _, _, props) -> "{" ^ String.concat ", " (List.map (fun (k, p) ->
    match p with
    | Data({value = v}, _, _) -> k ^ ": " ^ (pretty_bind v) 
    | Accessor _ -> k ^ ": get/set"
  ) props) ^ "}"


(* module BINDING = struct *)
(*   type t = bind_value *)
(*   let compare = Pervasives.compare *)
(* end *)
(* module BindingSet = Set.Make (BINDING) *)
module Store = Map.Make (ADDRESS)

type retCont = 
  | Answer
  | RetCont of Label.t * id * cps_exp * bindingEnv * retContEnv * exnContEnv
type exnCont = 
  | Error
  | ExnCont of Label.t * id * id * cps_exp * bindingEnv * retContEnv * exnContEnv

let pretty_retcont ret = match ret with
  | Answer -> "Answer"
  | RetCont (label, arg, _, _, _, _) -> (string_of_int label) ^ ":RetCont(" ^ arg ^ ") {...}"
let pretty_exncont exn = match exn with
  | Error -> "Error"
  | ExnCont (label, arg, lbl, _, _, _, _) -> (string_of_int label) ^ ":ExnCont(" ^ arg ^ ", " ^ lbl ^ ") {...}"

(* module RET_CONT = struct *)
(*   type t = retCont *)
(*   let compare = Pervasives.compare *)
(* end *)
(* module RetContSet = Set.Make (RET_CONT) *)
(* module EXN_CONT = struct *)
(*   type t = exnCont *)
(*   let compare = Pervasives.compare *)
(* end *)
(* module ExnContSet = Set.Make (EXN_CONT) *)

type retContStore = retCont Store.t
type exnContStore = exnCont Store.t
type bindingStore = bind_value Store.t  (* for now these are not sets *)
