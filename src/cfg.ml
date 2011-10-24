open Prelude
open Es5_cps
open Graph

type vert = cps_exp
module Vert_COMPARABLE = struct
  type t = vert
  let compare t1 t2 = Pervasives.compare t1 t2
  let hash t = Hashtbl.hash t
  let equal t1 t2 = (t1 = t2)
end

module Es5_ORDERED_TYPE_DFT = struct
  type t = Jump | IfTrue | IfFalse | Prim (* get/set field?? *)
  let default = Prim
  let compare t1 t2 = Pervasives.compare t1 t2
end

module G = Persistent.Digraph.ConcreteBidirectionalLabeled (Vert_COMPARABLE) (Es5_ORDERED_TYPE_DFT)

type env = cps_exp IdMap.t

let no_free_vars exp (env : unit IdMap.t) : bool =
  let (++) env ids = List.fold_left (fun env id -> IdMap.add id () env) env ids in
  let ($$) env ids = List.fold_left (fun ans id -> ans && IdMap.mem id env) true ids in
  let rec free_val env value : bool =
    match value with
    | Id (_, id) -> env $$ [id]
    | Lambda (_, ret, exn, params, body) -> free_exp (env ++ (ret::exn::params)) body
    | Object(_, attrs, props) ->
      let opt_val value = match value with None -> true | Some v -> free_val env v in
      List.for_all opt_val [attrs.primval; attrs.code; attrs.proto]
      && List.for_all (fun (_, v) -> match v with 
      | Data ({value = v},_,_) -> free_val env v
      | Accessor ({getter=g; setter=s},_,_) -> free_val env g && free_val env s) props
    | _ -> true
  and free_prim env prim = 
    match prim with
    | GetAttr (_, _, obj, field) -> List.for_all (free_val env) [obj; field]
    | SetAttr (_, _, obj, field, value) -> List.for_all (free_val env) [obj; field; value]
    | Op1 (_, _, arg) -> free_val env arg
    | Op2 (_, _, left, right) -> List.for_all (free_val env) [left; right]
    | DeleteField (_, obj, field) -> List.for_all (free_val env) [obj; field]
    | SetBang (_, id, value) -> (env $$ [id]) && free_val env value
  and free_exp env exp =
    match exp with
    | LetValue(_, id, value, exp) -> free_val env value && free_exp (env ++ [id]) exp
    | RecValue(_, id, value, exp) -> let env' = env ++ [id] in 
                                     free_val env' value && free_exp env' exp
    | LetPrim(_, id, prim, exp) -> free_prim env prim && free_exp (env ++ [id]) exp
    | LetRetCont(ret, arg, retBody, exp) -> free_exp (env ++ [arg]) retBody && free_exp (env ++ [ret]) exp
    | LetExnCont(exn, arg, lbl, exnBody, exp) -> free_exp (env ++ [arg;lbl]) exnBody && free_exp (env ++ [exn]) exp
    | GetField(_, obj, field, args, ret, exn) -> (env $$ [ret;exn]) && List.for_all (free_val env) [obj;field;args]
    | SetField(_, obj, field, value, args, ret, exn) -> 
      (env $$ [ret;exn]) && List.for_all (free_val env) [obj;field;value;args]
    | If(_, cond, trueBranch, falseBranch) ->
      free_val env cond && List.for_all (free_exp env) [trueBranch; falseBranch]
    | AppFun(_, func, ret, exn, args) ->
      (env $$ [ret;exn])
      && List.for_all (free_val env) (func::args)
    | AppRetCont(ret, arg) -> (env $$ [ret]) && free_val env arg
    | AppExnCont(exn, arg, label) -> (env $$ [exn;label]) && free_val env arg
    | Eval(_, eval) -> true in
  free_exp env exp


let alphatize allowUnbound (exp, env) =
  let startsWith dest prefix =
    let pLen = String.length prefix in
    String.length dest >= pLen &&
      String.sub dest 0 pLen = prefix in
  let update ((id: string), (env : int IdMap.t)) : string * int IdMap.t =
    let count = try IdMap.find id env with Not_found -> 0 in
    if (startsWith id "@_" || startsWith id "%") then
      (if (count > 0) 
       then failwith "Trying to rebind a CPS nonce"
       else (id, env))
    else (id ^ "#" ^ (string_of_int (count+1)), IdMap.add id (count+1) env) in
  let lookup (id, env) = 
    if (startsWith id "@_" || startsWith id "%")
    then id
    else try id ^ "#" ^ (string_of_int (IdMap.find id env)) with Not_found -> 
      if allowUnbound then id else failwith ("Couldn't find >" ^ id ^ "<") in
  let merge env1 env2 =
    IdMap.fold (fun id count acc ->
      let oldcount = try IdMap.find id acc with Not_found -> 0 in
      IdMap.add id (max count oldcount) acc) env1 env2 in
  
  
  let rec alph_val ((value:cps_value), (env : int IdMap.t)) =
    match value with
    | Id (p, id) -> (Id(p, lookup (id, env)), env)
    | Lambda (p, ret, exn, params, body) -> 
      let (ret', env1) = update (ret,env) in
      let (exn', env2) = update (exn,env1) in
      let (revParams', env3) = List.fold_left (fun (revParams, env) id -> 
        let (id', env') = update (id,env) in (id'::revParams, env')) ([],env2) params in
      let (body', env4) = alph_exp (body, env3) in
      (Lambda(p,ret', exn', List.rev revParams', body'), env4)
    | Object(p, attrs, props) ->
      let opt_val (value, env) = match value with 
        | None -> (value, env) 
        | Some v -> let (v', env') = alph_val (v,env) in (Some v', env') in
      let (prim', env1) = opt_val (attrs.primval, env) in
      let (code', env2) = opt_val (attrs.code, env1) in
      let (proto', env3) = opt_val (attrs.proto, env2) in
      let (revProps', env4) = List.fold_left (fun (revProps, env) (name,v) -> 
        match v with
        | Data ({value=v; writable=w},config,enum) ->
          let (v', env') = alph_val (v,env) in 
          ((name,Data({value=v';writable=w},config,enum))::revProps, env')
        | Accessor ({getter=g;setter=s},config,enum) ->
          let (g', env') = alph_val (g, env) in
          let (s', env'') = alph_val (s, env') in
          ((name,Accessor({getter=g'; setter=s'},config,enum))::revProps, env'')) ([], env3) props in
      (Object(p, 
              {primval=prim';code=code';proto=proto';klass=attrs.klass;extensible=attrs.extensible},
              List.rev revProps'), 
       env4)
    | _ -> (value, env)
  and alph_prim (prim, env) = 
    match prim with
    | GetAttr (p, pattr, obj, field) ->
      let (obj', env1) = alph_val (obj, env) in
      let (field', env2) = alph_val (field, env1) in
      (GetAttr(p, pattr, obj', field'), env2) 
    | SetAttr (p, pattr, obj, field, value) ->
      let (obj', env1) = alph_val (obj, env) in
      let (field', env2) = alph_val (field, env1) in
      let (value', env3) = alph_val (value, env2) in
      (SetAttr(p, pattr, obj', field', value'), env3) 
    | Op1 (p, op, arg) ->
      let (arg', env1) = alph_val (arg, env) in
      (Op1(p, op, arg'), env1)
    | Op2 (p, op, left, right) ->
      let (left', env1) = alph_val (left, env) in
      let (right', env2) = alph_val (right, env1) in
      (Op2(p, op, left', right'), env2)
    | DeleteField (p, obj, field) ->
      let (obj', env1) = alph_val (obj, env) in
      let (field', env2) = alph_val (field, env1) in
      (DeleteField(p, obj', field'), env2)
    | SetBang (p, id, value) ->
      let (value', env1) = alph_val (value, env) in
      (SetBang(p, lookup (id, env), value'), env1)
  and alph_exp (exp, env) = 
    match exp with 
    | LetValue (p, id, value, exp) -> 
      let (value', env1) = alph_val (value, env) in
      let (id', env2) = update (id, env1) in (* let binding happens after value *)
      let (exp', env3) = alph_exp (exp, env2) in
      (LetValue(p, id', value', exp'), env3)
    | RecValue (p, id, value, exp) ->
      let (id', env1) = update (id, env) in (* rec binding happens before value *)
      let (value', env2) = alph_val (value, env1) in
      let (exp', env3) = alph_exp (exp, env2) in
      (RecValue(p, id', value', exp'), env3)
    | LetPrim (p, id, prim, exp) ->
      let (prim', env1) = alph_prim (prim, env) in
      let (id', env2) = update (id, env1) in (* let binding happens after value *)
      let (exp', env3) = alph_exp (exp, env2) in
      (LetPrim(p, id', prim', exp'), env3)
    | LetRetCont (ret, arg, retBody, exp) ->
      let (arg', env1) = update (arg, env) in
      let (retBody', env2) = alph_exp (retBody, env1) in
      let (ret', env3) = update (ret, env) in 
      let (exp', env4) = alph_exp (exp, env3) in
      (LetRetCont(ret', arg', retBody', exp'), merge env2 env4)
    | LetExnCont (exn, arg, label, exnBody, exp) ->
      let (arg', env1) = update (arg, env) in
      let (label', env2) = update (label, env1) in
      let (exnBody', env3) = alph_exp (exnBody, env2) in
      let (exn', env4) = update (exn, env) in 
      let (exp', env5) = alph_exp (exp, env4) in
      (LetExnCont(exn', arg', label', exnBody', exp'), merge env3 env5)
    | GetField(p, obj, field, args, ret, exn) -> 
      let ret' = lookup (ret, env) in
      let exn' = lookup (exn, env) in
      let (obj', env1) = alph_val (obj, env) in
      let (field', env2) = alph_val (field, env1) in
      let (args', env3) = alph_val (args, env2) in
      (GetField(p, obj', field', args', ret', exn'), env3)
    | SetField(p, obj, field, value, args, ret, exn) -> 
      let ret' = lookup (ret, env) in
      let exn' = lookup (exn, env) in
      let (obj', env1) = alph_val (obj, env) in
      let (field', env2) = alph_val (field, env1) in
      let (value', env3) = alph_val (value, env2) in
      let (args', env4) = alph_val (args, env3) in
      (SetField(p, obj', field', value', args', ret', exn'), env4)
    | If(p, cond, trueBranch, falseBranch) -> 
      let (cond', env1) = alph_val (cond, env) in
      let (true', env2) = alph_exp (trueBranch, env1) in
      let (false', env3) = alph_exp (falseBranch, env2) in
      (If(p, cond', true', false'), env3)
    | AppFun(p, func, ret, exn, args) -> 
      let ret' = lookup (ret, env) in
      let exn' = lookup (exn, env) in
      let (func', env1) = alph_val (func, env) in
      let (revArgs', env2) = List.fold_left (fun (revArgs, env) arg -> 
        let (arg', env') = alph_val (arg,env) in (arg'::revArgs, env')) ([],env1) args in
      (AppFun(p, func', ret', exn', List.rev revArgs'), env2)
    | AppRetCont(ret, arg) -> 
      let ret' = lookup (ret, env) in
      let (arg', env1) = alph_val (arg, env) in
      (AppRetCont(ret', arg'), env1)
    | AppExnCont(exn, arg, label) -> 
      let exn' = lookup (exn, env) in
      let label' = lookup (label, env) in
      let (arg', env1) = alph_val (arg, env) in      
      (AppExnCont(exn', arg', label'), env1)
    | Eval(p, eval) -> (Eval(p, eval), env)

  in alph_exp (exp, env)

let build expr =
  let v = expr in 
  let cfg = G.add_vertex G.empty v in
  let rec build_exp (g : G.t) (env : env) (entry : vert) (exp : Es5_cps.cps_exp) : (G.t * vert) =
    match exp with
  | LetValue(pos, id, value, exp) -> (g, entry)
  | RecValue(pos, id, value, exp) -> (g, entry)
  | LetPrim(pos, id, prim, exp) -> (g, entry)
  | LetRetCont(ret, arg, retBody, exp) -> (g, entry)
  | LetExnCont(exn, arg, label, exnBody, exp) -> (g, entry)
  | GetField(pos, obj, field, args, ret, exn) -> (g, entry)
  | SetField(pos, obj, field, value, args, ret, exn) -> (g, entry)
  | If(pos, cond, trueBranch, falseBranch) -> (g, entry)
  | AppFun(pos, func, ret, exn, args) -> (g, entry)
  | AppRetCont(ret, arg) -> (g, entry)
  | AppExnCont(exn, arg, label) -> (g, entry)
  | Eval(pos, eval) -> (g, entry) in
  fst (build_exp cfg IdMap.empty v expr)

let cpsv_to_string cps_value = 
  Es5_cps_pretty.value cps_value Format.str_formatter; 
  Format.flush_str_formatter()
module Display = struct
  include G
  let vertex_name v = match v with
  | LetValue(pos, id, value, exp) -> "LetValue(" ^ id ^ ")"
  | RecValue(pos, id, value, exp) -> "RecValue(" ^ id ^ ")"
  | LetPrim(pos, id, prim, exp) -> "LetPrim(" ^ id ^ ")"
  | LetRetCont(ret, arg, retBody, exp) -> "LetRet(" ^ ret ^ ")"
  | LetExnCont(exn, arg, label, exnBody, exp) -> "LetExn(" ^ exn ^ ")"
  | GetField(pos, obj, field, args, ret, exn) -> "GetField(" ^ (cpsv_to_string obj) 
    ^ "[" ^ (cpsv_to_string field) ^ "])"
  | SetField(pos, obj, field, value, args, ret, exn) -> "SetField(" ^ (cpsv_to_string obj)
    ^ "[" ^ (cpsv_to_string field) ^ "])"
  | If(pos, cond, trueBranch, falseBranch) -> "If(" ^ (cpsv_to_string cond) ^ ")"
  | AppFun(pos, func, ret, exn, args) -> "App(" ^ (cpsv_to_string func) ^ ")"
  | AppRetCont(ret, arg) -> "Ret(" ^ ret ^ ")"
  | AppExnCont(exn, arg, label) -> "Exn(" ^ exn ^ ", " ^ label ^ ")"
  | Eval(pos, eval) -> "Eval"
  let graph_attributes _ = []
  let default_vertex_attributes _ = []
  let vertex_attributes _ = []
  let default_edge_attributes _ = []
  let edge_attributes _ = []
  let get_subgraph _ = None
end

module D = Graphviz.Dot(Display)

let print_cfg g = 
  D.fprint_graph Format.str_formatter g;
  Format.flush_str_formatter()
