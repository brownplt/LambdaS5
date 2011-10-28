open Prelude
module C = Es5_cps
module D = Es5_cps_delta
module E = Es5_syntax
module V = Es5_cps_values
open Graph

type vert = C.cps_exp
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

type env = C.cps_exp IdMap.t

let no_free_vars exp (env : unit IdMap.t) : bool =
  let (++) env ids = List.fold_left (fun env id -> IdMap.add id () env) env ids in
  let ($$) env ids = List.fold_left (fun ans id -> ans && IdMap.mem id env) true ids in
  let rec free_val env value : bool =
    match value with
    | C.Id (_,_, id) -> env $$ [id]
    | C.Lambda (_,_, ret, exn, params, body) -> free_exp (env ++ (ret::exn::params)) body
    | C.Object(_,_, attrs, props) ->
      let opt_val value = match value with None -> true | Some v -> free_val env v in
      List.for_all opt_val [attrs.C.primval; attrs.C.code; attrs.C.proto]
      && List.for_all (fun (_, v) -> match v with
      | C.Data ({C.value = v},_,_) -> free_val env v
      | C.Accessor ({C.getter=g; C.setter=s},_,_) -> free_val env g && free_val env s) props
    | _ -> true
  and free_prim env prim =
    match prim with
    | C.GetAttr (_,_, _, obj, field) -> List.for_all (free_val env) [obj; field]
    | C.SetAttr (_,_, _, obj, field, value) -> List.for_all (free_val env) [obj; field; value]
    | C.Op1 (_,_, _, arg) -> free_val env arg
    | C.Op2 (_,_, _, left, right) -> List.for_all (free_val env) [left; right]
    | C.DeleteField (_,_, obj, field) -> List.for_all (free_val env) [obj; field]
    | C.SetBang (_,_, id, value) -> (env $$ [id]) && free_val env value
  and free_exp env exp =
    match exp with
    | C.LetValue(_,_, id, value, exp) -> free_val env value && free_exp (env ++ [id]) exp
    | C.RecValue(_,_, id, value, exp) -> let env' = env ++ [id] in
                                     free_val env' value && free_exp env' exp
    | C.LetPrim(_,_, id, prim, exp) -> free_prim env prim && free_exp (env ++ [id]) exp
    | C.LetRetCont(_,ret, arg, retBody, exp) -> free_exp (env ++ [arg]) retBody && free_exp (env ++ [ret]) exp
    | C.LetExnCont(_,exn, arg, lbl, exnBody, exp) -> free_exp (env ++ [arg;lbl]) exnBody && free_exp (env ++ [exn]) exp
    | C.If(_,_, cond, trueBranch, falseBranch) ->
      free_val env cond && List.for_all (free_exp env) [trueBranch; falseBranch]
    | C.AppFun(_,_, func, ret, exn, args) ->
      (env $$ [ret;exn])
      && List.for_all (free_val env) (func::args)
    | C.AppRetCont(_,ret, arg) -> (env $$ [ret]) && free_val env arg
    | C.AppExnCont(_,exn, arg, label) -> (env $$ [exn]) && List.for_all (free_val env) [arg;label]
    | C.Eval(_,_, eval) -> true in
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
  
  
  let rec alph_val ((value:C.cps_value), (env : int IdMap.t)) : C.cps_value * int IdMap.t =
    match value with
    | C.Id (p,l, id) -> (C.Id(p,l, lookup (id, env)), env)
    | C.Lambda (p,l, ret, exn, params, body) ->
      let (ret', env1) = update (ret,env) in
      let (exn', env2) = update (exn,env1) in
      let (revParams', env3) = List.fold_left (fun (revParams, env) id ->
        let (id', env') = update (id,env) in (id'::revParams, env')) ([],env2) params in
      let (body', env4) = alph_exp (body, env3) in
      (C.Lambda(p,l,ret', exn', List.rev revParams', body'), env4)
    | C.Object(p,l, attrs, props) ->
      let opt_val (value, env) = match value with
        | None -> (value, env)
        | Some v -> let (v', env') = alph_val (v,env) in (Some v', env') in
      let (prim', env1) = opt_val (attrs.C.primval, env) in
      let (code', env2) = opt_val (attrs.C.code, env1) in
      let (proto', env3) = opt_val (attrs.C.proto, env2) in
      let (revProps', env4) = List.fold_left (fun (revProps, env) (name,v) ->
        match v with
        | C.Data ({C.value=v; C.writable=w},config,enum) ->
          let (v', env') = alph_val (v,env) in
          ((name,C.Data({C.value=v';C.writable=w},config,enum))::revProps, env')
        | C.Accessor ({C.getter=g;C.setter=s},config,enum) ->
          let (g', env') = alph_val (g, env) in
          let (s', env'') = alph_val (s, env') in
          ((name,C.Accessor({C.getter=g'; C.setter=s'},config,enum))::revProps, env'')) ([], env3) props in
      (C.Object(p,l,
              {C.primval=prim';C.code=code';C.proto=proto';C.klass=attrs.C.klass;C.extensible=attrs.C.extensible},
              List.rev revProps'),
       env4)
    | _ -> (value, env)
  and alph_prim (prim, env) =
    match prim with
    | C.GetAttr (p,l, pattr, obj, field) ->
      let (obj', env1) = alph_val (obj, env) in
      let (field', env2) = alph_val (field, env1) in
      (C.GetAttr(p,l, pattr, obj', field'), env2)
    | C.SetAttr (p,l, pattr, obj, field, value) ->
      let (obj', env1) = alph_val (obj, env) in
      let (field', env2) = alph_val (field, env1) in
      let (value', env3) = alph_val (value, env2) in
      (C.SetAttr(p,l, pattr, obj', field', value'), env3)
    | C.Op1 (p,l, op, arg) ->
      let (arg', env1) = alph_val (arg, env) in
      (C.Op1(p,l, op, arg'), env1)
    | C.Op2 (p,l, op, left, right) ->
      let (left', env1) = alph_val (left, env) in
      let (right', env2) = alph_val (right, env1) in
      (C.Op2(p,l, op, left', right'), env2)
    | C.DeleteField (p,l, obj, field) ->
      let (obj', env1) = alph_val (obj, env) in
      let (field', env2) = alph_val (field, env1) in
      (C.DeleteField(p,l, obj', field'), env2)
    | C.SetBang (p,l, id, value) ->
      let (value', env1) = alph_val (value, env) in
      (C.SetBang(p,l, lookup (id, env), value'), env1)

  and alph_exp (exp, env) =
    match exp with
    | C.LetValue (p,l, id, value, exp) ->
      let (value', env1) = alph_val (value, env) in
      let (id', env2) = update (id, env1) in (* let binding happens after value *)
      let (exp', env3) = alph_exp (exp, env2) in
      (C.LetValue(p,l, id', value', exp'), env3)
    | C.RecValue (p,l, id, value, exp) ->
      let (id', env1) = update (id, env) in (* rec binding happens before value *)
      let (value', env2) = alph_val (value, env1) in
      let (exp', env3) = alph_exp (exp, env2) in
      (C.RecValue(p,l, id', value', exp'), env3)
    | C.LetPrim (p,l, id, prim, exp) ->
      let (prim', env1) = alph_prim (prim, env) in
      let (id', env2) = update (id, env1) in (* let binding happens after value *)
      let (exp', env3) = alph_exp (exp, env2) in
      (C.LetPrim(p,l, id', prim', exp'), env3)
    | C.LetRetCont (l,ret, arg, retBody, exp) ->
      let (arg', env1) = update (arg, env) in
      let (retBody', env2) = alph_exp (retBody, env1) in
      let (ret', env3) = update (ret, env) in
      let (exp', env4) = alph_exp (exp, env3) in
      (C.LetRetCont(l,ret', arg', retBody', exp'), merge env2 env4)
    | C.LetExnCont (l,exn, arg, label, exnBody, exp) ->
      let (arg', env1) = update (arg, env) in
      let (label', env2) = update (label, env1) in
      let (exnBody', env3) = alph_exp (exnBody, env2) in
      let (exn', env4) = update (exn, env) in
      let (exp', env5) = alph_exp (exp, env4) in
      (C.LetExnCont(l,exn', arg', label', exnBody', exp'), merge env3 env5)
    | C.If(p,l, cond, trueBranch, falseBranch) ->
      let (cond', env1) = alph_val (cond, env) in
      let (true', env2) = alph_exp (trueBranch, env1) in
      let (false', env3) = alph_exp (falseBranch, env2) in
      (C.If(p,l, cond', true', false'), env3)
    | C.AppFun(p,l, func, ret, exn, args) ->
      let ret' = lookup (ret, env) in
      let exn' = lookup (exn, env) in
      let (func', env1) = alph_val (func, env) in
      let (revArgs', env2) = List.fold_left (fun (revArgs, env) arg ->
        let (arg', env') = alph_val (arg,env) in (arg'::revArgs, env')) ([],env1) args in
      (C.AppFun(p,l, func', ret', exn', List.rev revArgs'), env2)
    | C.AppRetCont(l,ret, arg) ->
      let ret' = lookup (ret, env) in
      let (arg', env1) = alph_val (arg, env) in
      (C.AppRetCont(l,ret', arg'), env1)
    | C.AppExnCont(l,exn, arg, label) ->
      let exn' = lookup (exn, env) in
      let (arg', env1) = alph_val (arg, env) in
      let (label', env2) = alph_val (label, env1) in
      (C.AppExnCont(l,exn', arg', label'), env2)
    | C.Eval(p,l, eval) -> (C.Eval(p,l, eval), env)
  in alph_exp (exp, env)






;;

  let print_bindings env store =
    printf "Condensed bindings:\n";
    let reachableAddrs : V.ADDRESS.t list ref = ref [] in
    let rootAddrs : V.ADDRESS.t list ref = ref [] in
    let rec addReachable obj = match obj with
      | V.VarCell (_, _, a) ->
        reachableAddrs := a::!reachableAddrs;
        addReachable (Es5_cps_values.Store.find a store)
      | _ -> () in
    IdMap.iter (fun id addr ->
      rootAddrs := addr::!rootAddrs;
      let lookup = Es5_cps_values.Store.find addr store in
      addReachable lookup;
      printf "  %s -> %d -> %s\n" id addr (V.pretty_bind lookup)) env;
    List.iter (fun addr ->
      if List.mem addr !rootAddrs then ()
      else (printf "  ** -> %d -> %s\n" addr (V.pretty_bind (Es5_cps_values.Store.find addr store));
      rootAddrs := addr::!rootAddrs))
      !reachableAddrs
  let print_all_bindings env store =
    printf "Binding Env:\n";
    IdMap.iter (fun id addr -> printf "  %s -> %d\n" id addr) env;
    printf "Binding Store:\n";
    Es5_cps_values.Store.iter (fun addr value -> printf "  %d -> %s\n" addr (V.pretty_bind value)) store

  let print_rets env store = 
    printf "Condensed returns:\n";
    IdMap.iter (fun id addr -> printf "  %s -> %d" id addr;
      match (Es5_cps_values.Store.find addr store) with
      | V.Answer -> printf " -> ANS\n"
      | V.RetCont(l, arg, _, _,_,_) -> printf " -> RET(%s->...)[...]\n" arg) env
  let print_all_rets env store = 
    printf "Return Env:\n";
    IdMap.iter (fun id addr -> printf "  %s -> %d\n" id addr) env;
    printf "Return Store:\n";
    Es5_cps_values.Store.iter (fun addr ret ->
      match ret with
      | V.Answer -> printf "  %d -> ANS\n" addr
      | V.RetCont(l, arg, body, _,_,_) -> printf "  %d -> RET(%s->...)\n" addr arg
    ) store 

  let print_exns env store = 
    printf "Error Env:\n";
    IdMap.iter (fun id addr -> printf "  %s -> %d\n" id addr) env;
    printf "Error Store:\n";
    Es5_cps_values.Store.iter (fun addr ret ->
      match ret with
      | V.Error -> printf "  %d -> ERR\n" addr
      | V.ExnCont(l, arg, lbl, body, _,_,_) -> printf "  %d -> RET(%s, %s->...)\n" addr arg lbl
    ) store


type complete = Ans of V.bind_value | Err of V.bind_value
let eval (exp : C.cps_exp) =
  let newLabel = C.newLabel in
  let bool b pos = if b then V.True(pos, newLabel()) else V.False(pos, newLabel()) in
  let unbool v = match v with
    | V.True _ -> true
    | V.False _ -> false
    | _ -> failwith "tried to unbool a non-bool" in

  let rec eval_exp exp bindingEnv retContEnv exnContEnv (bindingStore : V.bind_value Es5_cps_values.Store.t) retContStore exnContStore = 
    (* print_bindings bindingEnv bindingStore; *)
    (* (match exp with *)
    (* | C.LetValue (_, l, id, _, _) -> printf "%s" ("LetValue " ^ (string_of_int l) ^ "," ^ id ^ "\n") *)
    (* | C.RecValue (_, l, id, _, _) -> printf "%s" ("RecValue " ^ (string_of_int l) ^ "," ^ id ^ "\n") *)
    (* | C.LetPrim (_, l, id, _, _) -> printf "%s" ("LetPrim " ^ (string_of_int l) ^ "," ^ id ^ "\n") *)
    (* | C.LetRetCont (l, id, _, _, _) -> printf "%s" ("LetRetCont " ^ (string_of_int l) ^ "," ^ id ^ "\n") *)
    (* | C.LetExnCont (l, id, _, _, _, _) -> printf "%s" ("LetExnCont " ^ (string_of_int l) ^ "," ^ id ^ "\n") *)
    (* | C.AppRetCont (l, id, _) -> printf "%s" ("AppRetCont " ^ (string_of_int l) ^ "," ^ id ^ "\n") *)
    (* | C.AppExnCont (l, id, _, _) -> printf "%s" ("AppExnCont " ^ (string_of_int l) ^ "," ^ id ^ "\n") *)
    (* | C.AppFun (_, l, f, r, e, a) -> printf "%s %s(Ret %s, Exn %s; %s)\n" ("AppFun " ^ (string_of_int l)) *)
    (*   (value_to_string f) r e (String.concat ", " (List.map value_to_string a)) *)
    (* | C.If(_, l, _, _, _) -> printf "%s" ("If " ^ (string_of_int l) ^ "\n") *)
    (* | C.Eval(_, l, _) -> printf "%s" ("Eval " ^ (string_of_int l) ^ "\n") *)
    (* ); *)
    match exp with
    | C.LetValue(pos, label, id, value, body) ->
      let (value, bindingStore) = eval_val value bindingEnv bindingStore retContEnv exnContEnv in
      let addr = V.ADDRESS.newAddr() in
      eval_exp body 
        (IdMap.add id addr bindingEnv) retContEnv exnContEnv 
        (Es5_cps_values.Store.add addr value bindingStore) retContStore exnContStore
    | C.RecValue(pos, label, id, value, body) ->
      let addr = V.ADDRESS.newAddr() in
      let bindingEnv' = IdMap.add id addr bindingEnv in
      let (value', bindingStore) = eval_val value bindingEnv' (Es5_cps_values.Store.add addr 
                                                 (V.Undefined(dummy_pos, newLabel()))
                                                 bindingStore) retContEnv exnContEnv in
      eval_exp body 
        bindingEnv' retContEnv exnContEnv 
        (Es5_cps_values.Store.add addr value' bindingStore) retContStore exnContStore
    | C.LetPrim(pos, label, id, prim, body) ->
      let (value, bindingStore') = eval_prim prim bindingEnv bindingStore retContEnv exnContEnv in
      let addr = V.ADDRESS.newAddr() in
      eval_exp body 
        (IdMap.add id addr bindingEnv) retContEnv exnContEnv 
        (Es5_cps_values.Store.add addr value bindingStore') retContStore exnContStore
    | C.LetRetCont(label, id, arg, body, exp) ->
      let ret = V.RetCont(label, arg, body, bindingEnv, retContEnv, exnContEnv) in
      let addr = V.ADDRESS.newAddr() in
      eval_exp exp
        bindingEnv (IdMap.add id addr retContEnv) exnContEnv
        bindingStore (Es5_cps_values.Store.add addr ret retContStore) exnContStore
    | C.AppRetCont(label, id, value) ->
      let (value', bindingStore) = eval_val value bindingEnv bindingStore retContEnv exnContEnv in
      let ret = Es5_cps_values.Store.find (IdMap.find id retContEnv) retContStore in
      begin match ret with
      | V.Answer -> 
        (match value' with
        | V.VarCell (_, _, a) -> 
          (Ans (Es5_cps_values.Store.find a bindingStore), bindingStore, retContStore, exnContStore)
        | _ ->
          (Ans value', bindingStore, retContStore, exnContStore))
      | V.RetCont (_, arg, body, bindingEnv, retContEnv, exnContEnv) ->
        let addr = V.ADDRESS.newAddr() in
        eval_exp body
          (IdMap.add arg addr bindingEnv) retContEnv exnContEnv
          (Es5_cps_values.Store.add addr value' bindingStore) retContStore exnContStore
      end
    | C.LetExnCont(label, id, arg, lbl, body, exp) ->
      let exn = V.ExnCont(label, arg, lbl, body, bindingEnv, retContEnv, exnContEnv) in
      let addr = V.ADDRESS.newAddr() in
      eval_exp exp
        bindingEnv retContEnv (IdMap.add id addr exnContEnv)
        bindingStore retContStore (Es5_cps_values.Store.add addr exn exnContStore)
    | C.AppExnCont(label, id, arg, lbl) ->
      let (arg', bindingStore) = eval_val arg bindingEnv bindingStore retContEnv exnContEnv in
      let (lbl', bindingStore) = eval_val lbl bindingEnv bindingStore retContEnv exnContEnv in
      let exn = Es5_cps_values.Store.find (IdMap.find id exnContEnv) exnContStore in
      begin match exn with
      | V.Error -> 
        (match arg' with
        | V.VarCell (_, _, a) -> 
          (Err (Es5_cps_values.Store.find a bindingStore), bindingStore, retContStore, exnContStore)
        | _ ->
          (Err arg', bindingStore, retContStore, exnContStore))
      | V.ExnCont(_, arg, lbl, body, bindingEnv, retContEnv, exnContEnv) ->
        let argAddr = V.ADDRESS.newAddr() in
        let lblAddr = V.ADDRESS.newAddr() in
        eval_exp body
          (IdMap.add arg argAddr (IdMap.add lbl lblAddr bindingEnv)) retContEnv exnContEnv
          (Es5_cps_values.Store.add argAddr arg' (Es5_cps_values.Store.add lblAddr lbl' bindingStore)) retContStore exnContStore
      end
    | C.If(pos, label, cond, left, right) ->
      let (cond', bindingStore) = eval_val cond bindingEnv bindingStore retContEnv exnContEnv in
      if unbool cond' 
      then eval_exp left bindingEnv retContEnv exnContEnv bindingStore retContStore exnContStore
      else eval_exp right bindingEnv retContEnv exnContEnv bindingStore retContStore exnContStore
    | C.AppFun(pos, label, func, ret, exn, args) ->
      let (func', bindingStore) = eval_val func bindingEnv bindingStore retContEnv exnContEnv in
      let (args', bindingStore) = List.fold_left (fun (args, bindingStore) arg -> 
        let (arg', bs) = eval_val arg bindingEnv bindingStore retContEnv exnContEnv in
        arg'::args, bs) ([],bindingStore) args in
      let args' = List.rev args' in
      let ret' = Es5_cps_values.Store.find (IdMap.find ret retContEnv) retContStore in
      let exn' = Es5_cps_values.Store.find (IdMap.find exn exnContEnv) exnContStore in
      let rec getLambda fobj = match fobj with
        | V.Closure (_, _, retArg, exnArg, argNames, body, bindingEnv,retContEnv,exnContEnv) -> 
          (retArg, exnArg, argNames, body, bindingEnv, retContEnv, exnContEnv)
        | V.Object(_, _, {V.code = Some value}, _) -> getLambda value
        | _ -> failwith "[cps-interp] applying a non-function" in
      let (retArg, exnArg, argNames, body, cBindingEnv, cRetEnv, cExnEnv) = getLambda func' in
      let retAddr = V.ADDRESS.newAddr() in
      let exnAddr = V.ADDRESS.newAddr() in
      let argAddrs = List.map (fun _ -> V.ADDRESS.newAddr()) argNames in
      let bindingEnv' = List.fold_left (fun env (name, addr) -> IdMap.add name addr env)
        cBindingEnv (List.combine argNames argAddrs) in (* NEED THE CLOSURE ENVIRONMENTS *)
      let bindingStore' = List.fold_left (fun store (addr, value) -> Es5_cps_values.Store.add addr value store)
        bindingStore (List.combine argAddrs args') in
      eval_exp body
        bindingEnv' (IdMap.add retArg retAddr cRetEnv) (IdMap.add exnArg exnAddr cExnEnv)
        bindingStore' (Es5_cps_values.Store.add retAddr ret' retContStore) (Es5_cps_values.Store.add exnAddr exn' exnContStore)
    | C.Eval _ ->
      (Err (V.Undefined(dummy_pos, newLabel())), bindingStore, retContStore, exnContStore)
  and eval_val (value : C.cps_value) env bindingStore retEnv exnEnv : (V.bind_value * Es5_cps_values.bindingStore) = match value with
    | C.Id(_, _, id) -> (Es5_cps_values.Store.find (IdMap.find id env) bindingStore, bindingStore)
    | C.Null(p,l) -> (V.Null(p,l), bindingStore)
    | C.Undefined(p,l) -> (V.Undefined(p,l), bindingStore)
    | C.String(p,l,s) -> (V.String(p,l,s), bindingStore)
    | C.Num(p,l,n) -> (V.Num(p,l,n), bindingStore)
    | C.True(p,l) -> (V.True(p,l), bindingStore)
    | C.False(p,l) -> (V.False(p,l), bindingStore)
    | C.Object(p,l,a,ps) -> 
      let opt_val v bindingStore = match v with 
        | None -> (None, bindingStore)
        | Some v -> let (ans,bs) = eval_val v env bindingStore retEnv exnEnv in (Some ans, bs) in
      let (primval, bindingStore) = opt_val a.C.primval bindingStore in
      let (code, bindingStore) = opt_val a.C.code bindingStore in
      let (proto, bindingStore) = opt_val a.C.proto bindingStore in
      let a' = { V.primval = primval; V.code = code; V.proto = proto; 
                 V.klass = a.C.klass; V.extensible = a.C.extensible } in
      let prop (props, bindingStore) (str, p) = (match p with
        | C.Data({C.value = v; C.writable = w}, enum, config) ->
          let (v, bindingStore) = eval_val v env bindingStore retEnv exnEnv in
          (str, V.Data({V.value = v; V.writable = w}, enum, config))::props, bindingStore
        | C.Accessor({C.getter = g; C.setter = s}, enum, config) -> 
          let (g, bindingStore) = eval_val g env bindingStore retEnv exnEnv in
          let (s, bindingStore) = eval_val s env bindingStore retEnv exnEnv in
          (str, V.Accessor({V.getter = g; V.setter = s}, enum, config))::props, bindingStore) in
      let (ps', bindingStore) = List.fold_left prop ([], bindingStore) ps in
      let ps' = List.rev ps' in
      let addr = V.ADDRESS.newAddr() in
      (V.VarCell(dummy_pos,newLabel(),addr), Es5_cps_values.Store.add addr (V.Object(p,l,a',ps')) bindingStore)
    | C.Lambda(p,l,r,e,a,b) -> (V.Closure(p,l,r,e,a,b,env, retEnv, exnEnv), bindingStore)
  and eval_prim (prim : C.cps_prim) env bindingStore retEnv exnEnv = 
    (* print_bindings env bindingStore; *)
    (* (let pretty_val v = Es5_cps_pretty.value v Format.str_formatter; Format.flush_str_formatter() in *)
    (*   match prim with *)
    (* | C.GetAttr(_, l, a, o, f) -> printf "%d GetAttr %s[%s<%s>]\n" l (pretty_val o) (E.string_of_attr a) (pretty_val f) *)
    (* | C.SetAttr(_, l, a, o, f, v) -> printf "%d SetAttr %s[%s<%s> = %s]\n" l (pretty_val o) (E.string_of_attr a) (pretty_val f) (pretty_val v) *)
    (* | C.DeleteField(_, l, o, f) -> printf "%d DeleteField %s[%s]\n" l (pretty_val o) (pretty_val f) *)
    (* | C.Op1(_, l, o, a) -> printf "%d Op1(%s, %s)\n" l o (pretty_val a) *)
    (* | C.Op2(_, l, o, a, b) -> printf "%d Op1(%s, %s, %s)\n" l o (pretty_val a) (pretty_val b) *)
    (* | C.SetBang(_, l, i, v) -> printf "%d Set!(%s = %s)\n" l i (pretty_val v) *)
    (* ); *)
    match prim with
    | C.GetAttr(_, _, pattr, obj, field) ->
      let (obj', bindingStore) = eval_val obj env bindingStore retEnv exnEnv in
      let obj' = match obj' with
        | V.VarCell (_, _, a) -> Es5_cps_values.Store.find a bindingStore
        | _ -> failwith "[cps-interp] set-attr didn't get a VarCell" in
      let (field', bindingStore) = eval_val field env bindingStore retEnv exnEnv in
      begin match obj', field' with
      | V.Object(pos, label, attrs, props), V.String(_, _, s) -> 
        begin 
          try
            match (List.assoc s props), pattr with
            | V.Data({ V.value = v }, _, _), E.Value -> (v, bindingStore)
            | V.Accessor({ V.getter = g }, _, _), E.Getter -> (g, bindingStore)
            | V.Accessor({ V.setter = s }, _, _), E.Setter -> (s, bindingStore)
            | V.Data(_, _, config), E.Config -> (bool config pos, bindingStore)
            | V.Accessor(_, _, config), E.Config -> (bool config pos, bindingStore)
            | V.Data(_, enum, _), E.Enum -> (bool enum pos, bindingStore)
            | V.Accessor(_, enum, _), E.Enum -> (bool enum pos, bindingStore)
            | V.Data({ V.writable = w }, _, _), E.Writable -> (bool w pos, bindingStore)
            | _ -> failwith "bad access of attribute"
          with Not_found -> failwith "Field not found"
        end
      | _ -> failwith "GetAttr didn't have both an object and a string"
      end
    | C.SetAttr(pos, label, pattr, obj, field, value) ->
      let (obj', bindingStore) = eval_val obj env bindingStore retEnv exnEnv in
      let (obj', addr) = match obj' with
        | V.VarCell (_, _, a) -> (Es5_cps_values.Store.find a bindingStore, a)
        | _ -> failwith ("[cps-interp] set-attr didn't get a VarCell: " ^ (V.pretty_bind obj')) in
      let (field', bindingStore) = eval_val field env bindingStore retEnv exnEnv in
      let (value', bindingStore) = eval_val value env bindingStore retEnv exnEnv in
      begin match obj', field' with
      | V.Object(pos, label, ({V.extensible = true} as attrs), props), V.String (_, _, s) ->
        let newprop = begin
          try 
            match (List.assoc s props), pattr with
            | V.Data ({ V.writable = true } as d, enum, config), E.Writable -> 
              V.Data ({ d with V.writable = unbool value' }, enum, config)
            | V.Data (d, enum, true), E.Writable ->
              V.Data ({ d with V.writable = unbool value' }, enum, true)
            (* Updating values only checks writable *)
            | V.Data ({ V.writable = true } as d, enum, config), E.Value ->
              V.Data ({ d with V.value = value' }, enum, config)
            (* If we had a data property, update it to an accessor *)
            | V.Data (d, enum, true), E.Setter ->
              V.Accessor ({ V.getter = V.Undefined(dummy_pos, newLabel()); V.setter = value' }, enum, true)
            | V.Data (d, enum, true), E.Getter ->
              V.Accessor ({ V.getter = value'; V.setter = V.Undefined(dummy_pos, newLabel()) }, enum, true)
            (* Accessors can update their getter and setter properties *)
            | V.Accessor (a, enum, true), E.Getter ->
              V.Accessor ({ a with V.getter = value' }, enum, true)
            | V.Accessor (a, enum, true), E.Setter ->
              V.Accessor ({ a with V.setter = value' }, enum, true)
            (* An accessor can be changed into a data property *)
            | V.Accessor (a, enum, true), E.Value ->
              V.Data ({ V.value = value'; V.writable = false; }, enum, true)
            | V.Accessor (a, enum, true), E.Writable ->
              V.Data ({ V.value = V.Undefined(dummy_pos, newLabel()); V.writable = unbool value'; }, enum, true)
            (* enumerable and configurable need configurable=true *)
            | V.Data (d, _, true), E.Enum ->
              V.Data (d, unbool value', true)
            | V.Data (d, enum, true), E.Config ->
              V.Data (d, enum, unbool value')
            | V.Data (d, enum, false), E.Config ->
              (match value' with
              | V.False _ -> V.Data (d, enum, false)
              | _ -> failwith ("[cps-interp] can't set Config property to true once it's false: " ^ s))
            | V.Accessor (a, enum, true), E.Config ->
              V.Accessor (a, enum, unbool value')
            | V.Accessor (a, enum, true), E.Enum ->
              V.Accessor (a, unbool value', true)
            | V.Accessor (a, enum, false), E.Config ->
              (match value' with 
              | V.False _ -> V.Accessor(a, enum, false)
              | _ -> failwith ("[cps-interp] can't set Config property to true once it's false: " ^ s))
            | _ -> failwith ("[cps-interp] bad property set: " ^ s)
          with Not_found ->
            let undef () = V.Undefined(pos, newLabel()) in
            match pattr with
            | E.Getter -> V.Accessor({V.getter = value'; V.setter = undef ()}, false, false)
            | E.Setter -> V.Accessor({V.getter = undef (); V.setter = value'}, false, false)
            | E.Value -> V.Data({V.value = value'; V.writable = false}, false, false)
            | E.Writable -> V.Data({V.value = undef(); V.writable = unbool value'}, false, false)
            | E.Enum -> V.Data({V.value = undef(); V.writable = false}, unbool value', true)
            | E.Config -> V.Data({V.value = undef(); V.writable = false}, true, unbool value')
        end in
        let replaceProp ((s, prop) as newProp) props =
          let rec help props acc =
            match props with
            | [] -> List.rev_append acc [newProp]
            | ((n, p) as oldProp)::props' -> if (s = n) 
              then List.rev_append acc (newProp::props')
              else help props' (oldProp::acc) in
          help props [] in
        let newobj = V.Object(pos, label, attrs, replaceProp (s, newprop) props) in
        (bool true pos, Es5_cps_values.Store.add addr newobj bindingStore)
      | V.Object(pos, label, {V.extensible = false}, props), V.String (_, _, s) -> 
        failwith "[cps-interp] extending inextensible object"
      | _ -> failwith "[cps-interp] set-attr didn't get an object and a string"
      end
    | C.Op1(_, _, op, arg) -> 
      let (arg', bindingStore) = eval_val arg env bindingStore retEnv exnEnv in
      (D.op1 op arg' bindingStore, bindingStore)
    | C.Op2(_, _, op, left, right) -> 
      let (left', bindingStore) = eval_val left env bindingStore retEnv exnEnv in
      let (right', bindingStore) = eval_val right env bindingStore retEnv exnEnv in
      (D.op2 op left' right' bindingStore, bindingStore)
    | C.DeleteField(pos, _, obj, field) -> 
      let (obj', bindingStore) = eval_val obj env bindingStore retEnv exnEnv in
      let (obj', addr) = match obj' with
        | V.VarCell (_, _, a) -> (Es5_cps_values.Store.find a bindingStore, a)
        | _ -> failwith "[cps-interp] set-attr didn't get a VarCell" in
      let (field', bindingStore) = eval_val field env bindingStore retEnv exnEnv in
      begin match obj', field' with
      | V.Object(pos, label, attrs, props), V.String (_, _, s) ->
        begin 
          try
            match (List.assoc s props) with
            | V.Data (_, _, true)
            | V.Accessor (_, _, true) ->
              let newObj = V.Object(pos, label, attrs, List.remove_assoc s props) in
              (bool true pos, Es5_cps_values.Store.add addr newObj bindingStore)
            | _ -> (bool false pos, bindingStore)
          with Not_found -> (bool false pos, bindingStore)
        end
      | _ -> failwith "DeleteField didn't have both an object and a string"
      end
    | C.SetBang(_, _, id, value) -> 
      let (value', bindingStore) = eval_val value env bindingStore retEnv exnEnv in
      let addr = IdMap.find id env in
      (* this is for binding sets
         let bindings = IdMap.find addr bindingStore in
         if (BindingSet.cardinal bindings == 1) 
         then (value', IdMap.add addr (BindingSet.singleton value') bindingStore)
         else (value', IdMap.add addr (BindingSet.add value' bindings) bindingStore) *)
      (value', Es5_cps_values.Store.add addr value' bindingStore) in
  let bindingEnv = IdMap.empty in
  let bindingStore = Es5_cps_values.Store.empty in
  let answerAddr = V.ADDRESS.newAddr() in
  let retContEnv = IdMap.add "%answer" answerAddr IdMap.empty in
  let retContStore = Es5_cps_values.Store.add answerAddr V.Answer Es5_cps_values.Store.empty in
  let errorAddr = V.ADDRESS.newAddr() in
  let exnContEnv = IdMap.add "%error" errorAddr IdMap.empty in
  let exnContStore = Es5_cps_values.Store.add errorAddr V.Error Es5_cps_values.Store.empty in
  let (ans, _, _, _) = (eval_exp exp bindingEnv retContEnv exnContEnv bindingStore retContStore exnContStore) in
  ans





















(* module type STORABLE = sig *)
(*   type t *)
(*   val compare : t -> t -> int *)
(*   val equal : t -> t -> bool *)
(* end *)
(* module Storable = struct *)
(*   type t =  *)
(*     | RetCont of label * id * cps_exp *)
(*     | ExnCont of label * id * id * cps_exp *)
(*     | Value of Es5_cps.cps_value *)
(*   let compare = Pervasives.compare *)
(*   let equal t1 t2 = match (t1, t2) with *)
(*     | RetCont(l1, _, _), RetCont(l2, _, _) -> l1 = l2 *)
(*     | ExnCont(l1, _, _, _), ExnCont(l2, _, _, _) -> l1 = l2 *)
(*     | Value v1, Value v2 -> v1 = v2 *)
(*     | _ -> false *)
(* end *)
  
(* module Labeled_Exp = struct *)
(*   type t = cps_exp *)
(*   let initial_env : Storable.t IdMap.t = *)
(*     let id id = Id(dummy_pos, newLabel(), id) in *)
(*     List.fold_left (fun map (key,value) -> IdMap.add key value map) *)
(*       IdMap.empty *)
(*       [("%answer",  *)
(*         let arg = newVar "arg" in *)
(*         Storable.RetCont(newLabel(), arg, *)
(*                          LetPrim(dummy_pos, newLabel(), newVar "",  *)
(*                                  Op1(dummy_pos, newLabel(), "print", id arg), *)
(*                                  AppFun(dummy_pos, newLabel(), id "%answer", arg, "", [])))); *)
(*        ("%error", *)
(*         let arg = newVar "arg" in *)
(*         let lab = newVar "lab" in  *)
(*         Storable.ExnCont(newLabel(), arg, lab, *)
(*                          LetPrim(dummy_pos, newLabel(), newVar "", *)
(*                                  Op1(dummy_pos, newLabel(), "print", id arg), *)
(*                                  AppFun(dummy_pos, newLabel(), id "%error", arg, lab, []))))] *)
(*   let compare = Pervasives.compare *)
(* end *)
(* module type LABELED_EXP = sig *)
(*   type t *)
(*   val initial_env : Storable.t IdMap.t *)
(*   val compare : t -> t -> int *)
(* end *)
(* module type ENV = sig *)
(*   type t *)
(*   val empty : t *)
(* end *)
(* module type ADDR = sig *)
(*   type t *)
(*   type state *)
(*   type kont *)
(*   val compare : t -> t -> int *)
(*   val alloc : state -> kont -> kont -> t *)
(*   val newAddr : unit -> t *)
(* end *)
(* module type TIME = sig *)
(*   type t *)
(*   type state *)
(*   type kont *)
(*   val start_time : t *)
(*   val tick : state -> kont -> kont -> t *)
(* end *)

(* module K_CFA_TIME : TIME = struct *)
(*   type kont = Mt | Prim | App | Ret | Exn | Label of label *)
(*   type t = kont * label list *)
(*   type state = (cps_exp * t) *)
(*   let start_time = (Mt, []) *)
(*   let truncate list n = *)
(*     let rec helper list n acc = *)
(*       match n, list with *)
(*       | 0, _ -> List.rev acc *)
(*       | _, [] -> List.rev acc *)
(*       | _, hd::tl -> helper tl (n-1) (hd::acc) *)
(*     in helper list n [] *)
(*   let tick (e, (l, delta)) k h = (l, delta) *)
(* (\*    match e with *)
(*     | LetValue *)
(*     | RecValue *)
(*     | LetPrim *)
(*     | LetRetCont *)
(*     | LetExnCont *)
(*     | If *)
(*     | AppFun *)
(*     | AppRetCont *)
(*     | AppExnCont *)
(*     | Eval *\) *)
(* end *)



(* module ABS_STORE = struct *)
(*   module type S = sig *)
(*     type t *)
(*     type addr *)
(*     type storable *)
(*     val equal : t -> t -> bool *)
(*     val empty : t *)
(*     val join  : t -> t -> t *)
(*     val add : addr -> storable -> t -> t *)
(*   end *)
(*   module Make (Addr : ADDR) (Storable : STORABLE) = struct *)
(*     type addr = Addr.t *)
(*     type storable = Storable.t *)
(*     module StorableSet = Set.Make (Storable) *)
(*     module AddrMap = Map.Make (StorableSet) *)
(*     type t = StorableSet.t AddrMap.t *)
(*     let equal store1 store2 = AddrMap.equal Storable.equal store1 store2 *)
(*     let empty = AddrMap.empty *)
(*     let add a v t = *)
(*       try *)
(*         let curBindings = AddrMap.find a t in *)
(*         let newBindings = StorableSet.add v curBindings in *)
(*         AddrMap.add a newBindings t *)
(*       with Not_found -> *)
(*         AddrMap.add a (StorableSet.singleton v) t *)
(*     let join store1 store2 = AddrMap.fold add store1 store2 *)

(*   end *)
(* end *)

(* module System *)
(*   (Exp : LABELED_EXP) *)
(*   (Env : ENV)  *)
(*   (Addr : ADDR)  *)
(*   (Time : TIME) *)
(*   (Store : ABS_STORE.S with type addr = Addr.t with type storable = Storable.t) = struct *)
(*   module State = struct *)
(*     type t = Exp.t * Env.t * Addr.t * Addr.t * Time.t *)
(*     let compare = Pervasives.compare *)
(*   end *)
(*   module StateSet = Set.Make (State) *)

(*   module S = struct *)
(*     type t = State.t * Store.t *)
(*     let compare = Pervasives.compare *)
(*   end *)
(*   module SystemSet = Set.Make (S) *)

(*   let step ((state : State.t), (store : Store.t)) = (state, store) (\* for now *\) *)

(*   type t = StateSet.t * Store.t *)

(*   let inject (e : Exp.t) : State.t * Store.t = *)
(*     let answer = Addr.newAddr()  in *)
(*     let error = Addr.newAddr() in *)
(*     let initialStore = *)
(*       Store.add answer (IdMap.find "%answer" Exp.initial_env) *)
(*         (Store.add error (IdMap.find "%error" Exp.initial_env) *)
(*            Store.empty) in     *)
(*     ((e, Env.empty, answer, error, Time.start_time), initialStore) *)

(*   let aval e = *)
(*     let rec lfp (f : 'help -> t -> ('help * t)) (help : 'help) (state, store) : t = *)
(*       let (help', (state', store')) = f help (state, store) in *)
(*       if (StateSet.equal state state' && Store.equal store store') *)
(*       then (state', store') *)
(*       else lfp f help' (state', store') in *)
(*     let (c_0, sigma_0) = inject e in *)
(*     let _C_0 = StateSet.singleton c_0 in *)
(*     let nextStep (worklist : StateSet.t) ((_C : StateSet.t), (sigma : Store.t)) = *)
(*       let _Q' = StateSet.fold (fun (state : State.t) (curSys : SystemSet.t) ->  *)
(*         SystemSet.add (step (state, sigma)) curSys) worklist SystemSet.empty in *)
(*       let (_C'', sigma'') = SystemSet.fold (fun (state', sigma') (curState, curStore) -> *)
(*         (StateSet.add state' curState, Store.join sigma' curStore)) _Q' (StateSet.empty, sigma) in *)
(*       let _C' = StateSet.union _C _C'' in *)
(*       (_C'', (_C', sigma'')) in *)
(*     lfp nextStep _C_0 (_C_0, sigma_0) *)
(* end *)

let build expr =
  let v = expr in
  let cfg = G.add_vertex G.empty v in
  let rec build_exp (g : G.t) (env : env) (entry : vert) (exp : Es5_cps.cps_exp) : (G.t * vert) =
    match exp with
  | C.LetValue(pos,l, id, value, exp) -> (g, entry)
  | C.RecValue(pos,l, id, value, exp) -> (g, entry)
  | C.LetPrim(pos,l, id, prim, exp) -> (g, entry)
  | C.LetRetCont(l,ret, arg, retBody, exp) -> (g, entry)
  | C.LetExnCont(l,exn, arg, label, exnBody, exp) -> (g, entry)
  | C.If(pos,l, cond, trueBranch, falseBranch) -> (g, entry)
  | C.AppFun(pos,l, func, ret, exn, args) -> (g, entry)
  | C.AppRetCont(l,ret, arg) -> (g, entry)
  | C.AppExnCont(l,exn, arg, label) -> (g, entry)
  | C.Eval(pos,l, eval) -> (g, entry) in
  fst (build_exp cfg IdMap.empty v expr)

let cpsv_to_string cps_value =
  Es5_cps_pretty.value cps_value Format.str_formatter;
  Format.flush_str_formatter()
module Display = struct
  include G
  let vertex_name v = match v with
  | C.LetValue(pos,l, id, value, exp) -> "LetValue(" ^ id ^ ")"
  | C.RecValue(pos,l, id, value, exp) -> "RecValue(" ^ id ^ ")"
  | C.LetPrim(pos,l, id, prim, exp) -> "LetPrim(" ^ id ^ ")"
  | C.LetRetCont(l,ret, arg, retBody, exp) -> "LetRet(" ^ ret ^ ")"
  | C.LetExnCont(l,exn, arg, label, exnBody, exp) -> "LetExn(" ^ exn ^ ")"
  | C.If(pos,l, cond, trueBranch, falseBranch) -> "If(" ^ (cpsv_to_string cond) ^ ")"
  | C.AppFun(pos,l, func, ret, exn, args) -> "App(" ^ (cpsv_to_string func) ^ ")"
  | C.AppRetCont(l,ret, arg) -> "Ret(" ^ ret ^ ")"
  | C.AppExnCont(l,exn, arg, label) -> "Exn(" ^ exn ^ ", " ^ (cpsv_to_string label) ^ ")"
  | C.Eval(pos,l, eval) -> "Eval"
  let graph_attributes _ = []
  let default_vertex_attributes _ = []
  let vertex_attributes _ = []
  let default_edge_attributes _ = []
  let edge_attributes _ = []
  let get_subgraph _ = None
end

module Dot = Graphviz.Dot(Display)

let print_cfg g =
  Dot.fprint_graph Format.str_formatter g;
  Format.flush_str_formatter()
