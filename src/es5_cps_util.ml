open Prelude
module C = Es5_cps
module D = Es5_cps_delta
module E = Es5_syntax
module V = Es5_cps_values
open Graph
open Format
open FormatExt

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
    try 
      let lookup = Es5_cps_values.Store.find addr store in
      addReachable lookup;
      printf "  %s -> %d -> %s\n" id addr (V.pretty_bind lookup)
    with _ -> printf "  %s -> %d -> XXX dangling pointer XXX\n" id addr) env;
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



let dump_heap_as_dot prefix bindingEnv bindingStore retEnv retStore exnEnv exnStore =
  let indent n inner = horz [ squish [ text (String.make n ' '); inner]] in
  let group_with_comment n c b = vert [horz [text "{ /*"; horz c; text "*/"]; 
                                       indent n (vert b);
                                       text "}"] in
  (* let escape str =  *)
  (*   let lt = Str.global_replace (Str.regexp "<") "&lt;" in *)
  (*   let gt = Str.global_replace (Str.regexp ">") "&gt;" in *)
  (*   let amp = Str.global_replace (Str.regexp "&") "&amp;" in *)
  (*   text (lt (gt (amp str))) in *)
  let bindMap = Es5_cps_values.Store.fold (fun addr value acc -> 
    let (b,r,e) = match value with
    | V.Closure(_, _, _, _, _, _, binds, rets, exns) -> (binds, rets, exns)
    | V.VarCell (_, _, ptr) -> (IdMap.singleton "dummy" ptr, IdMap.empty, IdMap.empty)
    | _ -> (IdMap.empty, IdMap.empty, IdMap.empty) in
    (addr, V.pretty_bind value, b,r,e)::acc) bindingStore [] in
  let retsMap = Es5_cps_values.Store.fold (fun addr ret acc -> match ret with 
    | V.Answer -> (addr, "ANSWER", IdMap.empty, IdMap.empty, IdMap.empty)::acc
    | V.RetCont(_, arg, _, b, r, s) -> (addr, "RET("^arg^"->...)", b, r, s)::acc) retStore [] in
  let exnsMap = Es5_cps_values.Store.fold (fun addr ret acc -> match ret with 
    | V.Error -> (addr, "ERROR", IdMap.empty, IdMap.empty, IdMap.empty)::acc
    | V.ExnCont(_, arg, lbl, _, b, r, s) -> (addr, "RET("^arg^", "^lbl^"->...)", b, r, s)::acc) exnStore [] in
  (* let fmt_bindings name env envName = *)
  (*   let bindRecord = IdMap.fold (fun id _ acc -> *)
  (*     (horz [squish [text "<TR><TD PORT=\""; text id; text "\">";  *)
  (*                    text id; text "</TD></TR>"]]) :: *)
  (*       acc *)
  (*   ) env [] in *)
  (*   vert [vert [horz[text name; text "[label=<"]; *)
  (*               vert [text "<TABLE BORDER=\"0\" CELLBORDER=\"0\" CELLSPACING=\"0\">"; *)
  (*                     indent 2 (vert (List.rev bindRecord)); *)
  (*                     text "</TABLE>"]; *)
  (*               text ">];"]; *)
  (*         vert (IdMap.fold (fun id addr acc -> *)
  (*           horz [squish [text name; text ":\""; text id; text "\" -> ";  *)
  (*                         text envName; text ":"; int addr; text ";"]] ::  *)
  (*             acc) env [])] in *)
  let fmt_bindings name env envName =
    let bindRecord = IdMap.fold (fun id addr acc ->
      (horz [squish [text "{rank=same ";
                     text "\""; text name; text "_"; text id; text "\" [label=\""; text id; text "\",";
                     text "group="; text name; text "]";
                     text envName; text "_"; int addr; text ";"]])::
        (horz [squish [text "\""; text name; text "_"; text id; text "\" -> ";
                      text envName; text "_"; int addr; text ";}"]])::acc)
      env [] in
    group_with_comment 2 [text name; text "bindings"] bindRecord in
  (* let fmt_env name map = *)
  (*   let envRecord = (List.rev_map (fun (addr, _, _, _, _) ->  *)
  (*     horz [squish [text "<TR><TD PORT=\""; int addr; text "\">";  *)
  (*                   int addr;  *)
  (*                   text "</TD></TR>"]]) map) in *)
  (*   vert [horz[text name; text "[label=<"]; *)
  (*         vert [text "<TABLE BORDER=\"0\" CELLBORDER=\"1\" CELLSPACING=\"0\">"; *)
  (*               indent 2 (horz [text "<TR><TD BORDER=\"0\">"; text name; text "</TD></TR>"]); *)
  (*               indent 2 (vert envRecord); *)
  (*               text "</TABLE>"]; *)
  (*         text ">];"] in *)
  let fmt_env name map =
    let envRecord = List.rev_map (fun (addr, _, _, _, _) ->
      horz [squish [text "\""; text name; text "_"; int addr; text "\" ";
                    text "[label=\""; text name; int addr; 
                    text "\",shape=box,group="; text name; text "];"]]) map in
    let edges = match map with
      | []
      | [_] -> [text "/* No edges needed */"]
      | (first, _, _, _, _)::tl -> (snd (List.fold_left (fun (prev,acc) (addr, _, _, _, _) ->
        (addr, (horz [squish [text "\""; text name; text "_"; int addr; text "\" -> ";
                              text "\""; text name; text "_"; int prev; text "\" [weight=100,style=\"invis\"];"]])::acc))
                                           (first,[]) tl)) in
    vert [group_with_comment 2 [text name; text "environment"] envRecord;
          group_with_comment 2 [text name; text "ordering edges"] edges
          ] in
  let fmt_store name map envName =
      (* horz [squish [text "<TR><TD PORT=\""; int addr; text "\">"; *)
      (*               escape value; *)
      (*               text "</TD></TR>"]]) map) in *)
    let storeRecord = (List.rev_map (fun (addr, value, bindings, rets, exns) ->
      horz [squish [text "\""; text name; text "_"; int addr; text "\" [label=\"";
                    text value;
                    text "\",shape=box,group="; text name; text "]"]]) map) in
    let edges = match map with
      | []
      | [_] -> [text "/* No edges needed */"]
      | (first, _, _, _, _)::tl -> (snd (List.fold_left (fun (prev,acc) (addr, _, _, _, _) ->
        (addr, (horz [squish [text "\""; text name; text "_"; int addr; text "\" -> ";
                              text "\""; text name; text "_"; int prev; text "\" [weight=100,style=\"invis\"];"]])::acc))
                                           (first,[]) tl)) in
    let ranks = match map with
      | [] -> [text "/* No ranks needed */"]
      | _ -> List.rev_map (fun (addr, _, _, _, _) ->
        horz [squish [text "{rank=same; "; 
                      text envName; text "_"; int addr; text "; ";
                      text name; text "_"; int addr; text "; ";
                      text envName; text "_"; int addr; text " -> ";
                      text name; text "_"; int addr; text " [weight=100]; }"]]) map in
    (* vert [vert [horz[text name; text "[label=<"]; *)
    (*             vert [text "<TABLE BORDER=\"0\" CELLBORDER=\"1\" CELLSPACING=\"0\">"; *)
    (*                   indent 2 (horz [text "<TR><TD BORDER=\"0\">"; text name; text "</TD></TR>"]); *)
    (*                   indent 2 (vert storeRecord); *)
    (*                   text "</TABLE>"]; *)
    (*             text ">];"]; *)
    vert [group_with_comment 2 [text "bindings"] storeRecord;
          group_with_comment 2 [text "bindings ordering edges"] edges;
          group_with_comment 2 [text "bindings same rank as bindingEnv"] ranks;
          group_with_comment 2 [text "bindings dependencies"] 
            (List.flatten (List.rev_map (fun (addr, _, bindings, _, _) ->
              (IdMap.fold (fun _ addr2 acc ->
                horz [squish [text "\""; text name; text "_"; int addr; text "\" -> ";
                              text "\""; text envName; text "_"; int addr2; text "\"";
                              text " [color=blue];"]] :: 
                  acc) bindings [])) map))
         ] in
  let fmt_conts name map rankEnvName bindEnvName retEnvName exnEnvName =
    let storeRecord = (List.rev_map (fun (addr, value, bindings, rets, exns) ->
      horz [squish [text "\""; text name; text "_"; int addr; text "\" [label=\"";
                    text value;
                    text "\",shape=box,group="; text name; text "]"]]) map) in
    let edges = match map with
      | []
      | [_] -> [text "/* No edges needed */"]
      | (first, _, _, _, _)::tl -> (snd (List.fold_left (fun (prev,acc) (addr, _, _, _, _) ->
        (addr, (horz [squish [text "\""; text name; text "_"; int addr; text "\" -> ";
                              text "\""; text name; text "_"; int prev; text "\" [weight=100,style=\"invis\"];"]])::acc))
                                           (first,[]) tl)) in
    let ranks = match map with
      | [] -> [text "/* No ranks needed */"]
      | _ -> List.rev_map (fun (addr, _, _, _, _) ->
        horz [squish [text "{rank=same; "; 
                      text rankEnvName; text "_"; int addr; text "; ";
                      text name; text "_"; int addr; text "; ";
                      text rankEnvName; text "_"; int addr; text " -> ";
                      text name; text "_"; int addr; text " [weight=100]; }"]]) map in
    vert [group_with_comment 2 [text name] storeRecord;
          group_with_comment 2 [text name; text "ordering edges"] edges;
          group_with_comment 2 [text name; text "same rank as"; text rankEnvName] ranks;
          group_with_comment 2 [text name; text "references"]
            (List.flatten (List.flatten (List.rev_map (fun (addr, _, bindings, rets, exns) ->
              [(IdMap.fold (fun _ addr2 acc ->
                horz [squish [text "\""; text name; text "_"; int addr; text "\" -> ";
                              text "\""; text bindEnvName; text "_"; int addr2; text "\"";
                              text " [color=purple];"]] :: 
                  acc) bindings []);
               (IdMap.fold (fun _ addr2 acc ->
                 horz [squish [text "\""; text name; text "_"; int addr; text "\" -> ";
                               text "\""; text retEnvName; text "_"; int addr2; text "\"";
                               text " [color=green];"]] :: 
                   acc) rets []);
               (IdMap.fold (fun _ addr2 acc ->
                 horz [squish [text "\""; text name; text "_"; int addr; text "\" -> ";
                               text "\""; text exnEnvName; text "_"; int addr2; text "\"";
                               text " [color=red];"]] :: 
                   acc) exns [])]) map)))
         ] in
    
          
  vert [horz[text "digraph heap {"];
        indent 2 (vert [horz [text "subgraph"; text prefix; text "{"];
                        indent 2
                          (vert [text "node [shape=plaintext]";
                                 fmt_env (prefix ^ "bindings") bindMap;
                                 fmt_bindings (prefix ^ "bindEnv") bindingEnv (prefix ^ "bindings");
                                 fmt_store (prefix ^ "bindMap") bindMap (prefix ^ "bindings");
                                 fmt_env (prefix ^ "retConts") retsMap;
                                 fmt_bindings (prefix ^ "retEnv") retEnv (prefix ^ "retConts");
                                 fmt_conts (prefix ^ "retEnv") retsMap (prefix ^ "retConts") (prefix ^ "bindings") (prefix ^ "retConts") (prefix ^ "exnConts");
                                 fmt_env (prefix ^ "exnConts") exnsMap;
                                 fmt_bindings (prefix ^ "exnEnv") exnEnv (prefix ^ "exnConts");
                                 fmt_conts (prefix ^ "exnEnv") exnsMap (prefix ^ "exnConts") (prefix ^ "bindings") (prefix ^ "retConts") (prefix ^ "exnConts")]);
                       text "}"]);
        horz[text "}"]]
