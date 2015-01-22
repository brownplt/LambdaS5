open Util
open Ljs_new_env_clean
open OUnit2


let apply_env (s : string) = Printf.sprintf
  "let (%%ObjectProto = {[#proto : null]})
   let (%%global = {[#proto:%%ObjectProto]})
   let (%%globalContext = {[#proto: %%global, #extensible: true]})
   let (%%FunctionProto = {[#proto: %%ObjectProto, #class : 'Function', #code : func(this, args){ undefined },]
                           'length' : {#value 0, #writable true} })
    let (%%defineOwnProperty = func(a,b,c) {a[b=c]})
    let (%%functionToString = {[#code : func(this,args) {'function ToString'}, #proto: %%FunctionProto]}) 
    {
     %%FunctionProto['toString' = %%functionToString];
     %%FunctionProto['toString'<#enumerable> = false];
     {
      %%global['undefined' = undefined];
      %%global['undefined'<#enumerable> = false];
      %%global['undefined'<#configurable> = false];
      %%global['undefined'<#writable> = false];
      %%ObjectProto['propertyIsEnumerable' = func(x){x}]
     };
     let (%%escapeLambda = func(this, args) {'escape NYI'})
     let (%%escape = {[#code : %%escapeLambda, #proto : %%FunctionProto,]})
     {
      %%defineOwnProperty(%%global, 'escape',
          {[] 'value' : {#value %%escape, #writable true},
              'enumerable' : {#value false, #writable true},
              'configurable' : {#value true, #writable true},
              'writable' : {#value true, #writable true}})
     };
     %s
    }" s

let suite = 
  let cmp before after = cmp before new_env_clean after in
  let no_change code = no_change code new_env_clean in
  "Test Env Clean" >:::
  [
    "clean unused bindings" >::
    (cmp "let (x = 1)
          let (x = 2)
          x"
          "let (x = 2) x");
    
    "id clean" >::
    (cmp "let (x = func(t) {t})
          let (y = func(t) {x})
          let (z = func(t) {y})
          x"
       "let (x=func(t){t}) x"
    );
    
    "ids dependency" >::
    (no_change "let (x = func(t) {t})
                let (y = func(t) {x})
                let (z = func(t) {y})
                z");

    "clean global" >::
    (cmp (apply_env "1") "1");

    
  ]
let _ =
  run_test_tt_main suite
