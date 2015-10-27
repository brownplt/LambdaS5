open Prelude
module S = Ljs_syntax

let ids = [
  "%LeftShift";
  "%SyntaxError";
  "%PostIncrement";
  "%propertyNames";
  "%defineGlobalAccessors";
  "%UnaryPlus";
  "%SignedRightShift";
  "%defineGlobalVar";
  "%LessThan";
  "%FunctionProto";
  "%ToBoolean";
  "%BitwiseNot";
  "%LessEqual";
  "%UnsignedRightShift";
  "%PrefixDecrement";
  "%PropAccessorCheck";
  "%ThrowTypeError";
  "%PrimAdd";
  "%EnvCheckAssign";
  "%nonstrictContext";
  "%RegExpGlobalFuncObj";
  "%BitwiseInfix";
  "%makeWithContext";
  "%UnaryNeg";
  "%ToString";
  "%strictContext";
  "%PrefixIncrement";
  "%set-property";
  "%resolveThis";
  "%GreaterThan";
  "%this";
  "%Typeof";
  "%GreaterEqual";
  "%PrimMultOp";
  "%ThrowSyntaxError";
  "%instanceof";
  "%mkArgsObj";
  "%mkNewArgsObj";
  "%ToObject";
  "%PostDecrement";
  "%PrimSub";
  "%IsObject";
  "%TypeError";
  "%ObjectProto";
  "%maybeDirectEval";
  "%in";
  "%ArrayProto";
  "%EqEq";
  "%ToJSError";
  "%ErrorDispatch"
]

let id_obj = S.Object (
    Pos.dummy,
    S.d_attrs,
    (* Add each id as a writable field; some things (like eval)
       want to be able to update this list *)
    List.fold_right (fun s props ->
      (s, (S.Data ({
        S.value=S.Id (Pos.dummy, s);
        S.writable=true
      }, false, false))) :: props) ids []
  )

let vars_env exp = S.Seq (
    Pos.dummy,
    S.SetBang (Pos.dummy, "%makeGlobalEnv",
      S.Lambda (Pos.dummy, [], id_obj)),
    exp
  )

let env_var p s =
  if List.mem s ids
  then S.Id (Pos.synth p, s)
  else failwith ("[desugar] Attempted to use unbound id " ^ s ^
                   " in env_var.  Add it to env_free_vars.ml")
                
(* dummy_env is initially used for replace env_var when flag
 * -internal-env is used with optimization flags. *)
let dummy_env exp = S.Seq (Pos.dummy, S.Undefined Pos.dummy, exp)
