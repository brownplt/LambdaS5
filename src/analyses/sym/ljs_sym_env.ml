open Prelude

(* The "environment" is actually a stack of envs, representing
 * the call stack. The top env on the stack has the all of the
 * bindings currently in scope. *)
module Env = struct

  (* Maps var ids to store locations *)
  type env = (id * Store.loc) list
  (* Represents the envs in the call stack of the evaluator *)
  type stack = env list

  let mt_env = []
  let mt_envs = [mt_env]

  (* Functions that take advantage of the entire stack, which
   * are useful for the garbage collector and for closures. *)
  let stack_curr envs = List.hd envs
  let stack_f_curr f envs = (f (List.hd envs)) :: (List.tl envs)
  let stack_push env envs = env :: envs
  (* Returns a list of all bindings in the env stack.
   * May contain duplicates. *)
  let stack_bindings envs = List.concat envs

  (* Functions that operate on an env stack as if it were
   * just the top env on the stack. This is useful when we 
   * only care about the current scope. *)
  let lookup id envs = List.assoc id (stack_curr envs)
  let mem id envs = List.mem_assoc id (stack_curr envs)
  let add id loc envs =
    stack_f_curr (fun env -> (id, loc) :: env) envs

  (* Functions on one env *)
  let fold f env acc = (* includes shadowed bindings *)
    List.fold_right 
      (fun (id, loc) acc -> f id loc acc)
      env acc

end
