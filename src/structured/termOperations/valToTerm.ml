open TermTypes
open Metatypes

(* Converts a value into an equivalent term, resolving all the free variables in
   closures into direct abstractions *)
let rec value_to_term (value : value) : term =
  match value with
  | VConst label -> Const label
  | Closure (branches, env) ->
      let converted_branches =
        List.map (substitute_abstraction_branch env 1) branches
      in
      Abstraction converted_branches

and substitute_abstraction_branch (env : environment) (depth : int)
    ((arg_type, body) : structured_type * term) =
  let substituted_body = substitute_from_env body env depth in
  (arg_type, substituted_body)

and substitute_from_env (term : term) (env : environment) (depth : int) =
  match term with
  | Abstraction branches ->
      let substituted_branches =
        List.map (substitute_abstraction_branch env (depth + 1)) branches
      in
      Abstraction substituted_branches
  | Application (left_term, right_term) ->
      Application
        ( substitute_from_env left_term env depth,
          substitute_from_env right_term env depth )
  | Const label -> Const label
  | Variable num ->
      (* If the variable references a free variable, we pull it from the env, otherwise, leave it *)
      if num - depth < 0 then Variable num
      else value_to_term (List.nth env (num - depth))
