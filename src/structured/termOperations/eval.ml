open TermTypes
open Typing
open TypeOperations.Subtype
open ValToTerm

(** [eval term] evaluates a term to a value *)
let rec eval (term : term) : value = eval_rec term []

and eval_rec (term : term) (env : environment) : value =
  match term with
  (* Variables simply need to be looked up from the environment *)
  | Variable num -> List.nth env num
  (* Constants are already values *)
  | Const label -> VConst label
  (* Abstractions must be bundled with their free variable environment to form a closure *)
  | Abstraction branches -> Closure (branches, env)
  (* Evaluate both sides of the application, determine the matching branch on the LHS,
     then evaluate the body of that branch with the RHS in the environment *)
  | Application (left_term, right_term) -> (
      match eval_rec left_term env with
      | Closure (left_branches, left_env) ->
          let right_value = eval_rec right_term env in
          (* TODO: can we pass the right_value here, and get the type of the value? *)
          let resolved_branch =
            resolve_branch left_branches (value_to_term right_value)
          in
          eval_rec resolved_branch (right_value :: left_env)
      | VConst _ -> raise (Invalid_argument "Cannot apply a constant"))

and resolve_branch branches argument =
  (* TODO: can I always associate a base type with arguments to guarantee I can determine
     the appropriate branch, without needing to recompute each time? *)
  let argument_type = Option.get (get_type argument) in
  let _, resolved_branch =
    List.find
      (fun (branch_type, _) -> is_subtype argument_type branch_type)
      branches
  in
  resolved_branch
