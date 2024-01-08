open TermTypes
open Typing
open TypeOperations.Subtype
open ValToTerm
open SubstituteUnivVar

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
  (* Universal quantifiers are themselves values *)
  | UnivQuantifier inner_term -> VUnivQuantifier inner_term
  (* Evaluate both sides of the application, determine the matching branch on the LHS,
     then evaluate the body of that branch with the RHS in the environment *)
  | Application (left_term, right_term) -> (
      match eval_rec left_term env with
      | Closure (left_branches, left_env) ->
          let right_value = eval_rec right_term env in
          let resolved_branch =
            resolve_branch left_branches (value_to_term right_value)
          in
          eval_rec resolved_branch (right_value :: left_env)
      | VConst _ -> raise (Invalid_argument "Cannot apply a constant")
      | VUnivQuantifier _ ->
          raise (Invalid_argument "Cannot apply a universal quantifier"))
  (* Perform implicit substitution with universal quantifier application for simplicity *)
  | UnivApplication (app_term, app_type) ->
    match eval_rec app_term env with
    | VUnivQuantifier inner_term ->
      let substituted_inner_term = substitute_univ_var_term app_type inner_term in
      eval_rec substituted_inner_term env
    | VConst _ -> raise (Invalid_argument "Cannot perform universal application on a constant")
    | Closure _ -> raise (Invalid_argument "Cannot perform universal application on a abstraction")

(* Determines the branch of the abstraction to execute, based on the type of the argument *)
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
