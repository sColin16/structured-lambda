open Term
open Type
open Helpers

(** [eval term] evaluates a term to a value *)
let rec eval (term : term) =
  match term with
  (* Application of a const should't happen under the type system, others are considered values *)
  | Abstraction _ | Variable _
  | Application (Variable _, _)
  | Const _
  | Application (Const _, _) ->
      term
  (* Evaluate the internals of a fix *)
  | Fix term -> (
      let inner_evaluated = eval term in
      match inner_evaluated with
      | Abstraction branches -> (
          match evaluate_fix inner_evaluated branches with
          | Some result -> result
          | None -> Fix inner_evaluated)
      | other -> Fix other)
  (* Evaluate the LHS of an application first *)
  | Application (Application (t1, t2), t3) ->
      let left_evaluated = eval (Application (t1, t2)) in
      eval (Application (left_evaluated, t3))
  | Application (Fix t1, t2) ->
      let fix_evaluated = eval (Fix t1) in
      eval (Application (fix_evaluated, t2))
  (* Then evaluate the RHS of an application *)
  | Application (Abstraction t1, Application (t2, t3)) ->
      let right_evaluated = eval (Application (t2, t3)) in
      eval (Application (Abstraction t1, right_evaluated))
  (* Finally, determine the branch of the abstraction to use, and substitute *)
  | Application (Abstraction branches, t2) ->
      let executed_branch = resolve_branch branches t2 in
      eval (substitute t2 executed_branch)

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

and substitute (with_term : term) (in_term : term) =
  let shifted_with_term = shift with_term 1 in
  let substitution_result = substitute_rec 0 shifted_with_term in_term in
  let final_resut = shift substitution_result (-1) in
  final_resut

and substitute_rec (variable_num : int) (with_term : term) (in_term : term) =
  match in_term with
  | Variable internal_num ->
      if variable_num == internal_num then with_term else in_term
  | Abstraction internal_term ->
      let new_var_num = variable_num + 1 in
      let new_with_term = shift with_term 1 in
      let substituted_bodies =
        List.map
          (fun (branch_type, branch_body) ->
            (branch_type, substitute_rec new_var_num new_with_term branch_body))
          internal_term
      in
      Abstraction substituted_bodies
  | Application (t1, t2) ->
      Application
        ( substitute_rec variable_num with_term t1,
          substitute_rec variable_num with_term t2 )
  | Const _ -> in_term
  | Fix internal_term -> Fix (substitute_rec variable_num with_term internal_term)

and shift (term : term) (shift_amt : int) = shift_rec term shift_amt 0

and shift_rec (term : term) (shift_amt : int) (cutoff : int) =
  match term with
  | Variable var_num ->
      if var_num >= cutoff then Variable (var_num + shift_amt)
      else Variable var_num
  | Abstraction internal_term ->
      let mapped_branches =
        List.map
          (fun (branch_type, branch_body) ->
            (branch_type, shift_rec branch_body shift_amt (cutoff + 1)))
          internal_term
      in
      Abstraction mapped_branches
  | Application (t1, t2) ->
      Application (shift_rec t1 shift_amt cutoff, shift_rec t2 shift_amt cutoff)
  | Const _ -> term
  | Fix internal_tem-> Fix (shift_rec internal_tem shift_amt cutoff)

and evaluate_fix (internal_term : term)
    (abstraction_branches : (structured_type * term) list) =
  let branch_terms = extract_second abstraction_branches in
  let evaluated_branches =
    List.map (evaluate_fix_branch internal_term) branch_terms
  in
  intersect_terms evaluated_branches

and evaluate_fix_branch (internal_term : term) (branch_term : term) =
  substitute (Fix internal_term) branch_term

and intersect_terms (terms : term intersection) =
  let abstraction_bodies_opt =
    List.map
      (fun term ->
        match term with Abstraction branches -> Some branches | _ -> None)
      terms
  in
  let abstraction_bodies = opt_list_to_list_opt abstraction_bodies_opt in
  let unified_abstraction_bodies = Option.map List.flatten abstraction_bodies in
  Option.map (fun x -> Abstraction x) unified_abstraction_bodies
