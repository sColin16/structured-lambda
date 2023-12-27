open TermTypes
open Typing
open TypeOperations.Subtype

(** [eval term] evaluates a term to a value *)
let rec eval (term : term) =
  match term with
  (* Application of a const should't happen under the type system, others are considered values *)
  | Abstraction _ | Variable _
  | Application (Variable _, _)
  | Const _
  | Application (Const _, _) ->
      term
  (* Evaluate the LHS of an application first *)
  | Application (Application (t1, t2), t3) ->
      let left_evaluated = eval (Application (t1, t2)) in
      eval (Application (left_evaluated, t3))
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
