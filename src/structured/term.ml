open Helpers
open Type

type term =
  | Abstraction of (structured_type * term) list
  | Application of term * term
  | Variable of int
  | Const of string
  | Fix of term

let rec shift_type_vars_union (amount : int) (union : union_type) =
  List.map (shift_type_vars_base amount) union

and shift_type_vars_base (amount : int) (base_type : base_type) =
  match base_type with
  | Label _ -> base_type
  | TypeVar n -> TypeVar (n + amount)
  | Intersection functions ->
      Intersection (List.map (shift_type_vars_func amount) functions)

and shift_type_vars_func (amount : int) ((arg, return) : unary_function) =
  (shift_type_vars_union amount arg, shift_type_vars_union amount return)

let get_type_in_context ((union, context1) : structured_type)
    (recursive_context : recursive_context) : structured_type =
  let new_recursive_context = recursive_context @ context1 in
  let new_union = shift_type_vars_union (List.length recursive_context) union in
  (new_union, new_recursive_context)

(** [type_lambda_term term] determines the type of a term, if it is well-typed *)
let rec get_type (term : term) = get_type_rec term TypeContextMap.empty (-1) []

and get_type_rec (term : term) (type_context : type_context_map) (level : int)
    (recursive_context : recursive_context) : structured_type option =
  match term with
  (* Constants always have label types *)
  | Const name -> Some ([ Label name ], recursive_context)
  (* Use the helper function to determine if an application is well-typed *)
  | Application (t1, t2) ->
      let left_type = get_type_rec t1 type_context level recursive_context in
      let right_type = get_type_rec t2 type_context level recursive_context in
      flat_map_opt2 get_application_type left_type right_type
  (* Abstractions are well-typed if their argument types don't match
     The return types of the body can be inferred recursively from the argument type *)
  | Abstraction definitions ->
      (* An abstraction is ill-typed if any of its arguments intersect *)
      let arg_types = extract_first definitions in
      let arg_pairs = self_pairs arg_types in
      let disjoint_args =
        not
          (List.exists
             (fun (arg1, arg2) -> has_intersection arg1 arg2)
             arg_pairs)
      in
      if not disjoint_args then None
      else
        (* TODO: should we fold right instead? The direction shouldn't matter and we need to append elements to the end of the list *)
        (* The approach here is to always append to the end of the recursive context. So we add the argument's recursive context to our
           current context, pass that down recursively, and whatever comes back should have just appended to the recursive context, so we
           can use that context. We fold over all the branches to accumulate a single recursive context and intersection type *)
        let intersection_type_opt = List.fold_left (fun acc -> fun (arg_branch_type, branch_body) ->
          (match acc with
          | None -> None
          | Some (acc_union_type, acc_recursive_context) ->
            let new_arg_type, new_recursive_context = get_type_in_context arg_branch_type acc_recursive_context in
            let body_result = get_type_rec branch_body (TypeContextMap.add (level + 1) new_arg_type type_context) (level + 1) new_recursive_context in
            let a = Option.map (fun (body_type, body_recursive_context) ->
              ( acc_union_type @ [new_arg_type, body_type], body_recursive_context )
            ) body_result in a
          )
        ) (Some([], recursive_context)) definitions in
        Option.map (fun (intersection_type, recursive_context) -> ([Intersection(intersection_type)], recursive_context)) intersection_type_opt
  | Variable var_num ->
      let union_type_opt =
        TypeContextMap.find_opt (level - var_num) type_context
      in
      Option.map
        (fun union_type -> (union_type, recursive_context))
        union_type_opt
  | Fix inner_term ->
      let inner_type_opt = get_type_rec inner_term type_context level recursive_context in
      (* The approach here is that we type each types in the union of the sub-term. If any of them are ill-typed, this term is ill-typed as well
          If they are all well-typed, we join all the resulting union types together, and bubble up the subterms recursive context *)
      Option.join (Option.map (fun (inner_type, inner_recursive_context) ->
        let fixed_option_types = List.map (type_fix_option recursive_context) inner_type in
        let fixed_types_opt = opt_list_to_list_opt fixed_option_types in
        let fixed_type_opt = Option.map List.flatten fixed_types_opt in
        Option.map (fun fixed_type -> (fixed_type, inner_recursive_context)) fixed_type_opt
      ) inner_type_opt)

and type_fix_option (context: recursive_context) (fix_option_type : base_type) =
  match fix_option_type with
  (* Fix can only be typed over a unary function type. n-ary functions can't be fixed  nore can the unit type or labels *)
  | Intersection [ (arg_type, return_type) ] ->
      if is_subtype (return_type, context) (arg_type, context) then Some arg_type else None
  | _ -> None
