open Common.Helpers
open TermTypes
open Metatypes
open TypeOperations.Helpers
open TypeOperations.Create
open TypeOperations.Intersection
open TypeOperations.Subtype
open TypeOperations.Context
open SubstituteUnivVar
open TypeOperations.Union

module TypeContextMap = Map.Make (struct
  type t = int

  let compare = compare
end)

type type_context_map = union_type TypeContextMap.t

(** [type_lambda_term term] determines the type of a term, if it is well-typed *)
let rec get_type (term : term) = get_type_rec term TypeContextMap.empty (-1) []

(* TODO: is this type context just an environment? Could I simplify by prepending to the front of the list to avoid the level? *)
and get_type_rec (term : term) (type_context : type_context_map) (level : int)
    (recursive_context : recursive_context) : structured_type option =
  match term with
  (* Constants always have label types *)
  | Const name -> Some (build_structured_type [ Label name ] recursive_context)
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
        let intersection_type_opt =
          List.fold_left
            (fun acc (arg_branch_type, branch_body) ->
              match acc with
              | None -> None
              | Some (acc_union_type, acc_recursive_context) ->
                  let new_arg_type =
                    get_type_in_context arg_branch_type acc_recursive_context
                  in
                  let body_type_opt =
                    get_type_rec branch_body
                      (TypeContextMap.add (level + 1) new_arg_type.union
                         type_context)
                      (level + 1) new_arg_type.context
                  in
                  Option.map
                    (fun body_type ->
                      ( acc_union_type
                        @ [ (new_arg_type.union, body_type.union) ],
                        body_type.context ))
                    body_type_opt)
            (Some ([], recursive_context))
            definitions
        in
        Option.map
          (fun (intersection_type, recursive_context) ->
            build_structured_type
              [ Intersection intersection_type ]
              recursive_context)
          intersection_type_opt
  (* The type of a variable is variable is based on the type of the argument in the abstraction defining it *)
  | Variable var_num ->
      let union_type_opt =
        TypeContextMap.find_opt (level - var_num) type_context
      in
      Option.map
        (fun union_type -> build_structured_type union_type recursive_context)
        union_type_opt
  (* Determine the type within the quantifier, then merge the recursive contexts and build the appropriate union type *)
  | UnivQuantifier inner_term ->
      let inner_type_opt =
        get_type_rec inner_term type_context level recursive_context
      in
      Option.map
        (fun inner_type ->
          let recontextualized_inner =
            get_type_in_context inner_type recursive_context
          in
          build_structured_type
            [ UnivQuantification recontextualized_inner.union ]
            recontextualized_inner.context)
        inner_type_opt
  | UnivApplication (inner_term, inner_type) ->
      let inner_term_type_opt =
        get_type_rec inner_term type_context level recursive_context
      in
      Option.join (Option.map
        (fun inner_term_type ->
          get_univ_application_type inner_term_type inner_type)
        inner_term_type_opt)

(** [get_application_type func_type arg_type] determines the resulting type of
    applying a term of type [arg_type] to a term of type [func_type], if
    the function can be applied to the argument *)
and get_application_type (func : structured_type)
    (arg : structured_type) : structured_type option =
  (* Flatten the func type so only labels and intersection types remain *)
  let func_flat = flatten_union func.union func.context in
  (* The argument should be applicable to any function in the union, so acquire the type of applying the arg to each option *)
  let return_types_opt =
    List.map
      (fun func_option ->
        get_application_option_type (func_option, func.context) arg)
      func_flat
  in
  (* Aggregate the return types - if any of them were none, the application is not well-typed *)
  (* Return types that come back have context func.context, since abstractions determine their return types *)
  let return_types = opt_list_to_list_opt return_types_opt in
  (* Join all of the return types into a single union type, add the context *)
  Option.map
    (fun return_types_concrete ->
      build_structured_type (List.flatten return_types_concrete) func.context)
    return_types

and get_application_option_type
    ((func_option, context1) : flat_base_type * recursive_context)
    (arg : structured_type) : union_type option =
  match func_option with
  (* Label types, universal quantifications, and their variables cannot be applied *)
  (* TODO: some variables may be able to be applied under bounded quantification *)
  | FLabel _ | FUnivTypeVar _ | FUnivQuantification _ -> None
  (* An application against a function type is well-typed if the function accepts at least as many arguments.
     The return type is the union of all return types that the argument might match with *)
  | FIntersection functions ->
      let func_params = extract_composite_args functions in
      let exhaustive_arg_coverage =
        is_subtype arg (build_structured_type func_params context1)
      in
      if not exhaustive_arg_coverage then None
      else
        Some
          (List.fold_left
             (fun acc (func_arg, func_return) ->
               if has_intersection arg (build_structured_type func_arg context1)
               then acc @ func_return
               else acc)
             [] functions)

and get_univ_application_type (quantifier : structured_type)
    (type_arg : structured_type): structured_type option =
  (* Flatten the func type to get rid of recursive types *)
  let quantifier_flat = flatten_union quantifier.union quantifier.context in
  (* The type argument is applicable to any universal quantification in the union, so determine the types resulting
     from applying the type argument to each universal quantification in the union *)
  let return_opt_types =
    List.map
      (fun quant_option ->
        get_univ_application_option_type (quant_option, quantifier.context) type_arg)
      quantifier_flat
  in
  (* Aggregate the return types - if any of them were none, the application is not well-typed *)
  let return_types_opt = opt_list_to_list_opt return_opt_types in
  (* Combine all of the structured types, merging both the unions and and contexts *)
  Option.map (
    fun return_types -> (
      get_type_union return_types
    )
  ) return_types_opt

and get_univ_application_option_type
    ((func_option, context1) : flat_base_type * recursive_context)
    (type_arg : structured_type) : structured_type option =
  match func_option with
  (* Only universal quantification can have type applications
     Universal type variables may be instantiated with quantification (assuming impredicativity)
     but it's not guaranteed *)
  | FLabel _ | FIntersection _ | FUnivTypeVar _ -> None
  (* If we had bounded quantification, we'd need to make sure the type argument provided is valid *)
  (* But for now, we just substitution in the inner type. The function handles shifting for us *)
  | FUnivQuantification inner_union_type ->
    (* Construct the complete inner type using the context *)
    let inner_type = build_structured_type inner_union_type context1 in
    Some (substitute_univ_var_type type_arg inner_type)
