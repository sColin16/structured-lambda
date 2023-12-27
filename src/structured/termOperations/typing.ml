open Common.Helpers
open TermTypes
open Metatypes
open TypeOperations.Helpers
open TypeOperations.Create
open TypeOperations.Intersection
open TypeOperations.Subtype
open TypeOperations.Context

module TypeContextMap = Map.Make (struct
  type t = int

  let compare = compare
end)

type type_context_map = union_type TypeContextMap.t

(** [type_lambda_term term] determines the type of a term, if it is well-typed *)
let rec get_type (term : term) = get_type_rec term TypeContextMap.empty (-1) []

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
  | Variable var_num ->
      let union_type_opt =
        TypeContextMap.find_opt (level - var_num) type_context
      in
      Option.map
        (fun union_type -> build_structured_type union_type recursive_context)
        union_type_opt

and type_fix_option (context : recursive_context) (fix_option_type : base_type)
    =
  match fix_option_type with
  (* Fix can only be typed over a unary function type. n-ary functions can't be fixed  nore can the unit type or labels *)
  | Intersection [ (arg_type, return_type) ] ->
      if
        is_subtype
          (build_structured_type return_type context)
          (build_structured_type arg_type context)
      then Some arg_type
      else None
  | _ -> None

(** [get_application_type func_type arg_type] determines the resulting type of
    applying a term of type [arg_type] to a term of type [func_type], if
    the function can be applied to the argument *)
and get_application_type (func : structured_type) (arg : structured_type) :
    structured_type option =
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
  (* A label type cannot be applied *)
  | FLabel _ -> None
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
