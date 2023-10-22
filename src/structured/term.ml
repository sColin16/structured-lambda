open Helpers
open Type

type term =
  | Abstraction of (structured_type * term) list
  | Application of term * term
  | Variable of int
  | Const of string
  | FixAbs of (structured_type * term) list

(** [type_lambda_term term] determines the type of a term, if it is well-typed *)
let rec get_type (term : term) = get_type_rec term TypeContextMap.empty (-1)

and get_type_rec (term : term) (context : type_context_map) (level : int) :
    structured_type option =
  match term with
  (* Constants always have label types *)
  | Const name -> Some [ Label name ]
  (* Use the helper function to determine if an application is well-typed *)
  | Application (t1, t2) ->
      let left_type = get_type_rec t1 context level in
      let right_type = get_type_rec t2 context level in
      flat_map_opt2 get_application_type left_type right_type
  (* Abstractions are well-typed if their argument types don't match
     The return types of the body can be inferred recursively from the argument type *)
  | Abstraction definitions ->
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
        let body_types_opt =
          List.map (type_abstraction_branch context level) definitions
        in
        let return_types_opt = opt_list_to_list_opt body_types_opt in
        Option.map
          (fun return_types ->
            [ Function (List.combine arg_types return_types) ])
          return_types_opt
  | Variable var_num -> TypeContextMap.find_opt (level - var_num) context
  | FixAbs definitions ->
    let arg_types = extract_first definitions in
    let tentative_type_opt = distribute_intersection arg_types in
    match tentative_type_opt with
    | None -> None
    | Some tentative_type -> (
      let new_level = level + 1 in
      let new_context = TypeContextMap.add new_level tentative_type context in
      let branch_bodies = extract_second definitions in
      let return_types_opt_list = List.map (fun body -> get_type_rec body new_context new_level) branch_bodies in
      let return_types_opt = opt_list_to_list_opt return_types_opt_list in
      match return_types_opt with
      | None -> None
      | Some return_types -> (
        let subtype_invariant_met = List.for_all2 (fun arg_type return_type -> is_subtype return_type arg_type) arg_types return_types in
        if subtype_invariant_met then Some tentative_type else None
      )
    )

and type_abstraction_branch (context : type_context_map) (level : int)
    ((branch_type, branch_body) : structured_type * term) =
  get_type_rec branch_body
    (TypeContextMap.add (level + 1) branch_type context)
    (level + 1)

and distribute_intersection (type_intersection: base_type union intersection): structured_type option =
  let distributed_result: base_type intersection union  = multi_list_product type_intersection in
  let option_types = List.map resolve_base_intersection distributed_result in
  let function_type_unions = opt_list_to_list_opt option_types in
  let result = Option.map (fun x -> (List.map (fun functions -> Function functions) x)) function_type_unions in
  result

and resolve_base_intersection (intersection: base_type intersection): unary_function intersection option =
  let function_intersections_opt = List.map (fun base ->
    match base with
    | Label _ -> None
    | Function unary_intersections -> Some unary_intersections
  ) intersection in
  let function_intersections = opt_list_to_list_opt function_intersections_opt in
  let unified_intersection_opt = Option.map List.flatten function_intersections in
  match unified_intersection_opt with
  | None -> None
  | Some unified_intersection -> (
    let function_pairs = self_pairs unified_intersection in
    let has_arg_intersection = List.exists (fun ((arg1, _), (arg2, _)) -> has_intersection arg1 arg2) function_pairs in
    if has_arg_intersection then None else Some unified_intersection
  )
