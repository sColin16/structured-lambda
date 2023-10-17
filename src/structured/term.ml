open Helpers
open Type

type term =
  | Abstraction of (structured_type * term) list
  | Application of term * term
  | Variable of int
  | Const of string

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

and type_abstraction_branch (context : type_context_map) (level : int)
    ((branch_type, branch_body) : structured_type * term) =
  get_type_rec branch_body
    (TypeContextMap.add (level + 1) branch_type context)
    (level + 1)
