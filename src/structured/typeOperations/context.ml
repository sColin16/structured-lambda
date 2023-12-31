open Metatypes
open Create

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

and shift_type_vars_context (amount : int) (context : recursive_context) =
  List.map (shift_type_vars_def amount) context

and shift_type_vars_def (amount : int) (recursive_def : recursive_def) =
  let shifted_union = List.map (fun flat_base ->
    match flat_base with
    | FLabel _ -> flat_base
    | FIntersection functions ->
        FIntersection (List.map (shift_type_vars_func amount) functions)
  ) recursive_def.flat_union in
  build_recursive_def recursive_def.kind shifted_union

let get_type_in_context (t : structured_type)
    (recursive_context : recursive_context) : structured_type =
  let shift_amount = List.length recursive_context in
  let new_context = shift_type_vars_context shift_amount t.context in
  let new_union =
    shift_type_vars_union (List.length recursive_context) t.union
  in
  build_structured_type new_union (recursive_context @ new_context)