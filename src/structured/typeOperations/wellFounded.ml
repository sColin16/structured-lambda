open Metatypes
open Helpers

module TypeVarSet = Set.Make(struct
  type t = int
  let compare = compare
end)

let rec is_valid_well_founded_context (context: recursive_context) =
(* All inductive types must be well-founded in the context *)
  List.for_all (function
  | { kind = Coinductive; _  } -> true
  | { kind = Inductive; flat_union } ->
    let unflattened_union = unflatten_union flat_union in
    is_well_founded_union unflattened_union context
  ) context

and is_well_founded_union (union: union_type) (context: recursive_context) =
  is_well_founded_union_rec union context TypeVarSet.empty

and is_well_founded_union_rec (union: union_type) (context: recursive_context) (visited: TypeVarSet.t) =
  (* At least one type in a union must be well-founded for the union to be considered well-founded *)
  List.exists (is_well_founded_base context visited) union

and is_well_founded_base (context: recursive_context) (visited: TypeVarSet.t) (base: base_type) =
  match base with
  (* Labels are well-founded *)
  | Label _ -> true
  (* Intersections are well-founded if each function in the intersection is well-founded *)
  | Intersection functions -> List.for_all (is_well_founded_func context visited) functions
  | TypeVar n ->
    (* If we encounter a type-var loop, this branch of the type is not well-founded *)
    if TypeVarSet.mem n visited then false else
      (* Otherwise, track the type var, expand, and recurse *)
      let new_visited = TypeVarSet.add n visited in
      let expanded_union = expand_type_var_to_union n context in
      is_well_founded_union_rec expanded_union context new_visited

and is_well_founded_func (context: recursive_context) (visited: TypeVarSet.t) (arg, return: unary_function) =
  (* A function type is well-founded if bot the arguments and return type are *)
  is_well_founded_union_rec arg context visited && is_well_founded_union_rec return context visited