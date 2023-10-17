open Helpers

type structured_type = base_type list
and base_type = Label of string | Function of unary_function list
and unary_function = structured_type * structured_type

module TypeContextMap = Map.Make (struct
  type t = int

  let compare = compare
end)

type type_context_map = structured_type TypeContextMap.t

(* TODO: remov duplicate and subtypes from the union after flattening *)
let extract_composite_args (branches : unary_function list) =
  List.flatten (extract_first branches)

let extract_composite_return (branches : unary_function list) =
  List.flatten (extract_second branches)


(** [has_intersection type1 type2] determines if the intersection of the two types is inhabited
    More specfically, determines if there exists a subtype of the intersection of the two types, other than the bottom type *)
let rec has_intersection (t1 : structured_type) (t2 : structured_type) =
  (* The intersection of two union types is inhabited if any pairs in the uion of inhaboted *)
  let union_pairs = list_product t1 t2 in
  List.exists has_intersection_base union_pairs

and has_intersection_base type_pair =
  match type_pair with
  (* Two labels have an intersection only when they're equal *)
  | Label a, Label b -> a = b
  (* unit/top type intersected with any type is that type *)
  | _, Function [] | Function [], _ -> true
  (* Non-empty functions and labels have have uninhabited intersections *)
  | Label _, Function (_ :: _) | Function (_ :: _), Label _ -> false
  (* The intersection of two non-unit function types is inhabited if each pair of unary function types is inhabited *)
  | Function first, Function second ->
      let function_pairs = list_product first second in
      List.for_all has_intersection_func function_pairs

and has_intersection_func
    (((arg1, return1), (arg2, return2)) : unary_function * unary_function) =
  let args_intersect = has_intersection arg1 arg2 in
  let returns_intersect = has_intersection return1 return2 in
  (* Unary function intersection is inhabited if the argument types don't intersect (intersection
     is simply the ad-hoc polymorphic function), or if the argument types do intersect, but the return
     types do as well (the intersecting argument component maps to the intersection
     of the return types)*)
  (not args_intersect) || returns_intersect

(** [is_subtype type1 type2] determines if [type1] is a subtype of [type2] *)
let rec is_subtype (t1 : structured_type) (t2 : structured_type) =
  (* a type is a subtype of another, if for every type in the first type,
     there exists a supertype in the second type *)
  List.for_all
    (fun base_type1 ->
      List.exists (fun base_type2 -> is_base_subtype base_type1 base_type2) t2)
    t1

and is_base_subtype (t1 : base_type) (t2 : base_type) =
  match (t1, t2) with
  (* Labels are subtypes when they are the same label *)
  | Label a, Label b -> a = b
  (* Labels are considered a subtype of the unit/top type *)
  | Label _, Function [] -> true
  (* Otherwise, labels and functios have no subtype relation between them *)
  | Label _, Function (_ :: _) | Function _, Label _ -> false
  (* Two functions are subtypes if the first function accepts at least as many
     argument types, and returns subtypes for every argument types that intersects *)
  | Function first, Function second ->
      let first_args = extract_composite_args first in
      let second_args = extract_composite_args second in
      let function_pairs = list_product first second in
      let exhaustive_arg_coverage = is_subtype second_args first_args in
      let return_type_constraint =
        List.for_all is_subtype_func function_pairs
      in
      exhaustive_arg_coverage && return_type_constraint

and is_subtype_func
    (((arg1, return1), (arg2, return2)) : unary_function * unary_function) =
  let args_intersect = has_intersection arg1 arg2 in
  let return_subtype = is_subtype return1 return2 in
  (* Two unary function are subtype-compatible if their arguments don't intersect (other check will
      confirm arguments are exhaustive), or they do intersect, but the return type is a subtype
     (to guarantee thefunction cannot return a supertype for the intersecting argument) *)
  (not args_intersect) || return_subtype

(** [get_application_type func_type arg_type] determines the resulting type of
    applying a term of type [arg_type] to a term of type [func_type], if
    the function can be applied to the argument *)
let rec get_application_type (func : structured_type) (arg : structured_type) =
  (* The argument should be applicable to any function in the union, so acquire the type of applying the arg to each option *)
  let return_types_opt = List.map (get_application_option_type arg) func in
  (* Aggregate the return types - if anyof them were none, the application is not well-typed *)
  let return_types = opt_list_to_list_opt return_types_opt in
  (* Join all of the return types into a single union types *)
  Option.map List.flatten return_types

and get_application_option_type (arg : structured_type)
    (func_option : base_type) =
  match func_option with
  (* A label type cannot be applied *)
  | Label _ -> None
  (* An application against a function type is well-typed if the function accepts at least as many arguments.
     The return type is the union of all return types that the argument might match with *)
  | Function func_list ->
      let func_params = extract_composite_args func_list in
      let exhaustive_arg_coverage = is_subtype arg func_params in
      if not exhaustive_arg_coverage then None
      else
        Some
          (List.fold_left
             (fun acc (func_arg, func_return) ->
               if has_intersection arg func_arg then acc @ func_return else acc)
             [] func_list)
