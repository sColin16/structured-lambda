open Helpers

type 'a union = 'a list
type 'a intersection = 'a list

type structured_type = base_type union
and base_type = Label of string | Function of unary_function intersection
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

(** [is_unary union_type] determines if a type cannot be written as the union of two distinct, unrelated types *)
let rec is_unary (t : structured_type) =
  match t with
  (* Under the rewriting equality rule, the empty type is considered "unary" even though it's really more nullary *)
  | [] -> true
  (* A single type in a union is considered unary if the corresponding base type *)
  | [ base ] -> (
      match base with
      (* Labels are unary be definition *)
      | Label _ -> true
      (* Functions are unary if all their argument and return types are unary *)
      | Function functions ->
          List.for_all
            (fun (arg, return) -> is_unary arg && is_unary return)
            functions)
  (* A multiple type union is not considered unary. In theory it may be possible to rewrite as a single base type
     but we can do that later *)
  | _ :: _ -> false

(** [is_subtype type1 type2] determines if [type1] is a subtype of [type2] *)
let rec is_subtype (t1 : structured_type) (t2 : structured_type) =
  (* a type is a subtype of another, if for every type in the first type,
     there exists a supertype in the second type *)
  List.for_all (fun base_type1 -> is_base_union_subtype base_type1 t2) t1

and is_base_union_subtype (t1 : base_type) (t2 : structured_type) =
  match t1 with
  | Label _ -> List.exists (is_base_subtype t1) t2
  | Function functions -> is_function_union_subtype functions t2

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

and is_function_union_subtype (functions : unary_function intersection)
    (union : structured_type) =
  (* First, check if there a intersection types in the union that is a supertype directly *)
  let simply_subtyped =
    List.exists (is_base_subtype (Function functions)) union
  in
  if simply_subtyped then true
    (* Otherwise, we need to consider the function having return types split on union *)
  else is_exhaustive_function_subtype functions union

(** Checks if a function type is an exhaustive subtype of a union of function types *)
and is_exhaustive_function_subtype (functions : unary_function intersection)
    (union : structured_type) =
  (* Eliminate labels from the union type to get a union of intersections *)
  let union_of_intersections =
    List.filter_map
      (fun base_type ->
        match base_type with
        | Label _ -> None
        | Function functions -> Some functions)
      union
  in
  match union_of_intersections with
  (* If there are 0 or 1 types in the union, we cannot distribute a union, so direct function subtyping would be required *)
  | [] | [ _ ] -> false
  | _ :: _ ->
      (* If there are multiple types in the union, distribute the union *)
      let intersection_of_unions = multi_list_product union_of_intersections in
      (* We only consider functions with arguments in unary form, per splitting rule *)
      let unary_functions =
        List.filter (fun (arg, _) -> is_unary arg) functions
      in
      (* We must prove the intersection is a subtype of each union in the intersection *)
      let does_subtype =
        List.for_all
          (fun union_supertype ->
            is_subtype_of_unary_union unary_functions union_supertype)
          intersection_of_unions
      in
      does_subtype

and is_subtype_of_unary_union (unary_functions : unary_function intersection)
    (function_union : unary_function union) =
  (* We must prove that one function type in the intersection is a subtype of the union *)
  List.exists
    (fun (sub_arg, sub_return) ->
      let relevant_functions =
        List.filter
          (fun (super_arg, _) -> is_subtype super_arg sub_arg)
          function_union
      in
      let composite_return = extract_composite_return relevant_functions in
      (* It is a subtype if the return types of all functions with argument subtypes form a supertype *)
      is_subtype sub_return composite_return)
    unary_functions

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
