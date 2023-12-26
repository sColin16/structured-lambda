open Common.Helpers
open Create
open Helpers
open Metatypes
open Unary
open Intersection

(** [is_subtype type1 type2] determines if [type1] is a subtype of [type2] *)
let rec is_subtype (t1 : structured_type) (t2 : structured_type) =
  is_subtype_union_rec t1 t2 TypeVarUnionSet.empty

(* Recursive helper to determine if two structured types are subtypes of one another *)
and is_subtype_union_rec (t1 : structured_type) (t2 : structured_type)
    (encountered_type_vars : TypeVarUnionSet.t) =
  (* A union type is a subtype of another union type, if each base type in the first union is a subtype
     of the second union *)
  List.for_all
    (fun base_type ->
      is_base_union_subtype (base_type, t1.context) t2 encountered_type_vars)
    t1.union

and is_base_union_subtype ((t1, c1) : base_type * recursive_context)
    (t2 : structured_type) (encountered_type_vars : TypeVarUnionSet.t) =
  match t1 with
  | Label a -> is_label_union_subtype a t2
  | Intersection functions ->
      is_function_union_subtype (functions, c1) t2 encountered_type_vars
  | RecTypeVar n -> is_typevar_union_subtype (n, c1) t2 encountered_type_vars

and is_label_union_subtype (label : string) (t : structured_type) =
  let flat_union = flatten_union t.union t.context in
  (* A label is a subtype of an equivalent label in the union, or the top type *)
  List.exists
    (fun flat_union_elt ->
      match flat_union_elt with
      | FLabel a -> a = label
      | FIntersection [] -> true
      | FIntersection (_ :: _) -> false)
    flat_union

and is_function_union_subtype
    ((functions, context1) : unary_function intersection * recursive_context)
    (t : structured_type) (encountered_type_vars : TypeVarUnionSet.t) =
  (* Flatten the type with contractivity to only labels and intersections *)
  let flat_union = flatten_union t.union t.context in
  (* Filter out the label types because they don't assist in subtyping an intersection *)
  let union_of_intersections =
    List.filter_map
      (fun base_type ->
        match base_type with
        | FLabel _ -> None
        | FIntersection functions -> Some functions)
      flat_union
  in
  (* First, check if there a intersection types in the union that is a supertype directly *)
  let is_direct_subtype = fun () ->
    is_function_subtype_direct (functions, context1)
      (union_of_intersections, t.context)
      encountered_type_vars
  in
  (* Then, check if it's an indirect subtype of the entire union *)
  let is_indirect_subtype = fun () ->
    is_function_subtype_indirect (functions, context1)
      (union_of_intersections, t.context)
      encountered_type_vars
  in
  (* Only one needs to be true *)
  short_circuit_or is_direct_subtype is_indirect_subtype

and is_typevar_union_subtype ((var_num, context1) : int * recursive_context)
    (t : structured_type) (encountered_type_vars : TypeVarUnionSet.t) =
  let union_contains_typevars =
    List.exists
      (fun base_type ->
        match base_type with
        | RecTypeVar _ -> true
        | Label _ | Intersection _ -> false)
      t.union
  in
  let var_num_kind = (List.nth context1 var_num).kind in
  (* If we have encountered a loop in the type variables, we must
     analyze the contents of the loop components to make a decision *)
  if
    union_contains_typevars
    && TypeVarUnionSet.mem (var_num, t.union) encountered_type_vars
  then
    let union_has_coinductive = List.exists
      (fun base_type ->
        match base_type with
        | RecTypeVar n -> ((List.nth t.context n).kind = Coinductive)
        | Label _ | Intersection _ -> false)
      t.union in
    match var_num_kind with
    (* Coinductive loops are valid if there is at least one coinductive type on the other side *)
    | Coinductive -> union_has_coinductive
    (* Inductive loops of any kind require a base case, which is handled by the well-founded
       requirement of the type, so we consider this true *)
    | Inductive -> true
  else
    (* Otherwise, track this type var/union combination for future loops,
       if the union contains type variables at the top level *)
    let new_encountered_var =
      if union_contains_typevars then
        TypeVarUnionSet.add (var_num, t.union) encountered_type_vars
      else encountered_type_vars
    in
    (* Then, expand both sides contractively, removing all type vars *)
    let expanded_type_var = expand_type_var var_num context1 in
    let flat_union = to_contractive_type t.union t.context in
    (* Then recurse on the two expanded unions, determining if they are subtypes *)
    is_subtype_union_rec expanded_type_var flat_union new_encountered_var

(* Returns the compound structure. Must be able to union the compound structure *)
and is_function_subtype_direct
    ((functions, context1) : unary_function intersection * recursive_context)
    ((union_of_intersections, context2) :
      unary_function intersection union * recursive_context)
    (encountered_type_vars : TypeVarUnionSet.t) =
  (* Check if an intersection exists in the union type that is a direct supertype of the function in question *)
  List.exists
    (fun intersection_supertype ->
      is_intersection_subtype (functions, context1)
        (intersection_supertype, context2)
        encountered_type_vars)
    union_of_intersections

(* Must return an intersection of the compound structure *)
and is_function_subtype_indirect
    ((functions, context1) : unary_function intersection * recursive_context)
    ((union_of_intersections, context2) :
      unary_function intersection union * recursive_context)
    (encountered_type_vars : TypeVarUnionSet.t) =
  match union_of_intersections with
  (* If there are 0 or 1 types in the union, we cannot distribute a union, so direct function subtyping would be required *)
  | [] | [ _ ] -> false
  | _ :: _ ->
      (* If there are multiple types in the union, distribute the union *)
      let intersection_of_unions = multi_list_product union_of_intersections in
      (* We only consider functions in the subtype with arguments in unary form, per splitting rule *)
      let unary_form_functions =
        List.filter
          (fun (arg, _) -> is_unary (build_structured_type arg context1))
          functions
      in
      (* We must prove the unary form function intersection is a subtype of each union in the intersection *)
      List.for_all
        (fun union_supertype ->
          is_intersection_union_subtype
            (unary_form_functions, context1)
            (union_supertype, context2)
            encountered_type_vars)
        intersection_of_unions

(* Must return the compound structure. Must intersect multiple compound structures *)
and is_intersection_subtype
    ((functions1, context1) : unary_function intersection * recursive_context)
    ((functions2, context2) : unary_function intersection * recursive_context)
    (encountered_type_vars : TypeVarUnionSet.t) =
  let first_args = extract_composite_args functions1 in
  let second_args = extract_composite_args functions2 in
  let function_pairs = list_product functions1 functions2 in
  (* The function1's argument types (unioned together) must be a supertype of function2's argument types (unioned together) *)
  let exhaustive_arg_coverage = fun () ->
    is_subtype_union_rec
      (build_structured_type second_args context2)
      (build_structured_type first_args context1)
      encountered_type_vars
  in
  (* Every pair of unary functions must be "subtype compatible," returning a subtype if the arg types intersect *)
  let return_type_constraint_met = fun() ->
    List.for_all
      (fun (func1, func2) ->
        is_func_subtype_compatible (func1, context1) (func2, context2)
          encountered_type_vars)
      function_pairs
  in
  short_circuit_and exhaustive_arg_coverage return_type_constraint_met

(* Must return a union of the compound structure *)
and is_intersection_union_subtype
    ((unary_form_functions, context1) :
      unary_function intersection * recursive_context)
    ((function_union, context2) : unary_function union * recursive_context)
    (encountered_type_vars : TypeVarUnionSet.t) =
  (* We must prove that one function type in the unary form intersection is a subtype of the union *)
  List.exists
    (fun (sub_arg, sub_return) ->
      is_unary_func_union_subtype
        ((sub_arg, sub_return), context1)
        (function_union, context2) encountered_type_vars)
    unary_form_functions

and is_unary_func_union_subtype
    (((arg, return), context1) : unary_function * recursive_context)
    ((function_union, context2) : unary_function union * recursive_context)
    (encountered_type_vars : TypeVarUnionSet.t) =
  let relevant_functions =
    List.filter
      (fun (super_arg, _) ->
        (* Because arg is unary, super_arg cannot contain a well-founded inductive types. If it is to be a subtype,
           it must either be a finite type or an infinite type equal to super_arg. So we check for subtyping directly.
           If for some reason that's wrong, then we need to take the each subset of function_union and check that the
           args are a subtype of sub_arg and the return type is supertype, and take the union (base_case_exists)
           of all those combinations *)
        is_subtype
          (build_structured_type super_arg context2)
          (build_structured_type arg context1))
      function_union
  in
  (* It is a subtype if the return types of all functions with argument subtypes form a supertype *)
  let composite_return = extract_composite_return relevant_functions in
  is_subtype_union_rec
    (build_structured_type return context1)
    (build_structured_type composite_return context2)
    encountered_type_vars

(* Will need to return whatever compound expression we need. Sometimes may be true directly *)
and is_func_subtype_compatible
    (((arg1, return1), context1) : unary_function * recursive_context)
    (((arg2, return2), context2) : unary_function * recursive_context)
    (encountered_type_vars : TypeVarUnionSet.t) =
  let args_dont_intersect = fun () -> not
    (has_intersection
      (build_structured_type arg1 context1)
      (build_structured_type arg2 context2))
  in
  let return_subtype = fun () ->
    is_subtype_union_rec
      (build_structured_type return1 context1)
      (build_structured_type return2 context2)
      encountered_type_vars
  in
  (* Two unary function are subtype-compatible if their arguments don't
     intersect, or they do intersect, but the return type is a subtype (to
     guarantee the function cannot return a supertype for the intersecting
     argument) *)
  short_circuit_or args_dont_intersect return_subtype
