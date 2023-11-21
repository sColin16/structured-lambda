open Helpers

type 'a union = 'a list
type 'a intersection = 'a list

type structured_type = { union : union_type; context : recursive_context }
and union_type = base_type list

and base_type =
  | Label of string
  | Intersection of unary_function list
  | TypeVar of int

and unary_function = union_type * union_type
and recursive_context = recursive_def list
and flat_union_type = flat_base_type list
and flat_base_type = FLabel of string | FIntersection of unary_function list
and recursive_def = { kind : recursive_kind; flat_union : flat_union_type }
and recursive_kind = Inductive | Coinductive

module TypeVarPairSet = Set.Make (struct
  type t = int * int

  let compare = compare
end)

module TypeVarLoop = Set.Make (struct
  type t = int * union_type

  let compare = compare
end)

module TypeContextMap = Map.Make (struct
  type t = int

  let compare = compare
end)

type type_context_map = union_type TypeContextMap.t

(* Represents an expression that must have an inductive base case for the expression to be true *)
type base_case_conjunction = TypeVarLoop.t
type base_case_disjunction = base_case_conjunction list
type base_case_expr = False | True of base_case_disjunction

let build_structured_type (union : union_type) (context : recursive_context) =
  { union; context }

let build_recursive_def (kind : recursive_kind) (flat_union : flat_union_type): recursive_def
    =
  { kind; flat_union }

let build_recursive_context (defs: (recursive_kind * flat_union_type) list): recursive_context =
  List.map (fun (kind, union) -> build_recursive_def kind union) defs

(* TODO: remove duplicate and subtypes from the union after flattening *)
let extract_composite_args (branches : unary_function list) =
  List.flatten (extract_first branches)

let extract_composite_return (branches : unary_function list) =
  List.flatten (extract_second branches)

(* TODO: consider just accepting a structured type here *)
let flatten_union (union : union_type) (context : recursive_context) :
    flat_union_type =
  List.flatten
    (List.map
       (fun base_type ->
         match base_type with
         | Label a -> [ FLabel a ]
         | Intersection a -> [ FIntersection a ]
         | TypeVar n -> (List.nth context n).flat_union)
       union)

(* TODO: consider just accepted a structured type here *)
let flatten_union_contractive (union : union_type) (context : recursive_context)
    =
  let flat_union = flatten_union union context in
  let converted_union =
    List.map
      (fun base_type ->
        match base_type with
        | FLabel a -> Label a
        | FIntersection functions -> Intersection functions)
      flat_union
  in
  build_structured_type converted_union context

let expand_type_var_contractive (var_num : int) (context : recursive_context) =
  let flat_union = (List.nth context var_num).flat_union in
  let converted_union =
    List.map
      (fun base_type ->
        match base_type with
        | FLabel a -> Label a
        | FIntersection a -> Intersection a)
      flat_union
  in
  build_structured_type converted_union context

(** [has_intersection type1 type2] determines if the intersection of the two types is inhabited
    More specfically, determines if there exists a subtype of the intersection of the two types, other than the bottom type *)
let rec has_intersection (t1 : structured_type) (t2 : structured_type) =
  has_intersection_rec t1 t2 TypeVarPairSet.empty

and has_intersection_rec (t1 : structured_type) (t2 : structured_type)
    (encountered_type_vars : TypeVarPairSet.t) =
  let base_pairs = list_product t1.union t2.union in
  List.exists
    (fun (b1, b2) ->
      has_intersection_base_rec (b1, t1.context) (b2, t2.context)
        encountered_type_vars)
    base_pairs

and has_intersection_base_rec ((t1, c1) : base_type * recursive_context)
    ((t2, c2) : base_type * recursive_context)
    (encountered_type_vars : TypeVarPairSet.t) =
  match (t1, t2) with
  (* First, handle the true base/base pairs *)
  (* Two labels have an intersection only when they're equal *)
  | Label a, Label b -> a = b
  (* unit/top type intersected with any type is that type *)
  | _, Intersection [] | Intersection [], _ -> true
  (* Non-empty intersections and labels have have uninhabited intersections *)
  | Label _, Intersection (_ :: _) | Intersection (_ :: _), Label _ -> false
  (* The intersection of two non-unit function intersection types is inhabited if each pair of unary function types is inhabited *)
  | Intersection first, Intersection second ->
      let function_pairs = list_product first second in
      List.for_all
        (fun (f1, f2) ->
          has_intersection_func (f1, c1) (f2, c2) encountered_type_vars)
        function_pairs
  (* Handle cases where one of the types is a type variable, expanding that type out and recursing *)
  | TypeVar n, Label _ | TypeVar n, Intersection _ ->
      has_intersection_rec
        (expand_type_var_contractive n c1)
        (build_structured_type [ t2 ] c2)
        encountered_type_vars
  | Label _, TypeVar n | Intersection _, TypeVar n ->
      has_intersection_rec
        (build_structured_type [ t1 ] c1)
        (expand_type_var_contractive n c2)
        encountered_type_vars
  (* Finally, handle the potential loop case *)
  | TypeVar n, TypeVar m ->
      (* If we encounter a loop, we assume an intersection exists due to
         coinductive typing. This will be false for inductive types, which require a
         well-founded intersection *)
      if TypeVarPairSet.mem (n, m) encountered_type_vars then true
      else
        (* If we don't encounter a loop, we expand both sides and recurse, tracking this pair to detect a future loop *)
        has_intersection_rec
          (expand_type_var_contractive n c1)
          (expand_type_var_contractive m c2)
          (TypeVarPairSet.add (n, m) encountered_type_vars)

and has_intersection_func
    (((arg1, return1), c1) : unary_function * recursive_context)
    (((arg2, return2), c2) : unary_function * recursive_context)
    (encountered_type_vars : TypeVarPairSet.t) =
  let args_intersect =
    has_intersection_rec
      (build_structured_type arg1 c1)
      (build_structured_type arg2 c2)
      encountered_type_vars
  in
  let returns_intersect =
    has_intersection_rec
      (build_structured_type return1 c1)
      (build_structured_type return2 c2)
      encountered_type_vars
  in
  (* Unary function intersection is inhabited if the argument types don't intersect (intersection
     is simply the ad-hoc polymorphic function), or if the argument types do intersect, but the return
     types do as well (the intersecting argument component maps to the intersection
     of the return types) *)
  (not args_intersect) || returns_intersect

(** [is_unary union_type] determines if a type cannot be written as the union of two distinct, unrelated types *)
let rec is_unary (t : structured_type) =
  let flat_union = flatten_union t.union t.context in
  match flat_union with
  (* Under the rewriting equality rule, the empty type is considered "unary" even though it's really more nullary *)
  | [] -> true
  (* A single type in a union is considered unary if the corresponding base type *)
  | [ base ] -> (
      match base with
      (* Labels are unary be definition *)
      | FLabel _ -> true
      (* Functions are unary if all their argument and return types are unary *)
      | FIntersection functions ->
          List.for_all
            (fun (arg, return) ->
              is_unary (build_structured_type arg t.context)
              && is_unary (build_structured_type return t.context))
            functions)
  (* A multiple type union is not considered unary. In theory it may be possible to rewrite as a single base type
     but we can do that later *)
  | _ :: _ -> false

(** [is_subtype type1 type2] determines if [type1] is a subtype of [type2] *)
let rec is_subtype (t1 : structured_type) (t2 : structured_type) =
  is_subtype_union_rec t1 t2 TypeVarLoop.empty

(* This would return a list of all the base union types it encounters instead, so caller can process *)
(* We might have a helper that can return a unified result, for callers that don't need to process individual elements *)
and is_subtype_union_rec (t1 : structured_type) (t2 : structured_type)
    (encountered_type_vars : TypeVarLoop.t) =
  (* A union type is a subtype of another union type, if each base type in the first union is a subtype
     of the second union *)
  List.for_all
    (fun base_type ->
      is_base_union_subtype (base_type, t1.context) t2 encountered_type_vars)
    t1.union

and is_base_union_subtype ((t1, c1) : base_type * recursive_context)
    (t2 : structured_type) (encountered_type_vars : TypeVarLoop.t) =
  match t1 with
  | Label a -> is_label_union_subtype a t2
  | Intersection functions ->
      is_function_union_subtype (functions, c1) t2 encountered_type_vars
  | TypeVar n -> is_typevar_union_subtype (n, c1) t2 encountered_type_vars

(* Should always be able to return a definitive true/false *)
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

(* Must return a union of the compound structure *)
and is_function_union_subtype
    ((functions, context1) : unary_function intersection * recursive_context)
    (t : structured_type) (encountered_type_vars : TypeVarLoop.t) =
  (* Flatten the type with contractivity to only labels and intersections *)
  let flat_union = flatten_union t.union t.context in
  (* Filter out the label types because they don't assist in subtypeing an intersection *)
  let union_of_intersections =
    List.filter_map
      (fun base_type ->
        match base_type with
        | FLabel _ -> None
        | FIntersection functions -> Some functions)
      flat_union
  in
  (* First, check if there a intersection types in the union that is a supertype directly *)
  let is_direct_subtype =
    is_function_subtype_direct (functions, context1)
      (union_of_intersections, t.context)
      encountered_type_vars
  in
  if is_direct_subtype then true
  else
    (* Otherwise, check if it's an indirect subtype of the entire union *)
    let is_indirect_subtype =
      is_function_subtype_indirect (functions, context1)
        (union_of_intersections, t.context)
        encountered_type_vars
    in
    is_indirect_subtype

(* Must return the compound structure, be able to create it as a base case, and introspect return of recursive case to determine outcome of loops *)
and is_typevar_union_subtype ((var_num, context1) : int * recursive_context)
    (t : structured_type) (encountered_type_vars : TypeVarLoop.t) =
  let union_contains_typevars =
    List.exists
      (fun base_type ->
        match base_type with
        | TypeVar _ -> true
        | Label _ | Intersection _ -> false)
      t.union
  in
  (* If we encounter a loop with type vars, subtyping is valid for coninductive types.
     For inductive types, we will need to perform additional checks *)
  if
    union_contains_typevars
    && TypeVarLoop.mem (var_num, t.union) encountered_type_vars
  then true
  else
    (* Otherwise, expand both sides, removing all type vars *)
    let expanded_type_var = expand_type_var_contractive var_num context1 in
    let flat_union = flatten_union_contractive t.union t.context in
    (* If the original union had type vars, track it for loop detection *)
    let new_encountered_var =
      if union_contains_typevars then
        TypeVarLoop.add (var_num, t.union) encountered_type_vars
      else encountered_type_vars
    in
    (* And recurse on both sides *)
    is_subtype_union_rec expanded_type_var flat_union new_encountered_var

(* Returns the compound structure. Must be able to union the compound structure *)
and is_function_subtype_direct
    ((functions, context1) : unary_function intersection * recursive_context)
    ((union_of_intersections, context2) :
      unary_function intersection union * recursive_context)
    (encountered_type_vars : TypeVarLoop.t) =
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
    (encountered_type_vars : TypeVarLoop.t) =
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
      let does_subtype =
        List.for_all
          (fun union_supertype ->
            is_intersection_union_subtype
              (unary_form_functions, context1)
              (union_supertype, context2)
              encountered_type_vars)
          intersection_of_unions
      in
      does_subtype

(* Must return the compound structure. Must intersect multiple compound structures *)
and is_intersection_subtype
    ((functions1, context1) : unary_function intersection * recursive_context)
    ((functions2, context2) : unary_function intersection * recursive_context)
    (encountered_type_vars : TypeVarLoop.t) =
  let first_args = extract_composite_args functions1 in
  let second_args = extract_composite_args functions2 in
  let function_pairs = list_product functions1 functions2 in
  (* The function1's argument types (unioned together) must be a supertype of function2's argument types (unioned together) *)
  let exhaustive_arg_coverage =
    is_subtype_union_rec
      (build_structured_type second_args context2)
      (build_structured_type first_args context1)
      encountered_type_vars
  in
  (* Every pair of unary functions must be "subtype compatible," returning a subtype is the arg types intersect *)
  let return_type_constraint =
    List.for_all
      (fun (func1, func2) ->
        is_func_subtype_compatible (func1, context1) (func2, context2)
          encountered_type_vars)
      function_pairs
  in
  exhaustive_arg_coverage && return_type_constraint

(* Must return a union of the compound structure *)
and is_intersection_union_subtype
    ((unary_form_functions, context1) :
      unary_function intersection * recursive_context)
    ((function_union, context2) : unary_function union * recursive_context)
    (encountered_type_vars : TypeVarLoop.t) =
  (* We must prove that one function type in the unary form intersection is a subtype of the union *)
  List.exists
    (fun (sub_arg, sub_return) ->
      let relevant_functions =
        List.filter
          (fun (super_arg, _) ->
            is_subtype_union_rec
              (build_structured_type super_arg context2)
              (build_structured_type sub_arg context1)
              encountered_type_vars)
          function_union
      in
      let composite_return = extract_composite_return relevant_functions in
      (* It is a subtype if the return types of all functions with argument subtypes form a supertype *)
      is_subtype_union_rec
        (build_structured_type sub_return context1)
        (build_structured_type composite_return context2)
        encountered_type_vars)
    unary_form_functions

(* Will need to return whatever compound expression we need. Sometimes may be true directly *)
and is_func_subtype_compatible
    (((arg1, return1), context1) : unary_function * recursive_context)
    (((arg2, return2), context2) : unary_function * recursive_context)
    (encountered_type_vars : TypeVarLoop.t) =
  let args_intersect =
    has_intersection
      (build_structured_type arg1 context1)
      (build_structured_type arg2 context2)
  in
  let return_subtype =
    is_subtype_union_rec
      (build_structured_type return1 context1)
      (build_structured_type return2 context2)
      encountered_type_vars
  in
  (* Two unary function are subtype-compatible if their arguments don't
     intersect, or they do intersect, but the return type is a subtype (to
     guarantee the function cannot return a supertype for the intersecting
     argument) *)
  (not args_intersect) || return_subtype

(** [get_application_type func_type arg_type] determines the resulting type of
    applying a term of type [arg_type] to a term of type [func_type], if
    the function can be applied to the argument *)
let rec get_application_type (func : structured_type) (arg : structured_type) :
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
