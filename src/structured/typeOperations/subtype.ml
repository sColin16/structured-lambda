open Common.Helpers
open Helpers
open BaseCaseAlgebra
open Metatypes
open Unary
open Intersection

(** [is_subtype type1 type2] determines if [type1] is a subtype of [type2] *)
let rec is_subtype (t1 : structured_type) (t2 : structured_type) =
  let thunk = is_subtype_union_rec t1 t2 TypeVarUnionSet.empty in
  is_true (thunk ())

(* Returns a single base case expression, for use in most places *)
and is_subtype_union_rec (t1 : structured_type) (t2 : structured_type)
    (encountered_type_vars : TypeVarUnionSet.t) () =
  (* A union type is a subtype of another union type, if each base type in the first union is a subtype
     of the second union *)
  base_case_for_all (is_subtype_union_rec_destruct t1 t2 encountered_type_vars)

(* Returns each base case expression separately, so we can process inductive base cases *)
and is_subtype_union_rec_destruct (t1 : structured_type) (t2 : structured_type)
    (encountered_type_vars : TypeVarUnionSet.t) =
  List.map
    (fun base_type ->
      is_base_union_subtype (base_type, t1.context) t2 encountered_type_vars)
    t1.union

and is_base_union_subtype ((t1, c1) : base_type * recursive_context)
    (t2 : structured_type) (encountered_type_vars : TypeVarUnionSet.t) =
  match t1 with
  | Label a -> is_label_union_subtype a t2
  | Intersection functions ->
      is_function_union_subtype (functions, c1) t2 encountered_type_vars
  | TypeVar n -> is_typevar_union_subtype (n, c1) t2 encountered_type_vars

and is_label_union_subtype (label : string) (t : structured_type) () =
  let flat_union = flatten_union t.union t.context in
  (* A label is a subtype of an equivalent label in the union, or the top type *)
  let has_supertype =
    List.exists
      (fun flat_union_elt ->
        match flat_union_elt with
        | FLabel a -> a = label
        | FIntersection [] -> true
        | FIntersection (_ :: _) -> false)
      flat_union
  in
  to_base_case_expr has_supertype

and is_function_union_subtype
    ((functions, context1) : unary_function intersection * recursive_context)
    (t : structured_type) (encountered_type_vars : TypeVarUnionSet.t) () =
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
  (* Otherwise, check if it's an indirect subtype of the entire union *)
  let is_indirect_subtype =
    is_function_subtype_indirect (functions, context1)
      (union_of_intersections, t.context)
      encountered_type_vars
  in
  base_case_or is_direct_subtype is_indirect_subtype

and is_typevar_union_subtype ((var_num, context1) : int * recursive_context)
    (t : structured_type) (encountered_type_vars : TypeVarUnionSet.t) () =
  let union_contains_typevars =
    List.exists
      (fun base_type ->
        match base_type with
        | TypeVar _ -> true
        | Label _ | Intersection _ -> false)
      t.union
  in
  let var_num_kind = (List.nth context1 var_num).kind in
  (* If we encounter a loop with type vars, subtyping is valid for coninductive types.
     For inductive types, we will need to perform additional checks *)
  if
    union_contains_typevars
    && TypeVarUnionSet.mem (var_num, t.union) encountered_type_vars
  then
    let union_kinds =
         List.filter_map
           (fun base_type ->
             match base_type with
             | TypeVar n -> Some (List.nth t.context n).kind
             | Label _ | Intersection _ -> None)
           t.union
       in
    (* Coinductive/coinductive loops have no dependencies, like before *)
    if
         var_num_kind = Coinductive
         && List.for_all (fun kind -> kind = Coinductive) union_kinds
       then to_base_case_expr true
       else if
         (* Coinductive/inductive loops fail: subtype may contain infinite type that inductive types do not *)
         var_num_kind = Coinductive
         && List.exists (fun kind -> kind = Inductive) union_kinds
       then False
       else if
         (* Inductive loops of any kind just require a base case, so track that *)
         var_num_kind = Inductive
       then True (TypeVarUnionSet.singleton (var_num, t.union), [])
       else False
  else
    (* Otherwise, expand both sides, removing all type vars *)
    let expanded_type_var = expand_type_var_contractive var_num context1 in
    let flat_union = flatten_union_contractive t.union t.context in
    (* If the original union had type vars, track it for loop detection *)
    let new_encountered_var =
      if union_contains_typevars then
        TypeVarUnionSet.add (var_num, t.union) encountered_type_vars
      else encountered_type_vars
    in
    (* If this type variable is coinductive, we shouldn't encounter loops, so just recurse *)
    if var_num_kind = Coinductive then
      let is_subtype_thunk = is_subtype_union_rec expanded_type_var flat_union new_encountered_var in
      is_subtype_thunk ()
    else
      (* The type variable is inductive, so we need to resolve base case logic *)
      let destruct_exprs =
        is_subtype_union_rec_destruct expanded_type_var flat_union
          new_encountered_var
      in
      (* TODO: consider doing a smarter reduction here to avoid evaluating thunks if we encounter a false term *)
      let expr_opts =
        List.map
          (fun thunk -> match thunk () with False -> None | True a -> Some a)
          destruct_exprs
      in
      let dis_opt = opt_list_to_list_opt expr_opts in
      match dis_opt with
      | None -> False
      | Some disjunctions ->
          let normed_disjunctions = List.map flatten_disjunction disjunctions in
          let dis_combos = multi_list_product normed_disjunctions in
          let resolved_disjunctions =
            List.filter_map
              (fun dis_combo ->
                if
                  (* If there are no loop dependencies, there are no base cases to resolve *)
                  List.for_all
                    (fun conj -> not (TypeVarUnionSet.mem (var_num, t.union) conj))
                    dis_combo
                then Some (and_conjunctions dis_combo)
                  (* Otherwise, if there is one conjunction that doesn't contain a loop, we found the base case, so resolve it from the dependencies *)
                else if
                  List.exists
                    (fun conj -> not (TypeVarUnionSet.mem (var_num, t.union) conj))
                    dis_combo
                then
                  let base_conjunction = and_conjunctions dis_combo in
                  Some (TypeVarUnionSet.remove (var_num, t.union) base_conjunction)
                  (* Otherwise, we can't resolve the base case, so this combo resolves to false *)
                else None)
              dis_combos
          in
          (* If we were able to resolve at least one combination, we're set. Otherwise, everything required a base case but there were none *)
          if List.length resolved_disjunctions >= 1 then
            True (List.hd resolved_disjunctions, List.tl resolved_disjunctions)
          else False

(* Returns the compound structure. Must be able to union the compound structure *)
and is_function_subtype_direct
    ((functions, context1) : unary_function intersection * recursive_context)
    ((union_of_intersections, context2) :
      unary_function intersection union * recursive_context)
    (encountered_type_vars : TypeVarUnionSet.t) () =
  (* Check if an intersection exists in the union type that is a direct supertype of the function in question *)
  let exprs =
    List.map
      (fun intersection_supertype ->
        is_intersection_subtype (functions, context1)
          (intersection_supertype, context2)
          encountered_type_vars)
      union_of_intersections
  in
  base_case_exists exprs

(* Must return an intersection of the compound structure *)
and is_function_subtype_indirect
    ((functions, context1) : unary_function intersection * recursive_context)
    ((union_of_intersections, context2) :
      unary_function intersection union * recursive_context)
    (encountered_type_vars : TypeVarUnionSet.t) () =
  match union_of_intersections with
  (* If there are 0 or 1 types in the union, we cannot distribute a union, so direct function subtyping would be required *)
  | [] | [ _ ] -> False
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
      let exprs =
        List.map
          (fun union_supertype ->
            is_intersection_union_subtype
              (unary_form_functions, context1)
              (union_supertype, context2)
              encountered_type_vars)
          intersection_of_unions
      in
      base_case_for_all exprs

(* Must return the compound structure. Must intersect multiple compound structures *)
and is_intersection_subtype
    ((functions1, context1) : unary_function intersection * recursive_context)
    ((functions2, context2) : unary_function intersection * recursive_context)
    (encountered_type_vars : TypeVarUnionSet.t) () =
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
  let return_type_constraint_exprs =
    List.map
      (fun (func1, func2) ->
        is_func_subtype_compatible (func1, context1) (func2, context2)
          encountered_type_vars)
      function_pairs
  in
  base_case_and exhaustive_arg_coverage (fun () ->
      base_case_for_all return_type_constraint_exprs)

(* Must return a union of the compound structure *)
and is_intersection_union_subtype
    ((unary_form_functions, context1) :
      unary_function intersection * recursive_context)
    ((function_union, context2) : unary_function union * recursive_context)
    (encountered_type_vars : TypeVarUnionSet.t) () =
  (* We must prove that one function type in the unary form intersection is a subtype of the union *)
  let exprs =
    List.map
      (fun (sub_arg, sub_return) ->
        is_unary_func_union_subtype
          ((sub_arg, sub_return), context1)
          (function_union, context2) encountered_type_vars)
      unary_form_functions
  in
  base_case_exists exprs

and is_unary_func_union_subtype
    (((arg, return), context1) : unary_function * recursive_context)
    ((function_union, context2) : unary_function union * recursive_context)
    (encountered_type_vars : TypeVarUnionSet.t) () =
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
  let is_subtype_thunk =
    is_subtype_union_rec
      (build_structured_type return context1)
      (build_structured_type composite_return context2)
      encountered_type_vars
  in
  is_subtype_thunk ()

(* Will need to return whatever compound expression we need. Sometimes may be true directly *)
and is_func_subtype_compatible
    (((arg1, return1), context1) : unary_function * recursive_context)
    (((arg2, return2), context2) : unary_function * recursive_context)
    (encountered_type_vars : TypeVarUnionSet.t) () =
  let args_intersect =
    has_intersection
      (build_structured_type arg1 context1)
      (build_structured_type arg2 context2)
  in
  let args_no_intersect_expr = fun () -> to_base_case_expr (not args_intersect) in
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
  base_case_or args_no_intersect_expr return_subtype