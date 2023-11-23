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
(* TODO: consider requiring that inductive types are indeed well-founded, at least at this level of abstraction *)
(* TODO: consider requiring that recursive types are non-empty lists *)

module TypeVarSet = Set.Make (struct
  type t = int

  let compare = compare
end)

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
type base_case_disjunction = base_case_conjunction * base_case_conjunction list
type base_case_expr = False | True of base_case_disjunction
type base_case_thunk = unit -> base_case_expr

let to_base_case_expr (bool : bool) =
  if bool then True (TypeVarLoop.empty, []) else False

let is_true (expr : base_case_expr) =
  match expr with
  | True (first, rest) -> List.length rest = 0 && TypeVarLoop.is_empty first
  | _ -> false

let norm_dis (dis : base_case_disjunction) =
  let first, rest = dis in
  first :: rest

(* Merges a single conjunction into a normalized disjunction, producing a normalized disjunction *)
let union_single_conjunction (disjunction : base_case_disjunction)
    (conjunction : base_case_conjunction) =
  let normalized_dis = norm_dis disjunction in
  let is_superset =
    List.exists
      (fun dis_elt -> TypeVarLoop.subset dis_elt conjunction)
      normalized_dis
  in
  (* If the conjunction is a superset of an elements in the disjunction, don't change anything *)
  if is_superset then disjunction
  else
    (* Otherwise, use all non-supersets of the conjunction, and add the conjunction to the result *)
    let non_supersets =
      List.filter
        (fun dis_elt -> not (TypeVarLoop.subset conjunction dis_elt))
        normalized_dis
    in
    (conjunction, non_supersets)

(* Merges two normalized disjunctions, producting a normalized disjunction *)
let union_disjunctions (dis1 : base_case_disjunction)
    (dis2 : base_case_disjunction) =
  List.fold_left
    (fun dis con -> union_single_conjunction dis con)
    dis1 (norm_dis dis2)

let base_case_or_short_circuit (exp : base_case_expr) (thunk : base_case_thunk)
    =
  match exp with
  | False -> thunk ()
  | True a -> (
      if
        (* Avoid evaluting second thunk if first expression is unconditionally true *)
        is_true exp
      then exp
      else
        let exp2 = thunk () in
        match exp2 with False -> exp | True b -> True (union_disjunctions a b))

let base_case_or (thunk1 : base_case_thunk) (thunk2 : base_case_thunk) =
  base_case_or_short_circuit (thunk1 ()) thunk2

let rec base_case_exists (thunks : base_case_thunk list) =
  match thunks with
  | [] -> False
  | first :: rest -> base_case_exists_rec (first ()) rest

and base_case_exists_rec (curr : base_case_expr) (thunks : base_case_thunk list)
    =
  match thunks with
  | [] -> curr
  | first :: rest ->
      base_case_exists_rec (base_case_or_short_circuit curr first) rest

let disjunction_product (dis1 : base_case_disjunction)
    (dis2 : base_case_disjunction) : base_case_disjunction =
  let dis_pairs = list_product (norm_dis dis1) (norm_dis dis2) in
  let dis_list =
    List.map (fun (first, second) -> TypeVarLoop.union first second) dis_pairs
  in
  (* This is safe because the product of two lists of length at least 1 should also have length at least 1 *)
  (List.hd dis_list, List.tl dis_list)

let base_case_and_short_circuit (exp : base_case_expr)
    (thunk : base_case_thunk) =
  match exp with
  (* If first expression is false, we avoid evaluating the second thunk *)
  | False -> False
  | True a -> (
      let exp2 = thunk () in
      match exp2 with
      | False -> False
      | True b -> True (disjunction_product a b))

let base_case_and (thunk1 : base_case_thunk) (thunk2 : base_case_thunk) =
  base_case_and_short_circuit (thunk1 ()) thunk2

let rec base_case_for_all (thunks : base_case_thunk list) =
  match thunks with
  | [] -> to_base_case_expr true
  | first :: rest -> base_case_for_all_rec (first ()) rest

and base_case_for_all_rec (exp : base_case_expr) (thunks : base_case_thunk list)
    =
  match thunks with
  | [] -> exp
  | first :: rest ->
      base_case_for_all_rec (base_case_and_short_circuit exp first) rest

let rec multi_intersection (conjunctions : base_case_conjunction list) =
  match conjunctions with
  | [] -> TypeVarLoop.empty
  | [ conj ] -> conj
  | first :: second :: rest ->
      multi_intersection (TypeVarLoop.inter first second :: rest)

let build_structured_type (union : union_type) (context : recursive_context) =
  { union; context }

let build_recursive_def (kind : recursive_kind) (flat_union : flat_union_type) :
    recursive_def =
  { kind; flat_union }

let build_recursive_context (defs : (recursive_kind * flat_union_type) list) :
    recursive_context =
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
      (* If we encounter a loop, intersection exists between two coinductive, but not
         if inductive types are involved at all, since they require a well-founded intersection *)
      if TypeVarPairSet.mem (n, m) encountered_type_vars then
        (List.nth c1 n).kind = Coinductive && (List.nth c2 m).kind = Coinductive
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

(* TODO: maybe inductive types that aren't well-founded should be considered unary? Maybe covered if we restrict
   recursive types to be non-empty lists, require inductive types to be well-founded as well *)

(** [is_unary union_type] determines if a type cannot be written as the union of two distinct, unrelated types *)
let rec is_unary (t : structured_type) = is_unary_rec t TypeVarSet.empty

and is_unary_rec (t : structured_type) (encountered_type_vars : TypeVarSet.t) =
  let type_var_num =
    if List.length t.union = 1 then
      match List.hd t.union with TypeVar n -> Some n | _ -> None
    else None
  in
  let is_type_var = Option.is_some type_var_num in
  let loop_encountered =
    is_type_var
    && TypeVarSet.mem (Option.get type_var_num) encountered_type_vars
  in
  (* If we encounter a type variable loop, then we can assume it is unary, barring evidence along other branches *)
  if loop_encountered then true
  else
    (* Add the type variable to the set to track the next loops, if applicable *)
    let new_encountered_vars =
      if is_type_var then
        TypeVarSet.add (Option.get type_var_num) encountered_type_vars
      else encountered_type_vars
    in
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
                is_unary_rec
                  (build_structured_type arg t.context)
                  new_encountered_vars
                && is_unary_rec
                     (build_structured_type return t.context)
                     new_encountered_vars)
              functions)
    (* A multiple type union is not considered unary. In theory it may be possible to rewrite as a single base type
       but we can do that later *)
    | _ :: _ -> false

(** [is_subtype type1 type2] determines if [type1] is a subtype of [type2] *)
let rec is_subtype (t1 : structured_type) (t2 : structured_type) =
  let thunk = is_subtype_union_rec t1 t2 TypeVarLoop.empty in
  is_true (thunk ())

(* Returns a single base case expression, for use in most places *)
and is_subtype_union_rec (t1 : structured_type) (t2 : structured_type)
    (encountered_type_vars : TypeVarLoop.t) () =
  (* A union type is a subtype of another union type, if each base type in the first union is a subtype
     of the second union *)
  base_case_for_all (is_subtype_union_rec_destruct t1 t2 encountered_type_vars)

(* Returns each base case expression separately, so we can process inductive base cases *)
and is_subtype_union_rec_destruct (t1 : structured_type) (t2 : structured_type)
    (encountered_type_vars : TypeVarLoop.t) =
  List.map
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
    (t : structured_type) (encountered_type_vars : TypeVarLoop.t) () =
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
    (t : structured_type) (encountered_type_vars : TypeVarLoop.t) () =
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
    && TypeVarLoop.mem (var_num, t.union) encountered_type_vars
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
       then True (TypeVarLoop.singleton (var_num, t.union), [])
       else False
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
          let normed_disjunctions = List.map norm_dis disjunctions in
          let dis_combos = multi_list_product normed_disjunctions in
          let resolved_disjunctions =
            List.filter_map
              (fun dis_combo ->
                if
                  (* If there are no loop dependencies, there are no base cases to resolve *)
                  List.for_all
                    (fun conj -> not (TypeVarLoop.mem (var_num, t.union) conj))
                    dis_combo
                then Some (multi_intersection dis_combo)
                  (* Otherwise, if there is one conjunction that doesn't contain a loop, we found the base case, so resolve it from the dependencies *)
                else if
                  List.exists
                    (fun conj -> not (TypeVarLoop.mem (var_num, t.union) conj))
                    dis_combo
                then
                  let base_conjunction = multi_intersection dis_combo in
                  Some (TypeVarLoop.remove (var_num, t.union) base_conjunction)
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
    (encountered_type_vars : TypeVarLoop.t) () =
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
    (encountered_type_vars : TypeVarLoop.t) () =
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
    (encountered_type_vars : TypeVarLoop.t) () =
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
    (encountered_type_vars : TypeVarLoop.t) () =
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
    (encountered_type_vars : TypeVarLoop.t) () =
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
    (encountered_type_vars : TypeVarLoop.t) () =
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
