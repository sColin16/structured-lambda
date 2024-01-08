open Metatypes
open TermTypes
open Common.Helpers
open ShiftUnivVar
open TypeOperations.Context
open TypeOperations.Create
open TypeOperations.Helpers

(* Substitutes the [with_type] into the [in_term] for universal type variables referencing
   the universal quantification at this level (0, or higher if nested within another universal quantifications) *)
let rec substitute_univ_var_term (with_type : structured_type) (in_term : term) : term =
  (* Shift the universal type indices in the argument by one since it is about to be substituted into a universal quantification,
    where their binding quantification is one further away *)
  let shifted_with_type = shift_univ_var_type with_type 1 in
  (* Perform the substitution on universal quantification variables that are bound to this universal quantification *)
  let substitution_result =
    substitute_univ_var_term_rec 0 shifted_with_type in_term
  in
  (* Finally shift everything down one since we remove a universal quantification where
     the binding quantification is one closer *)
  let final_result = shift_univ_var_term substitution_result (-1) in
  final_result

(* I believe we want the shifting logic here so that typing can call this to perform a type substitution *)
and substitute_univ_var_type (with_type: structured_type) (in_type: structured_type): structured_type =
  (* Shift the free universal type variables in the with type by one, since they are about to be substituted into a universal quantification,
     where their binding quantification is further away *)
  let shifted_with_type = shift_univ_var_type with_type 1 in
  (* Perform the substitution on universal quantification variables bound to this outermost universal quantification *)
  let substitution_result = substitute_univ_var_type_rec 0 shifted_with_type in_type in
  (* Finally, shift all the free universal type variables down one since we can now remove the outermost universal quantification,
     and so all free universal type variables move one closer to their binding quantifier *)
  let final_result = shift_univ_var_type substitution_result (-1) in
  final_result

and substitute_univ_var_term_rec (variable_num : int)
    (with_type : structured_type) (in_term : term) : term =
  match in_term with
  (* Variables and constants have nothing to substitute *)
  | Variable _ | Const _ -> in_term
  (* Applications are substituted recursively *)
  | Application (left_term, right_term) ->
      let left_subst, right_subst = map_pair (substitute_univ_var_term_rec variable_num with_type) (left_term, right_term) in
      Application (left_subst, right_subst)
  (* Abstractions are recursive, but we substitute in the term and types separately *)
  | Abstraction branches ->
      let substituted_branches =
        List.map
          (fun (branch_type, branch_body) ->
            ( substitute_univ_var_type_rec variable_num with_type branch_type,
              substitute_univ_var_term_rec variable_num with_type branch_body ))
          branches
      in
      Abstraction substituted_branches
  (* Universal application is also substituted recursively for the term and type *)
  | UnivApplication (inner_term, inner_type) ->
    UnivApplication
      ( substitute_univ_var_term_rec variable_num with_type inner_term,
        substitute_univ_var_type_rec variable_num with_type inner_type )
  (* Universal quantifiers require special logic to honor the de Bruijn indices *)
  | UnivQuantifier inner_term ->
    (* We increment the variable we substitute for by one since we are descending through another quantifier *)
    let new_var_num = variable_num + 1 in
    (* We shift the variables in the with type by one since the type is about to be placed one quantifier deeper,
       and so the bounding quantifiers for the variables will be one further away *)
    let new_with_type = shift_univ_var_type with_type 1 in
    (* Perform the recursive substitution *)
    let substituted_inner_term = substitute_univ_var_term_rec new_var_num new_with_type inner_term in
    (* And wrap the substituted result in a quantifier again *)
    UnivQuantifier substituted_inner_term

and substitute_univ_var_type_rec (variable_num : int)
    (with_type: structured_type) (in_type : structured_type) : structured_type
    =
  (* Get the in_type in the context of the with_type so we can safely substitute
  in the with_type while any recursive type variables in the with_type still reference the same types *)
  let recontextualized_type = get_type_in_context in_type with_type.context in
  (* Substitute the universal type variables in the recontextualized type context *)
  let new_context = substitute_univ_var_context variable_num with_type recontextualized_type.context in
  (* Substitute the universal type variables in the recontextualized union type *)
  let new_union = substitute_univ_var_union variable_num with_type recontextualized_type.union in
  (* And then build the new type *)
  let new_structured_type = build_structured_type new_union new_context in
  new_structured_type

and substitute_univ_var_context (variable_num: int) (with_type: structured_type) (context: recursive_context) =
  List.map (substitute_univ_var_context_def variable_num with_type) context

and substitute_univ_var_context_def (variable_num: int) (with_type: structured_type) ({kind; flat_union}: recursive_def) =
  { kind; flat_union = substitute_univ_var_flat_union variable_num with_type flat_union }

and substitute_univ_var_flat_union (variable_num: int) (with_type: structured_type) (flat_union: flat_union_type) =
  (* Convert the union to the unflattened type *)
  let unflattened_union = unflatten_union flat_union in
  (* Perform the substitution on the unflattened type *)
  let substituted_union = substitute_univ_var_union variable_num with_type unflattened_union in
  (* Convert to a flat union, using the with_type context where recursive variables may be from*)
  let substituted_flat_union = flatten_union substituted_union with_type.context
  in substituted_flat_union

and substitute_univ_var_function (variable_num: int) (with_type: structured_type) (arg, return: unary_function) =
  map_pair (substitute_univ_var_union variable_num with_type) (arg, return)

and substitute_univ_var_union (variable_num: int) (with_type: structured_type) (union: union_type) =
  List.flatten (List.map (substitute_univ_var_base variable_num with_type) union)

and substitute_univ_var_base (variable_num: int) (with_type: structured_type) (base: base_type) =
  match base with
  (* Labels and recursive type variables don't need substitutions *)
  | Label _ | RecTypeVar _ -> [ base ]
  (* Intersections are substituted recursively *)
  | Intersection branches ->
    let substituted_branches = List.map (substitute_univ_var_function variable_num with_type) branches in
    [ Intersection substituted_branches ]
  (* Universal quantification requires special logic to honor the de Bruijn indices (which I believe do change passing through the quantifier type) *)
  | UnivQuantification inner_type ->
    let new_var_num = variable_num + 1 in
    let new_with_type = shift_univ_var_type with_type 1 in
    let substituted_inner_type = substitute_univ_var_union new_var_num new_with_type inner_type in
    [ UnivQuantification substituted_inner_type ]
  (* Type variables are substituted when they match the target variable number *)
  | UnivTypeVar num -> if num = variable_num then
    with_type.union else [ UnivTypeVar num ]
