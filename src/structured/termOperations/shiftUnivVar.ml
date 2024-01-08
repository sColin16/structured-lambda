open Metatypes
open TermTypes
open Common.Helpers
open TypeOperations.Create

(** Utilities for shifting universal quantification variables represented by de Bruijn indices *)

(** Shifts free universal type variables in a type by the shift amount *)
let rec shift_univ_var_type (stype : structured_type) (shift_amount : int) =
  shift_univ_var_type_rec shift_amount 0 stype

(** Shift free universal type variables in a term by the shift amount *)
and shift_univ_var_term (term : term) (shift_amount : int) =
  shift_univ_var_term_rec shift_amount 0 term

and shift_univ_var_term_rec (shift_amount : int) (cutoff : int) (term : term) =
  match term with
  (* Variables and consts don't need anything shifted *)
  | Variable _ | Const _ -> term
  (* Applications are shifted recursively *)
  | Application (left_term, right_term) ->
      let left_shifted, right_shifted =
        map_pair
          (shift_univ_var_term_rec shift_amount cutoff)
          (left_term, right_term)
      in
      Application (left_shifted, right_shifted)
  (* Abstractions are substituted recursively as well *)
  | Abstraction branches ->
      let shifted_branches =
        List.map
          (fun (branch_type, branch_body) ->
            ( shift_univ_var_type_rec shift_amount cutoff branch_type,
              shift_univ_var_term_rec shift_amount cutoff branch_body ))
          branches
      in
      Abstraction shifted_branches
  (* Universal applications are substituted recursively *)
  | UnivApplication (inner_term, inner_type) ->
      let term_shifted =
        shift_univ_var_term_rec shift_amount cutoff inner_term
      in
      let type_shifted =
        shift_univ_var_type_rec shift_amount cutoff inner_type
      in
      UnivApplication (term_shifted, type_shifted)
  (* Universal quantifiers increment the cutoff by one since the index of free variables increases by one when passing through a quantifier *)
  | UnivQuantifier inner_term ->
      UnivQuantifier
        (shift_univ_var_term_rec shift_amount (cutoff + 1) inner_term)

and shift_univ_var_type_rec (shift_amount : int) (cutoff : int)
    (stype : structured_type) =
  (* Shift the recursive context and union separately, then combine *)
  let shifted_context =
    shift_univ_var_context shift_amount cutoff stype.context
  in
  let shifted_union = shift_univ_var_union shift_amount cutoff stype.union in
  let shifted_type = build_structured_type shifted_union shifted_context in
  shifted_type

and shift_univ_var_context (shift_amount : int) (cutoff : int)
    (context : recursive_context) =
  List.map (shift_univ_var_context_def shift_amount cutoff) context

and shift_univ_var_context_def (shift_amount : int) (cutoff : int)
    ({ kind; flat_union } : recursive_def) =
  {
    kind;
    flat_union = shift_univ_var_flat_union shift_amount cutoff flat_union;
  }

and shift_univ_var_flat_union (shift_amount : int) (cutoff : int)
    (flat_union : flat_union_type) =
  List.map (shift_univ_var_flat_base shift_amount cutoff) flat_union

(* TODO: how can I reduce the amount of duplicate code with the other base version *)
and shift_univ_var_flat_base (shift_amount : int) (cutoff : int)
    (flat_base : flat_base_type) =
  match flat_base with
  (* Labels don't need any shifting *)
  | FLabel _ -> flat_base
  (* Intersections are shifted recursively *)
  | FIntersection branches ->
      let shifted_branches =
        List.map (shift_univ_var_func shift_amount cutoff) branches
      in
      FIntersection shifted_branches
  (* When we cross through a quantifier, we increment the cutoff since the index of free variables
     increases by one as we pass through the quantifier *)
  | FUnivQuantification inner_type ->
      FUnivQuantification
        (shift_univ_var_union shift_amount (cutoff + 1) inner_type)
  (* Universal type variables are shifted if they are at least the cutoff value, which means they are free variables *)
  | FUnivTypeVar num ->
      if num >= cutoff then FUnivTypeVar (num + shift_amount)
      else FUnivTypeVar num

and shift_univ_var_union (shift_amount : int) (cutoff : int)
    (union : union_type) =
  List.map (shift_univ_var_base shift_amount cutoff) union

and shift_univ_var_base (shift_amount : int) (cutoff : int) (base : base_type) =
  match base with
  (* Labels and recursive type variables don't need to be shifted (context is shifted separately) *)
  | Label _ | RecTypeVar _ -> base
  (* Intersections are shifted recursively *)
  | Intersection branches ->
      let shifted_branches =
        List.map (shift_univ_var_func shift_amount cutoff) branches
      in
      Intersection shifted_branches
  (* When we cross through a quantifier, we increment the cutoff since the index of free variables
     increases by one as we pass through the quantifier *)
  | UnivQuantification inner_type ->
      UnivQuantification
        (shift_univ_var_union shift_amount (cutoff + 1) inner_type)
  (* Universal type variables are shifted if they are at least the cutoff value, which means they are free variables *)
  | UnivTypeVar num ->
      if num >= cutoff then UnivTypeVar (num + shift_amount)
      else UnivTypeVar num

and shift_univ_var_func (shift_amount : int) (cutoff : int)
    ((arg, return) : unary_function) =
  map_pair (shift_univ_var_union shift_amount cutoff) (arg, return)
