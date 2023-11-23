open Helpers
open Metatypes

(* A boolean algebra that tracks expressions that must have base cases to be considered true *)
type base_case_conjunction = TypeVarUnionSet.t
type base_case_disjunction = base_case_conjunction * base_case_conjunction list
type base_case_expr = False | True of base_case_disjunction
type base_case_thunk = unit -> base_case_expr

(** Converts a boolean to the equivalent base-case expression *)
let to_base_case_expr (bool : bool) =
  if bool then True (TypeVarUnionSet.empty, []) else False

(** Determines if a base case expression is an unconditional true *)
let is_true (expr : base_case_expr) =
  match expr with
  | True (first, rest) -> List.length rest = 0 && TypeVarUnionSet.is_empty first
  | _ -> false

let flatten_disjunction ((first, rest) : base_case_disjunction) = first :: rest

(** Performs a boolean or on a normalized disjunction and a conjunction, producing a normalized disjunction *)
let or_single_conjunction (disjunction : base_case_disjunction)
    (new_conjunction : base_case_conjunction) =
  let flat_disjunction = flatten_disjunction disjunction in
  let is_superset =
    List.exists
      (fun conjunction -> TypeVarUnionSet.subset conjunction new_conjunction)
      flat_disjunction
  in
  (* If the conjunction is a superset of an elements in the disjunction, don't change anything *)
  if is_superset then disjunction
  else
    (* Otherwise, use all non-supersets of the conjunction, and add the conjunction to the result *)
    let non_supersets =
      List.filter
        (fun conjunction ->
          not (TypeVarUnionSet.subset new_conjunction conjunction))
        flat_disjunction
    in
    (new_conjunction, non_supersets)

(** Performs a boolean or on two more *)
let or_disjunctions (dis1 : base_case_disjunction)
    (dis2 : base_case_disjunction) =
  List.fold_left
    (fun dis con -> or_single_conjunction dis con)
    dis1 (flatten_disjunction dis2)

(** Helper to implement the core logic for boolean or *)
let base_case_or_helper (exp : base_case_expr) (thunk : base_case_thunk)
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
        match exp2 with False -> exp | True b -> True (or_disjunctions a b))

(** Performs boolean or over two base case thunks, with short circuiting *)
let base_case_or (thunk1 : base_case_thunk) (thunk2 : base_case_thunk) =
  base_case_or_helper (thunk1 ()) thunk2

let rec base_case_exists_rec (curr : base_case_expr) (thunks : base_case_thunk list)
    =
  match thunks with
  | [] -> curr
  | first :: rest ->
      base_case_exists_rec (base_case_or_helper curr first) rest

(** Equivalent to List.exists, but across base case thunks, with short-circuiting *)
let base_case_exists (thunks : base_case_thunk list) =
  match thunks with
  | [] -> False
  | first :: rest -> base_case_exists_rec (first ()) rest

(** Performs a boolean and across two normalized disjunctions, producing a new normalized disjunction *)
let and_disjunctions (dis1 : base_case_disjunction)
    (dis2 : base_case_disjunction) : base_case_disjunction =
  let dis_pairs = list_product (flatten_disjunction dis1) (flatten_disjunction dis2) in
  let new_dis_list =
    List.map (fun (first, second) -> TypeVarUnionSet.union first second) dis_pairs
  in
  (* This is safe because the product of two lists of length at least 1 should also have length at least 1 *)
  (List.hd new_dis_list, List.tl new_dis_list)

(** Helper to implement core logic of boolean and *)
let base_case_and_helper (exp : base_case_expr)
    (thunk : base_case_thunk) =
  match exp with
  (* If first expression is false, we avoid evaluating the second thunk *)
  | False -> False
  | True a -> (
      let exp2 = thunk () in
      match exp2 with
      | False -> False
      | True b -> True (and_disjunctions a b))

(** Performs boolean and over *)
let base_case_and (thunk1 : base_case_thunk) (thunk2 : base_case_thunk) =
  base_case_and_helper (thunk1 ()) thunk2

let rec base_case_for_all_rec (exp : base_case_expr) (thunks : base_case_thunk list)
    =
  match thunks with
  | [] -> exp
  | first :: rest ->
      base_case_for_all_rec (base_case_and_helper exp first) rest

(* TODO: consider accepting an arbitrary list and the map function instead of this *)
(** Equivalent to List.for_all, *)
let base_case_for_all (thunks : base_case_thunk list) =
  match thunks with
  | [] -> to_base_case_expr true
  | first :: rest -> base_case_for_all_rec (first ()) rest

(** Performs boolean and across multiple conjunctions *)
let rec and_conjunctions (conjunctions : base_case_conjunction list) =
  match conjunctions with
  | [] -> TypeVarUnionSet.empty
  | [ conj ] -> conj
  | first :: second :: rest ->
    and_conjunctions (TypeVarUnionSet.union first second :: rest)
