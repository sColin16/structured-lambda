open Common.Helpers
open Create
open Metatypes

module TypeVarPairSet = Set.Make (struct
  type t = int * int

  let compare = compare
end)

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

(* The approach here with universal quantification is to return true if there exists an instantiation of the
   type variable that could intersect. I believe this is correct because it's conservative, and so prevents possible
    argument intersections in functions, but it may require adjustments *)
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
  (* A universal type variable may intersect with the label, so we consider it does have an intersection
      With bounded quantification, we may need to adjust since bounding could eliminate label types *)
  | Label _, UnivTypeVar _ | UnivTypeVar _, Label _ -> true
  (* A universal type variable may intersect with an intersection type, so we consider it to have an intersection
     Like with labels, we may need to adjust when we add bounding*)
  | Intersection (_ :: _), UnivTypeVar _ | UnivTypeVar _, Intersection (_ :: _)
    ->
      true
  (* Universal type variables may intersect, although certain bounds (like labels) may change that *)
  | UnivTypeVar _, UnivTypeVar _ -> true
  (* Assuming impredicativity, universal types variables may be instantiated with a quantified type,
     and so the two types have an intersection. Bounding may change this... *)
  | UnivQuantification _, UnivTypeVar _ | UnivTypeVar _, UnivQuantification _ ->
      true
  (* Universal quantification doesn't intersect with labels since these are distinct terms *)
  | Label _, UnivQuantification _ | UnivQuantification _, Label _ -> false
  (* Universal quantification doesn't intersect with intersection types since they are distinct terms *)
  | Intersection (_ :: _), UnivQuantification _
  | UnivQuantification _, Intersection (_ :: _) ->
      false
  (* Univeral quantifications intersect if the contents of them do *)
  | UnivQuantification univ_union1, UnivQuantification univ_union2 ->
      has_intersection_rec
        (build_structured_type univ_union1 c1)
        (build_structured_type univ_union2 c2)
        encountered_type_vars
  (* Handle cases where one of the types is a type variable, expanding that type out and recursing *)
  (* We recursively check recursive types against universal quantification, since the
     recursive type definition could include universal quantification, and thus intersect *)
  (* We expand in the universal/recursive type var in case the recursive type expands to the bottom type
     but I believe in practice it should be equivalent to just always consider the two to have an intersection.
     It's probably the right approach for bounded quantification in the future *)
  | RecTypeVar n, Label _
  | RecTypeVar n, Intersection _
  | RecTypeVar n, UnivTypeVar _
  | RecTypeVar n, UnivQuantification _ ->
      has_intersection_rec (expand_type_var n c1)
        (build_structured_type [ t2 ] c2)
        encountered_type_vars
  | Label _, RecTypeVar n
  | Intersection _, RecTypeVar n
  | UnivTypeVar _, RecTypeVar n
  | UnivQuantification _, RecTypeVar n ->
      has_intersection_rec
        (build_structured_type [ t1 ] c1)
        (expand_type_var n c2) encountered_type_vars
  (* Finally, handle the potential loop case *)
  | RecTypeVar n, RecTypeVar m ->
      (* If we encounter a loop, intersection exists between two coinductive, but not
         if inductive types are involved at all, since they require a well-founded intersection *)
      if TypeVarPairSet.mem (n, m) encountered_type_vars then
        (List.nth c1 n).kind = Coinductive && (List.nth c2 m).kind = Coinductive
      else
        (* If we don't encounter a loop, we expand both sides and recurse, tracking this pair to detect a future loop *)
        has_intersection_rec (expand_type_var n c1) (expand_type_var m c2)
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
