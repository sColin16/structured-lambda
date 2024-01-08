open LambdaCalculus.StructuredPoly
open LambdaCalculus.Structured.TermOperations.Eval
open LambdaCalculus.Structured.TermOperations.ValToTerm
open LambdaCalculus.Structured.TypeOperations.Subtype
open LambdaCalculus.Structured.Metatypes
open LambdaCalculus.StructuredHelpers
open LambdaCalculus.StructuredArithmetic

let test (name : string) (result : bool) =
  Printf.printf "%s: %s\n" (if result then "PASS" else "FAIL") name

let evaluates_to term value = value_to_term (eval term) = value

let is_equivalent_type (t1 : structured_type) (t2 : structured_type) =
  is_subtype t1 t2 && is_subtype t2 t1

let applied_poly_identity =
  get_typed_term_unsafe
    (UnivApplication (polymoprhic_identity.term, name_label.stype))

let applied_poly_double =
  get_typed_term_unsafe
    (UnivApplication (polymorphic_double.term, three_bit_type))

let applied_poly_quadruple =
  get_typed_term_unsafe
    (UnivApplication (polymorphic_quadruple.term, three_bit_type))

let expected_poly_identity_type =
  base_to_structured_type
    (UnivQuantification
       [ Intersection [ ([ UnivTypeVar 0 ], [ UnivTypeVar 0 ]) ] ])

let expected_applied_poly_type =
  base_to_structured_type
    (Intersection [ (name_label.stype.union, name_label.stype.union) ])

let expected_poly_map_type =
  base_to_structured_type
    (UnivQuantification
       [
         Intersection
           [
             ( [ Intersection [ ([ UnivTypeVar 0 ], [ UnivTypeVar 0 ]) ] ],
               [ Intersection [ ([ UnivTypeVar 0 ], [ UnivTypeVar 0 ]) ] ] );
           ];
       ])

let expected_poly_map_applied_type =
  base_to_structured_type
    (Intersection
       [
         ( [ Intersection [ (three_bit_type.union, three_bit_type.union) ] ],
           [ Intersection [ (three_bit_type.union, three_bit_type.union) ] ] );
       ])

let () =
  test "Polymoprhic identity function type"
    (is_equivalent_type polymoprhic_identity.stype expected_poly_identity_type)

let () =
  test "Polymoprhic identity function applied type"
    (is_equivalent_type applied_poly_identity.stype expected_applied_poly_type)

let () =
  test "Polymoprhic double function type"
    (is_equivalent_type polymorphic_double.stype expected_poly_map_type)

let () =
  test "Polymoprhic double function applied type"
    (is_equivalent_type applied_poly_double.stype
       expected_poly_map_applied_type)

let () =
  test "Polymorphic quadruple function type"
    (is_equivalent_type polymorphic_quadruple.stype expected_poly_map_type)

let () =
  test "Polymoprhic quadruple function applied type"
    (is_equivalent_type applied_poly_quadruple.stype
       expected_poly_map_applied_type)

let () =
  test "Simple polymoprhic evaluation"
    (evaluates_to
       (Application (applied_poly_identity.term, name_label.term))
       name_label.term)

let () =
  test "Double polymorphic eval with increment"
    (evaluates_to
       (Application
          (Application (applied_poly_double.term, increment.term), two.term))
       four.term)

let () =
  test "Double polymorphic eval with decrement"
    (evaluates_to
       (Application
          (Application (applied_poly_double.term, decrement.term), zero.term))
       six.term)

let () =
  test "Quadruple polymorphic with increment"
    (evaluates_to
       (Application
          (Application (applied_poly_quadruple.term, increment.term), six.term))
       two.term)

let () =
  test "Quadruple polymorphic with decrement"
    (evaluates_to
       (Application
          (Application (applied_poly_quadruple.term, decrement.term), five.term))
       one.term)
