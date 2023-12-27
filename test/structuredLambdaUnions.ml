open LambdaCalculus.Structured.TermOperations.Eval
open LambdaCalculus.Structured.TypeOperations.Subtype
open LambdaCalculus.Structured.TypeOperations.Intersection
open LambdaCalculus.StructuredBool
open LambdaCalculus.StructuredUnions
open LambdaCalculus.StructuredHelpers
open LambdaCalculus.Structured.TermOperations.ValToTerm

let test (name : string) (result : bool) =
  Printf.printf "%s: %s\n" (if result then "PASS" else "FAIL") name

let evaluates_to term value = value_to_term (eval term) = value

let () =
  test "Exhaustive function coverage of union A"
    (is_subtype split_unary_bool
       (get_type_union
          [
            split_identity_type;
            split_not_type;
            split_unary_true_type;
            split_unary_false_type;
          ]))

let () =
  test "Exhaustive function coverage of union B"
    (is_subtype
       (get_type_union
          [
            split_identity_type;
            split_not_type;
            split_unary_true_type;
            split_unary_false_type;
          ])
       split_unary_bool)

let () =
  test "Incomplete function coverage of union A"
    (not
       (is_subtype split_unary_bool
          (get_type_union
             [ split_identity_type; split_not_type; split_unary_false_type ])))

let () =
  test "Incomplete function coverage of union B"
    (is_subtype
       (get_type_union
          [ split_identity_type; split_not_type; split_unary_false_type ])
       split_unary_bool)

let () =
  test "Incomplete function coverage of union C"
    (not
       (is_subtype split_unary_bool
          (get_type_union
             [
               split_identity_type;
               split_unary_false_type;
               split_unary_true_type;
             ])))

let () =
  test "Incomplete function coverage of union D"
    (is_subtype
       (get_type_union
          [ split_identity_type; split_unary_false_type; split_unary_true_type ])
       split_unary_bool)

let () =
  test "Non-unary function splitting A"
    (not
       (is_subtype unary_bool_op
          (get_type_union [ unary_true_type; unary_false_type ])))

let () =
  test "Non-unary function splitting B"
    (is_subtype
       (get_type_union [ unary_true_type; unary_false_type ])
       unary_bool_op)

let () =
  test "Exhaustive function coverage with extras A"
    (is_subtype
       (get_type_union [ split_unary_bool; and_lambda.stype ])
       (get_type_union
          [
            split_identity_type;
            split_not_type;
            split_unary_true_type;
            split_unary_false_type;
            binary_bool_op;
          ]))

let () =
  test "Exhaustive function coverage with extras B"
    (is_subtype
       (get_type_union
          [
            and_lambda.stype;
            split_identity_type;
            split_not_type;
            split_unary_true_type;
            split_unary_false_type;
          ])
       (get_type_union [ split_unary_bool; binary_bool_op ]))

let () =
  test "Increment three bit has expected type A"
    (is_subtype increment_three_bit.stype increment_three_bit_type_expected)

let () =
  test "Increment three bit has expected type B"
    (is_subtype increment_three_bit_type_expected increment_three_bit.stype)

let () =
  test "Decrement three bit has expected type A"
    (is_subtype decrement_three_bit.stype decrement_three_bit_type_expected)

let () =
  test "Decrement three bit has expected type B"
    (is_subtype decrement_three_bit_type_expected decrement_three_bit.stype)

let () =
  test "Increment three bit is a unary number operation"
    (is_subtype increment_three_bit.stype unary_num_type)

let () =
  test "Decrement three bit is a unary number operation"
    (is_subtype decrement_three_bit.stype unary_num_type)

let () =
  test "Add is a bunary number operation"
    (is_subtype add_three_bit.stype binary_num_type)

let () =
  test "one plus one"
    (evaluates_to
       (Application (Application (add_three_bit.term, one.term), one.term))
       two.term)

let () =
  test "two plus two"
    (evaluates_to
       (Application (Application (add_three_bit.term, two.term), two.term))
       four.term)

let () =
  test "three plus seven"
    (evaluates_to
       (Application (Application (add_three_bit.term, three.term), seven.term))
       two.term)

let () = test "zero and zero" (has_intersection zero.stype zero.stype)
let () = test "zero and one" (not (has_intersection zero.stype one.stype))
let () = test "one and two" (not (has_intersection one.stype two.stype))
let () = test "zero and two" (not (has_intersection zero.stype two.stype))
let () = test "different functions A" (not (is_subtype one.stype two.stype))
let () = test "different functions B" (not (is_subtype two.stype one.stype))
