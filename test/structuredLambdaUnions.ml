open LambdaCalculus.Structured
open LambdaCalculus.StructuredBool
open LambdaCalculus.StructuredUnions

let test (name : string) (result : bool) =
  Printf.printf "%s: %s\n" (if result then "PASS" else "FAIL") name

let evaluates_to term value = eval term = value

let () =
  test "Exhaustive function coverage of union A"
    (is_subtype [ split_unary_bool ]
       [
         split_identity_type;
         split_not_type;
         split_unary_true_type;
         split_unary_false_type;
       ])

let () =
  test "Exhaustive function coverage of union B"
    (is_subtype
       [
         split_identity_type;
         split_not_type;
         split_unary_true_type;
         split_unary_false_type;
       ]
       [ split_unary_bool ])

let () =
  test "Incomplete function coverage of union A"
    (not
       (is_subtype [ split_unary_bool ]
          [ split_identity_type; split_not_type; split_unary_false_type ]))

let () =
  test "Incomplete function coverage of union B"
    (is_subtype
       [ split_identity_type; split_not_type; split_unary_false_type ]
       [ split_unary_bool ])

let () =
  test "Incomplete function coverage of union C"
    (not
       (is_subtype [ split_unary_bool ]
          [ split_identity_type; split_unary_false_type; split_unary_true_type ]))

let () =
  test "Incomplete function coverage of union D"
    (is_subtype
       [ split_identity_type; split_unary_false_type; split_unary_true_type ]
       [ split_unary_bool ])

let () =
  test "Non-unary function splitting A"
    (not (is_subtype [ unary_bool_op ] [ unary_true_type; unary_false_type ]))

let () =
  test "Non-unary function splitting B"
    (is_subtype [ unary_true_type; unary_false_type ] [ unary_bool_op ])

let () =
  test "Exhaustive function coverage with extras A"
    (is_subtype
       (split_unary_bool :: and_type)
       [
         split_identity_type;
         split_not_type;
         split_unary_true_type;
         split_unary_false_type;
         binary_bool_op;
       ])

let () =
  test "Exhaustive function coverage with extras B"
    (is_subtype
       (and_type
       @ [
           split_identity_type;
           split_not_type;
           split_unary_true_type;
           split_unary_false_type;
         ])
       [ split_unary_bool; binary_bool_op ])

let () =
  test "Increment three bit has expected type A"
    (is_subtype increment_three_bit_type [ increment_three_bit_type_expected ])

let () =
  test "Increment three bit has expected type B"
    (is_subtype [ increment_three_bit_type_expected ] increment_three_bit_type)

let () =
  test "Decrement three bit has expected type A"
    (is_subtype decrement_three_bit_type [ decrement_three_bit_type_expected ])

let () =
  test "Decrement three bit has expected type B"
    (is_subtype [ decrement_three_bit_type_expected ] decrement_three_bit_type)

let () =
  test "Increment three bit is a unary number operation"
    (is_subtype increment_three_bit_type [ unary_num_type ])

let () =
  test "Decrement three bit is a unary number operation"
    (is_subtype decrement_three_bit_type [ unary_num_type ])

let () =
  test "Add is a bunary number operation"
    (is_subtype add_three_bit_type [ binary_num_type ])

let () =
  test "one plus one"
    (evaluates_to
       (Application (Application (add_three_bit, one_term), one_term))
       two_term)

let () =
  test "two plus two"
    (evaluates_to
       (Application (Application (add_three_bit, two_term), two_term))
       four_term)

let () =
  test "three plus seven"
    (evaluates_to
       (Application (Application (add_three_bit, three_term), seven_term))
       two_term)
