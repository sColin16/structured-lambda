open LambdaCalculus.Structured
open LambdaCalculus.StructuredArithmetic
open LambdaCalculus.StructuredBool
open LambdaCalculus.StructuredMixed

let test (name : string) (result : bool) =
  Printf.printf "%s: %s\n" (if result then "PASS" else "FAIL") name

let evaluates_to term value = eval term = value

let is_even_odd_type_expected =
  Function [ ([ is_even_label_type; is_odd_label_type ], [ num_to_bool ]) ]

let () =
  test "is_zero is num to bool type" (is_subtype is_zero_type [ num_to_bool ])

let () =
  test "is_even_odd has expected mutually recursive type"
    (is_subtype is_even_odd_type [ is_even_odd_type_expected ])

let () =
  test "is_even is num to bool type" (is_subtype is_even_type [num_to_bool])

let () =
  test "is_odd is num to bool type" (is_subtype is_odd_type [num_to_bool])

let () =
  test "zero is zero"
    (evaluates_to (Application (is_zero, zero_term)) true_term)

let () =
  test "two is not zero"
    (evaluates_to (Application (is_zero, two_term)) false_term)

let () =
  test "zero is even" (evaluates_to (Application(is_even, zero_term)) true_term)

let () =
  test "one is odd" (evaluates_to (Application(is_odd, one_term)) true_term)

let () =
  test "six is even" (evaluates_to (Application(is_even, six_term)) true_term)

let () =
  test "seven is odd" (evaluates_to (Application(is_odd, seven_term)) true_term)

let () =
  test "zero is not odd" (evaluates_to (Application(is_odd, zero_term)) false_term)

let () =
  test "one is not even" (evaluates_to (Application(is_even, one_term)) false_term)

let () =
  test "six is not odd" (evaluates_to (Application(is_odd, six_term)) false_term)

let () =
  test "seven is not even" (evaluates_to (Application(is_even, seven_term)) false_term)
