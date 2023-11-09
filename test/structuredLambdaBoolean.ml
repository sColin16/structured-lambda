open LambdaCalculus.Structured
open LambdaCalculus.StructuredBool

let test (name : string) (result : bool) =
  Printf.printf "%s: %s\n" (if result then "PASS" else "FAIL") name

let evaluates_to term value = eval term = value

let () =
  test "identity is unary bool op" (is_subtype identity_type [ unary_bool_op ])

let () = test "not is unary bool op" (is_subtype not_type [ unary_bool_op ])
let () = test "and is binary bool op" (is_subtype and_type [ binary_bool_op ])
let () = test "or is binary bool op" (is_subtype or_type [ binary_bool_op ])
let () = test "if is ternary bool op" (is_subtype if_type [ ternary_bool_op ])

let () =
  test "not true" (evaluates_to (Application (not_term, true_term)) false_term)

let () =
  test "not false" (evaluates_to (Application (not_term, false_term)) true_term)

let () = test "true and true" (evaluates_to (Application(Application(and_term, true_term), true_term)) true_term)
let () = test "true and false" (evaluates_to (Application(Application(and_term, true_term), false_term)) false_term)
let () = test "false and true" (evaluates_to (Application(Application(and_term, false_term), true_term)) false_term)
let () = test "false and false" (evaluates_to (Application(Application(and_term, false_term), false_term)) false_term)
let () = test "true or true" (evaluates_to (Application(Application(or_term, true_term), true_term)) true_term)
let () = test "true or false" (evaluates_to (Application(Application(or_term, true_term), false_term)) true_term)
let () = test "false or true" (evaluates_to (Application(Application(or_term, false_term), true_term)) true_term)
let () = test "false or false" (evaluates_to (Application(Application(or_term, false_term), false_term)) false_term)
