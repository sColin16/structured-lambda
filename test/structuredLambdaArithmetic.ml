open LambdaCalculus.Structured
open LambdaCalculus.StructuredArithmetic

let test (name : string) (result : bool) =
  Printf.printf "%s: %s\n" (if result then "PASS" else "FAIL") name

let get_type_unsafe term = Option.get (get_type term)
let evaluates_to term value = eval term = value
let fib_type = get_type_unsafe fib

let () =
  test "increment is a unary num operator"
    (is_subtype increment_type [ unary_num_op ])

let () =
  test "decrement is a unary num operator"
    (is_subtype decrement_type [ unary_num_op ])

let () =
  test "add is a binary num operator" (is_subtype add_type [ binary_num_op ])

let () =
  test "fib is a unary num operator" (is_subtype fib_type [ unary_num_op ])

let () =
  test "increment zero"
    (evaluates_to (Application (increment, zero_term)) one_term)

let () =
  test "increment seven"
    (evaluates_to (Application (increment, seven_term)) zero_term)

let () =
  test "decrement two"
    (evaluates_to (Application (decrement, two_term)) one_term)

let () =
  test "decrement zero"
    (evaluates_to (Application (decrement, zero_term)) seven_term)

let () =
  test "one plus one"
    (evaluates_to
       (Application (Application (add, one_term), one_term))
       two_term)

let () =
  test "two plus two"
    (evaluates_to
       (Application (Application (add, two_term), two_term))
       four_term)

let () =
  test "three plus seven"
    (evaluates_to
       (Application (Application (add, three_term), seven_term))
       two_term)

let () =
  test "fib 0"
    (evaluates_to (Application(fib, zero_term)) one_term)

let () =
  test "fib 1"
    (evaluates_to (Application(fib, one_term)) one_term)

let () =
  test "fib 2"
    (evaluates_to (Application(fib, two_term)) two_term)

let () =
  test "fib 3"
    (evaluates_to (Application(fib, three_term)) three_term)

let () =
  test "fib 4"
    (evaluates_to (Application(fib, four_term)) five_term)

let () =
  test "fib 5"
    (evaluates_to (Application(fib, five_term)) zero_term)

let () =
  test "fib 6"
    (evaluates_to (Application(fib, six_term)) five_term)

let () =
  test "fib 7"
    (evaluates_to (Application(fib, seven_term)) five_term)
