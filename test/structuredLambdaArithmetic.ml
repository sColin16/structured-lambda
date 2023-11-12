open LambdaCalculus.Structured
open LambdaCalculus.StructuredArithmetic

let test (name : string) (result : bool) =
  Printf.printf "%s: %s\n" (if result then "PASS" else "FAIL") name

let evaluates_to term value = eval term = value

let () =
  test "increment is a unary num operator"
    (is_subtype increment.stype unary_num_op)

let () =
  test "decrement is a unary num operator"
    (is_subtype decrement.stype unary_num_op)

let () =
  test "add is a binary num operator" (is_subtype add.stype binary_num_op)

let () = test "fib is a unary num operator" (is_subtype fib.stype unary_num_op)

let () =
  test "increment zero"
    (evaluates_to (Application (increment.term, zero.term)) one.term)

let () =
  test "increment seven"
    (evaluates_to (Application (increment.term, seven.term)) zero.term)

let () =
  test "decrement two"
    (evaluates_to (Application (decrement.term, two.term)) one.term)

let () =
  test "decrement zero"
    (evaluates_to (Application (decrement.term, zero.term)) seven.term)

let () =
  test "one plus one"
    (evaluates_to
       (Application (Application (add.term, one.term), one.term))
       two.term)

let () =
  test "two plus two"
    (evaluates_to
       (Application (Application (add.term, two.term), two.term))
       four.term)

let () =
  test "three plus seven"
    (evaluates_to
       (Application (Application (add.term, three.term), seven.term))
       two.term)

let () =
  test "fib 0" (evaluates_to (Application (fib.term, zero.term)) one.term)

let () = test "fib 1" (evaluates_to (Application (fib.term, one.term)) one.term)
let () = test "fib 2" (evaluates_to (Application (fib.term, two.term)) two.term)

let () =
  test "fib 3" (evaluates_to (Application (fib.term, three.term)) three.term)

let () =
  test "fib 4" (evaluates_to (Application (fib.term, four.term)) five.term)

let () =
  test "fib 5" (evaluates_to (Application (fib.term, five.term)) zero.term)

let () =
  test "fib 6" (evaluates_to (Application (fib.term, six.term)) five.term)

let () =
  test "fib 7" (evaluates_to (Application (fib.term, seven.term)) five.term)
