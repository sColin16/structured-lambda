open LambdaCalculus.Structured
open LambdaCalculus.StructuredMixed

let test (name : string) (result : bool) =
  Printf.printf "%s: %s\n" (if result then "PASS" else "FAIL") name

let get_type_unsafe term = Option.get (get_type term)

let is_even_odd_type = Function [ ([ is_even_type; is_odd_type ], [ num_to_bool ]) ]

let () = test "is_zero is num to bool type" (is_subtype is_zero_type [num_to_bool])