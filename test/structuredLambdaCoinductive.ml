open LambdaCalculus.Structured
open LambdaCalculus.StructuredCoinductive
open LambdaCalculus.StructuredHelpers

let test (name : string) (result : bool) =
  Printf.printf "%s: %s\n" (if result then "PASS" else "FAIL") name

let is_equivalent_type (t1 : structured_type) (t2 : structured_type) =
  is_subtype t1 t2 && is_subtype t2 t1

let () =
  test "Even or odd integers equal to natural number"
    (is_equivalent_type integer
       (get_type_union [ even_integer; odd_integer ]))

(* These coinductive types have an inhabited intersection, the infinite function type *)
let () =
  test "Coinductive even and odd integers have an intersection"
    (has_intersection even_integer odd_integer)

let () =
  test "Pos/neg infinity is subtype of coinductive integers" (is_subtype infinity integer)

let () =
  test "Pos/neg infinity is subtype of coinductive even integers"
    (is_subtype infinity even_integer)

let () =
  test "Pos/neg infinity is subtype of coinductive odd integers"
    (is_subtype infinity odd_integer)

let () =
  test "Zero is a subtype of coinductive integers"
    (is_subtype zero.stype integer)

let () =
  test "Zero is a subtype of conindutive even integers" (is_subtype zero.stype even_integer)

let () =
  test "Zero is a not subtype of coninductive odd integers"
    (not (is_subtype zero.stype odd_integer))

let () =
  test "One is a subtype of coinductive integers"
    (is_subtype one.stype integer)

let () =
  test "One is not a subtype of coinductive even integers"
    (not (is_subtype one.stype even_integer))

let () =
  test "One is a subtype of coninductive odd integers" (is_subtype one.stype odd_integer)

let () =
  test "Negative two is a subtype of coinductive integers"
    (is_subtype neg_two.stype integer)

let () =
  test "Negative two is a subtype of coinductive even integers"
    (is_subtype neg_two.stype even_integer)

let () =
  test "Negative two is not a subtype of coninductive odd integers" (not (is_subtype neg_two.stype odd_integer))
