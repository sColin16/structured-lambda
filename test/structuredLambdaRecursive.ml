open LambdaCalculus.Structured.Metatypes
open LambdaCalculus.Structured.TypeOperations.Subtype
open LambdaCalculus.Structured.TypeOperations.Intersection
open LambdaCalculus.Structured.TypeOperations.Unary
open LambdaCalculus.Structured.TypeOperations.WellFounded
open LambdaCalculus.StructuredRecursive
open LambdaCalculus.StructuredHelpers

let test (name : string) (result : bool) =
  Printf.printf "%s: %s\n" (if result then "PASS" else "FAIL") name

let is_equivalent_type (t1 : structured_type) (t2 : structured_type) =
  is_subtype t1 t2 && is_subtype t2 t1

let is_strict_subtype (t1: structured_type) (t2: structured_type) =
  is_subtype t1 t2 && not (is_subtype t2 t1)

let () =
  test "Coninductive even or odd integers equal to coinductive integer"
    (is_equivalent_type coi_integer
       (get_type_union [ coi_even_integer; coi_odd_integer ]))

let () =
  test "Inductive even or odd integers equal to inductive integer"
    (is_equivalent_type ind_integer
       (get_type_union [ ind_even_integer; ind_odd_integer ]))

let () =
  test "Inductive integer or pos/neg infinity equal to coinductive integer"
    (is_equivalent_type coi_integer
       (get_type_union [ ind_integer; infinity ]))

let () =
  test "Inductive integers with positive infinity strict subtype of coinductive integers"
    (is_strict_subtype ind_integer_plus coi_integer)

let () =
  test "Inductive integers with negative infinity strict subtype of coinductive integers"
    (is_strict_subtype ind_integer_minus coi_integer)

(* These coinductive types have an inhabited intersection, the infinite function type *)
let () =
  test "Coinductive even and odd integers have an intersection"
    (has_intersection coi_even_integer coi_odd_integer)

(* But the inductive versions intentionally do not have an intersection *)
let () =
  test "Inductive even and odd integers don't have an intersection"
    (not (has_intersection ind_even_integer ind_odd_integer))

let () =
  test "Pos/neg infinity is subtype of coinductive integers"
    (is_subtype infinity coi_integer)

let () =
  test "Pos/neg infinity is subtype of coinductive even integers"
    (is_subtype infinity coi_even_integer)

let () =
  test "Pos/neg infinity is subtype of coinductive odd integers"
    (is_subtype infinity coi_odd_integer)

let () =
  test "Pos/neg infinity is not a subtype of inductive integers"
    (not (is_subtype infinity ind_integer))

let () =
  test "Pos/neg infinity is not a subtype of inductive even integers"
    (not (is_subtype infinity ind_even_integer))

let () =
  test "Pos/neg infinity is not a subtype of inductive odd integers"
    (not (is_subtype infinity ind_odd_integer))

let () =
  test
    "Pos infinity is a subtype of inductive integers with inductive positives"
    (is_subtype pos_infinity ind_integer_plus)

let () =
  test
    "Neg infinity is not a subtype of inductive integers with inductive \
     positives"
    (not (is_subtype neg_infinity ind_integer_plus))

let () =
  test
    "Pos infinity is not a subtype of inductive integers with inductive \
     negatives"
    (not (is_subtype pos_infinity ind_integer_minus))

let () =
  test
    "Neg infinity is a subtype of inductive integers with inductive negatives"
    (is_subtype neg_infinity ind_integer_minus)

let () =
  test "Zero is a subtype of coinductive integers"
    (is_subtype zero.stype coi_integer)

let () =
  test "Zero is a subtype of conindutive even integers"
    (is_subtype zero.stype coi_even_integer)

let () =
  test "Zero is a not subtype of coninductive odd integers"
    (not (is_subtype zero.stype coi_odd_integer))

let () =
  test "One is a subtype of coinductive integers"
    (is_subtype one.stype coi_integer)

let () =
  test "One is not a subtype of coinductive even integers"
    (not (is_subtype one.stype coi_even_integer))

let () =
  test "One is a subtype of coninductive odd integers"
    (is_subtype one.stype coi_odd_integer)

let () =
  test "Negative two is a subtype of coinductive integers"
    (is_subtype neg_two.stype coi_integer)

let () =
  test "Negative two is a subtype of coinductive even integers"
    (is_subtype neg_two.stype coi_even_integer)

let () =
  test "Negative two is not a subtype of coninductive odd integers"
    (not (is_subtype neg_two.stype coi_odd_integer))

let () =
  test "inductive integers are a strict subtype of coninductive integers"
    (is_strict_subtype ind_integer coi_integer)

let () =
  test "coinductive and inductive integers have an intersction"
    (has_intersection ind_integer coi_integer)

let () =
  test "inductive integers do not intersect with infinity"
    (not (has_intersection ind_integer infinity))

let () = test "positive infinity is a unary type" (is_unary pos_infinity)
let () = test "negative infinity is a unary type" (is_unary pos_infinity)

let () =
  test "inductive integers are well-founded"
    (is_well_founded_union ind_integer.union ind_integer.context)

let () =
  test "Pos/neg infinity is not well-founded"
    (not (is_well_founded_union infinity.union infinity.context))
