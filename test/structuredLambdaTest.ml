open LambdaCalculus.Structured.Metatypes
open LambdaCalculus.Structured.TermOperations.Typing
open LambdaCalculus.Structured.TypeOperations.Subtype
open LambdaCalculus.Structured.TypeOperations.Intersection
open LambdaCalculus.StructuredHelpers
open TypeOperations.Union

let test (name : string) (result : bool) =
  Printf.printf "%s: %s\n" (if result then "PASS" else "FAIL") name

let b =
  union_to_structured_type
    [ Label "A"; Intersection [ ([ Label "A" ], [ Label "B" ]) ] ]

let c =
  union_to_structured_type
    [ Intersection [ ([ Label "A" ], [ Label "B" ]) ]; Label "A" ]

let a_label = label_to_structured_type "A"
let b_label = label_to_structured_type "B"
let c_label = label_to_structured_type "C"
let d_label = label_to_structured_type "D"
let e_label = label_to_structured_type "E"
let name_label = label_to_structured_type "Name"
let val_label = label_to_structured_type "Val"
let zero_label = label_to_structured_type "Zero"
let succ_label = label_to_structured_type "Succ"
let zero_type = func_to_structured_type (name_label.union, zero_label.union)

let increment_type (num : structured_type) =
  base_to_structured_type
    (Intersection
       [ (name_label.union, succ_label.union); (val_label.union, num.union) ])

let one_type = increment_type zero_type
let two_type = increment_type one_type
let three_type = increment_type two_type
let four_type = increment_type three_type
let five_type = increment_type four_type
let six_type = increment_type five_type
let seven_type = increment_type six_type

(* A -> (B -> C | D) *)
let nested_a =
  func_to_structured_type
    ( a_label.union,
      [
        Intersection
          [ (b_label.union, (get_type_union [ c_label; d_label ]).union) ];
      ] )

(* A -> (B -> D | E) *)
let nested_b =
  func_to_structured_type
    ( a_label.union,
      [
        Intersection
          [ (b_label.union, (get_type_union [ d_label; e_label ]).union) ];
      ] )

let a_to_b = func_to_structured_type (a_label.union, b_label.union)
let a_to_c = func_to_structured_type (a_label.union, c_label.union)
let b_to_c = func_to_structured_type (b_label.union, c_label.union)

let ab_to_c =
  func_to_structured_type
    ((get_type_union [ a_label; b_label ]).union, c_label.union)

let a_to_bc =
  func_to_structured_type
    (a_label.union, (get_type_union [ b_label; c_label ]).union)

let a_to_cd =
  func_to_structured_type
    (a_label.union, (get_type_union [ c_label; d_label ]).union)

let joinable_a = a_to_b
let joinable_b = b_to_c
let unit_type = base_to_structured_type (Intersection [])
let empty_type = union_to_structured_type []

let large_arg_split_subtype =
  union_to_structured_type
    [
      Intersection
        [
          ( (get_type_union [ a_label; b_label; c_label ]).union,
            (get_type_union [ c_label; d_label ]).union );
          ((get_type_union [ a_label; b_label ]).union, c_label.union);
        ];
    ]

let large_arg_split_supertype =
  func_to_structured_type
    ( (get_type_union [ a_label; b_label ]).union,
      (get_type_union [ c_label; d_label; e_label ]).union )

let () = test "simple empty" (not (has_intersection a_label b_label))
let () = test "simple identical" (has_intersection a_label a_label)
let () = test "out of order identical" (has_intersection b c)

let () =
  test "single label inhabited"
    (has_intersection
       (get_type_union [ a_label; b_label ])
       (get_type_union [ b_label; c_label ]))

let () = test "nested test" (has_intersection nested_a nested_b)
let () = test "joinable" (has_intersection joinable_a joinable_b)
let () = test "label reflexivity" (is_subtype a_label a_label)
let () = test "function reflexivity" (is_subtype one_type one_type)

let () =
  test "label union subtyping A"
    (is_subtype a_label
       (get_type_union [ a_label; b_label; one_type; zero_type ]))

let () =
  test "label union subtyping B"
    (not
       (is_subtype
          (get_type_union [ a_label; b_label; one_type; zero_type ])
          a_label))

let () =
  test "function union subtyping A"
    (is_subtype two_type (get_type_union [ two_type; one_type; a_label ]))

let () =
  test "function union subtyping B"
    (not (is_subtype (get_type_union [ two_type; one_type; a_label ]) two_type))

let () = test "different labels A" (not (is_subtype a_label b_label))
let () = test "different labels B" (not (is_subtype b_label a_label))

let () =
  test "disjoint labels"
    (not
       (is_subtype
          (get_type_union [ a_label; b_label ])
          (get_type_union [ c_label; d_label ])))

let () =
  test "intersecting labels A"
    (not
       (is_subtype
          (get_type_union [ a_label; b_label ])
          (get_type_union [ b_label; c_label ])))

let () =
  test "intersecting labels B"
    (not
       (is_subtype
          (get_type_union [ b_label; c_label ])
          (get_type_union [ a_label; b_label ])))

let () = test "top type of label A" (is_subtype a_label unit_type)
let () = test "top type of label B" (not (is_subtype unit_type a_label))
let () = test "top type of function A" (is_subtype two_type unit_type)
let () = test "top type of function B" (not (is_subtype unit_type two_type))
let () = test "bottom type of label A" (is_subtype empty_type a_label)
let () = test "bottom type of label B" (not (is_subtype a_label empty_type))

let () =
  test "extended function arg A"
    (is_subtype (get_type_intersection [ a_to_b; b_to_c ]) a_to_b)

let () =
  test "extended function arg B"
    (not (is_subtype a_to_b (get_type_intersection [ a_to_b; b_to_c ])))

let () = test "basic function subtyping A" (is_subtype ab_to_c a_to_bc)
let () = test "basic function subtyping B" (not (is_subtype a_to_bc ab_to_c))

let () =
  test "function arg split A"
    (is_subtype (get_type_intersection [ a_to_c; b_to_c ]) ab_to_c)

let () =
  test "function arg split B"
    (is_subtype ab_to_c (get_type_intersection [ a_to_c; b_to_c ]))

let () =
  test "large arg split A"
    (is_subtype large_arg_split_subtype large_arg_split_supertype)

let () =
  test "large arg split B"
    (not (is_subtype large_arg_split_supertype large_arg_split_subtype))

(* This potential property is not considered valid, we assume argument types don't have inhabited intersection *)
let () =
  test "invalid function return split A"
    (not (is_subtype (get_type_intersection [ a_to_bc; a_to_cd ]) a_to_c))

(* But the invrse is true within the system *)
let () =
  test "function return split B"
    (is_subtype a_to_c (get_type_intersection [ a_to_bc; a_to_cd ]))

(* We have not applied this property, and don't want to. We'd need to have unary argument types to split inthis way *)
let () =
  test "invalid function return split A"
    (not
       (is_subtype
          (func_to_structured_type
             ( (get_type_union [ a_label; b_label ]).union,
               (get_type_union [ a_label; b_label ]).union ))
          (union_to_structured_type
             [
               Intersection
                 [
                   ((get_type_union [ a_label; b_label ]).union, a_label.union);
                   ((get_type_union [ a_label; b_label ]).union, b_label.union);
                 ];
             ])))

(* But again, the reverse is true, and this is expected *)
let () =
  test "invalid function return split B"
    (is_subtype
       (base_to_structured_type
          (Intersection
             [
               ((get_type_union [ a_label; b_label ]).union, a_label.union);
               ((get_type_union [ a_label; b_label ]).union, b_label.union);
             ]))
       (func_to_structured_type
          ( (get_type_union [ a_label; b_label ]).union,
            (get_type_union [ a_label; b_label ]).union )))

(* This subtyping relation has also not been applied *)
(* TODO: Well but it kinda has been... I should revisit this, I think this requires automatic unary form coercion *)
let () =
  test "invalid fuction arg split A"
    (not
       (is_subtype
          (func_to_structured_type
             ((get_type_intersection [ a_to_b; b_to_c ]).union, a_label.union))
          (get_type_union
             [
               func_to_structured_type (a_to_b.union, a_label.union);
               func_to_structured_type (b_to_c.union, a_label.union);
             ])))

(* But the inverse should be true *)
let () =
  test "invalid fuction arg split B"
    (is_subtype
       (get_type_union
          [
            func_to_structured_type (a_to_b.union, a_label.union);
            func_to_structured_type (b_to_c.union, a_label.union);
          ])
       (func_to_structured_type
          ((get_type_intersection [ a_to_b; b_to_c ]).union, a_label.union)))

let () =
  test "basic application types"
    (get_application_type
       (func_to_structured_type (a_label.union, b_label.union))
       a_label
    = Some b_label)

let () =
  test "application against label fails"
    (get_application_type a_label a_label = None)

let () =
  test "basic mismatched application"
    (get_application_type
       (func_to_structured_type (b_label.union, b_label.union))
       a_label
    = None)

let () =
  test "contravariant function application A"
    (get_application_type
       (func_to_structured_type
          ((get_type_union [ a_label; b_label ]).union, c_label.union))
       a_label
    = Some c_label)

let () =
  test "contravariant function application B"
    (get_application_type
       (base_to_structured_type
          (Intersection
             [ (a_label.union, c_label.union); (b_label.union, d_label.union) ]))
       a_label
    = Some c_label)

let () =
  test "union function application A"
    (get_application_type
       (base_to_structured_type
          (Intersection
             [ ((get_type_union [ a_label; b_label ]).union, c_label.union) ]))
       (get_type_union [ a_label; b_label ])
    = Some c_label)

let () =
  test "union function application B"
    (get_application_type
       (base_to_structured_type
          (Intersection
             [ (a_label.union, c_label.union); (b_label.union, d_label.union) ]))
       (get_type_union [ a_label; b_label ])
    = Some (get_type_union [ c_label; d_label ]))

let () =
  test "application fails when label in union"
    (get_application_type
       (get_type_union
          [ a_label; func_to_structured_type (a_label.union, b_label.union) ])
       a_label
    = None)

let () =
  test "application fails when not all functios can be applied"
    (get_application_type
       (union_to_structured_type
          [
            Intersection [ (b_label.union, a_label.union) ];
            Intersection [ (a_label.union, b_label.union) ];
          ])
       a_label
    = None)

let () =
  test "union against union application fails"
    (get_application_type
       (union_to_structured_type
          [
            Intersection [ (b_label.union, a_label.union) ];
            Intersection [ (a_label.union, b_label.union) ];
          ])
       (get_type_union [ a_label; b_label ])
    = None)

let () =
  test "union of functions unions return types"
    (get_application_type
       (union_to_structured_type
          [
            Intersection [ (a_label.union, c_label.union) ];
            Intersection [ (a_label.union, d_label.union) ];
          ])
       a_label
    = Some (get_type_union [ c_label; d_label ]))

let () =
  test "function arguments may not overlap"
    (get_type
       (Abstraction
          [
            (a_label, Variable 0);
            (get_type_union [ a_label; b_label ], Variable 0);
          ])
    = None)
