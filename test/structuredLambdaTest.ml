open LambdaCalculus.Structured

let test (name : string) (result : bool) =
  Printf.printf "%s: %s\n" (if result then "PASS" else "FAIL") name

let b = [ Label "A"; Function [ ([ Label "A" ], [ Label "B" ]) ] ]
let c = [ Function [ ([ Label "A" ], [ Label "B" ]) ]; Label "A" ]
let a_label = Label "A"
let b_label = Label "B"
let c_label = Label "C"
let d_label = Label "D"
let e_label = Label "E"
let name_label = Label "Name"
let val_label = Label "Val"
let zero_label = Label "Zero"
let succ_label = Label "Succ"
let zero_type = Function [ ([ name_label ], [ zero_label ]) ]

let increment_type (num : base_type) =
  Function [ ([ name_label ], [ succ_label ]); ([ val_label ], [ num ]) ]

let one_type = increment_type zero_type
let two_type = increment_type one_type
let three_type = increment_type two_type
let four_type = increment_type three_type
let five_type = increment_type four_type
let six_type = increment_type five_type
let seven_type = increment_type six_type

let three_bit_num =
  [
    zero_type;
    one_type;
    two_type;
    three_type;
    four_type;
    five_type;
    six_type;
    seven_type;
  ]

(* A -> (B -> C | D) *)
let nested_a =
  Function
    [ ([ a_label ], [ Function [ ([ b_label ], [ c_label; d_label ]) ] ]) ]

(* A -> (B -> D | E) *)
let nested_b =
  Function
    [ ([ a_label ], [ Function [ ([ b_label ], [ d_label; e_label ]) ] ]) ]

let a_to_b = ([ a_label ], [ b_label ])
let a_to_c = ([ a_label ], [ c_label ])
let b_to_c = ([ b_label ], [ c_label ])
let ab_to_c = ([ a_label; b_label ], [ c_label ])
let a_to_bc = ([ a_label ], [ b_label; c_label ])
let a_to_cd = ([ a_label ], [ c_label; d_label ])
let joinable_a = Function [ a_to_b ]
let joinable_b = Function [ b_to_c ]
let unit_type = Function []

let large_arg_split_subtype =
  [
    Function
      [
        ([ a_label; b_label; c_label ], [ c_label; d_label ]);
        ([ a_label; b_label ], [ c_label ]);
      ];
  ]

let large_arg_split_supertype =
  [ Function [ ([ a_label; b_label ], [ c_label; d_label; e_label ]) ] ]

let () = test "simple empty" (not (has_intersection [ a_label ] [ b_label ]))
let () = test "simple identical" (has_intersection [ a_label ] [ a_label ])
let () = test "out of order identical" (has_intersection b c)

let () =
  test "single label inhabited"
    (has_intersection [ a_label; b_label ] [ b_label; c_label ])

let () = test "zero and zero" (has_intersection [ zero_type ] [ zero_type ])
let () = test "zero and one" (not (has_intersection [ zero_type ] [ one_type ]))
let () = test "one and two" (not (has_intersection [ one_type ] [ two_type ]))
let () = test "zero and two" (not (has_intersection [ zero_type ] [ two_type ]))
let () = test "nested test" (has_intersection [ nested_a ] [ nested_b ])
let () = test "joinable" (has_intersection [ joinable_a ] [ joinable_b ])
let () = test "label reflexivity" (is_subtype [ a_label ] [ a_label ])
let () = test "function reflexivity" (is_subtype [ one_type ] [ one_type ])

let () =
  test "label union subtyping A"
    (is_subtype [ a_label ] [ a_label; b_label; one_type; zero_type ])

let () =
  test "label union subtyping B"
    (not (is_subtype [ a_label; b_label; one_type; zero_type ] [ a_label ]))

let () =
  test "function union subtyping A"
    (is_subtype [ two_type ] [ two_type; one_type; a_label ])

let () =
  test "function union subtyping B"
    (not (is_subtype [ two_type; one_type; a_label ] [ two_type ]))

let () = test "different labels A" (not (is_subtype [ a_label ] [ b_label ]))
let () = test "different labels B" (not (is_subtype [ b_label ] [ a_label ]))

let () =
  test "disjoint labels"
    (not (is_subtype [ a_label; b_label ] [ c_label; d_label ]))

let () =
  test "intersecting labels A"
    (not (is_subtype [ a_label; b_label ] [ b_label; c_label ]))

let () =
  test "intersecting labels B"
    (not (is_subtype [ b_label; c_label ] [ a_label; b_label ]))

let () =
  test "different functions A" (not (is_subtype [ one_type ] [ two_type ]))

let () =
  test "different functions B" (not (is_subtype [ two_type ] [ one_type ]))

let () = test "top type of label A" (is_subtype [ a_label ] [ unit_type ])
let () = test "top type of label B" (not (is_subtype [ unit_type ] [ a_label ]))
let () = test "top type of function A" (is_subtype [ two_type ] [ unit_type ])

let () =
  test "top type of function B" (not (is_subtype [ unit_type ] [ two_type ]))

let () = test "bottom type of label A" (is_subtype [] [ a_label ])
let () = test "bottom type of label B" (not (is_subtype [ a_label ] []))

let () =
  test "extended function arg A"
    (is_subtype [ Function [ a_to_b; b_to_c ] ] [ Function [ a_to_b ] ])

let () =
  test "extended function arg B"
    (not (is_subtype [ Function [ a_to_b ] ] [ Function [ a_to_b; b_to_c ] ]))

let () =
  test "basic function subtyping A"
    (is_subtype [ Function [ ab_to_c ] ] [ Function [ a_to_bc ] ])

let () =
  test "basic function subtyping B"
    (not (is_subtype [ Function [ a_to_bc ] ] [ Function [ ab_to_c ] ]))

let () =
  test "function arg split A"
    (is_subtype [ Function [ a_to_c; b_to_c ] ] [ Function [ ab_to_c ] ])

let () =
  test "function arg split B"
    (is_subtype [ Function [ ab_to_c ] ] [ Function [ a_to_c; b_to_c ] ])

let () =
  test "large arg split A"
    (is_subtype large_arg_split_subtype large_arg_split_supertype)

let () =
  test "large arg split B"
    (not (is_subtype large_arg_split_supertype large_arg_split_subtype))

(* This potential property is not considered valid, we assume argument types don't have inhabited intersection *)
let () =
  test "invalid function return split A"
    (not (is_subtype [ Function [ a_to_bc; a_to_cd ] ] [ Function [ a_to_c ] ]))

(* But the invrse is true within the system *)
let () =
  test "function return split B"
    (is_subtype [ Function [ a_to_c ] ] [ Function [ a_to_bc; a_to_cd ] ])

(* We have not applied this property, and don't want to. We'd need to have unary argument types to split inthis way *)
let () =
  test "invalid function return split A"
    (not
       (is_subtype
          [ Function [ ([ a_label; b_label ], [ a_label; b_label ]) ] ]
          [
            Function
              [
                ([ a_label; b_label ], [ a_label ]);
                ([ a_label; b_label ], [ b_label ]);
              ];
          ]))

(* But again, the reverse is true, and this is expected *)
let () =
  test "invalid function return split B"
    (is_subtype
       [
         Function
           [
             ([ a_label; b_label ], [ a_label ]);
             ([ a_label; b_label ], [ b_label ]);
           ];
       ]
       [ Function [ ([ a_label; b_label ], [ a_label; b_label ]) ] ])

(* This subtyping relation has also not been applied *)
let () =
  test "invalid fuction arg split A"
    (not
       (is_subtype
          [ Function [ ([ Function [ a_to_b; b_to_c ] ], [ a_label ]) ] ]
          [
            Function [ ([ Function [ a_to_b ] ], [ a_label ]) ];
            Function [ ([ Function [ b_to_c ] ], [ a_label ]) ];
          ]))

(* But the inverse should be true *)
let () =
  test "invalid fuction arg split B"
    (is_subtype
       [
         Function [ ([ Function [ a_to_b ] ], [ a_label ]) ];
         Function [ ([ Function [ b_to_c ] ], [ a_label ]) ];
       ]
       [ Function [ ([ Function [ a_to_b; b_to_c ] ], [ a_label ]) ] ])

let () =
  test "basic application types"
    (get_application_type
       [ Function [ ([ a_label ], [ b_label ]) ] ]
       [ a_label ]
    = Some [ b_label ])

let () =
  test "application against label fails"
    (get_application_type [ a_label ] [ a_label ] = None)

let () =
  test "basic mismatched application"
    (get_application_type
       [ Function [ ([ b_label ], [ b_label ]) ] ]
       [ a_label ]
    = None)

let () =
  test "contravariant function application A"
    (get_application_type
       [ Function [ ([ a_label; b_label ], [ c_label ]) ] ]
       [ a_label ]
    = Some [ c_label ])

let () =
  test "contravariant function application B"
    (get_application_type
       [ Function [ ([ a_label ], [ c_label ]); ([ b_label ], [ d_label ]) ] ]
       [ a_label ]
    = Some [ c_label ])

let () =
  test "union function application A"
    (get_application_type
       [ Function [ ([ a_label; b_label ], [ c_label ]) ] ]
       [ a_label; b_label ]
    = Some [ c_label ])

let () =
  test "union function application B"
    (get_application_type
       [ Function [ ([ a_label ], [ c_label ]); ([ b_label ], [ d_label ]) ] ]
       [ a_label; b_label ]
    = Some [ c_label; d_label ])

let () =
  test "application fails when label in union"
    (get_application_type
       [ a_label; Function [ ([ a_label ], [ b_label ]) ] ]
       [ a_label ]
    = None)

let () =
  test "application fails when not all functios can be applied"
    (get_application_type
       [
         Function [ ([ b_label ], [ a_label ]) ];
         Function [ ([ a_label ], [ b_label ]) ];
       ]
       [ a_label ]
    = None)

let () =
  test "union against union application fails"
    (get_application_type
       [
         Function [ ([ b_label ], [ a_label ]) ];
         Function [ ([ a_label ], [ b_label ]) ];
       ]
       [ a_label; b_label ]
    = None)

let () =
  test "union of functions unions return types"
    (get_application_type
       [
         Function [ ([ a_label ], [ c_label ]) ];
         Function [ ([ a_label ], [ d_label ]) ];
       ]
       [ a_label ]
    = Some [ c_label; d_label ])

let () =
  test "function arguments may not overlap"
    (get_type
       (Abstraction
          [ ([ a_label ], Variable 0); ([ a_label; b_label ], Variable 0) ])
    = None)
