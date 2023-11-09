open Structured
open StructuredBool

let split_unary_bool =
  Function [ ([ true_type ], bool_type); ([ false_type ], bool_type) ]

let split_identity_type =
  Function [ ([ true_type ], [ true_type ]); ([ false_type ], [ false_type ]) ]

let split_not_type =
  Function [ ([ true_type ], [ false_type ]); ([ false_type ], [ true_type ]) ]

let split_unary_true_type =
  Function [ ([ true_type ], [ true_type ]); ([ false_type ], [ true_type ]) ]

let split_unary_false_type =
  Function [ ([ true_type ], [ false_type ]); ([ false_type ], [ false_type ]) ]

let unary_true_type = Function [ (bool_type, [ true_type ]) ]
let unary_false_type = Function [ (bool_type, [ false_type ]) ]
let name_term, name_type = get_typed_term_unsafe (Const "Name")
let val_term, val_type = get_typed_term_unsafe (Const "Val")
let zero_label_term, zero_label_type = get_typed_term_unsafe (Const "Zero")
let succ_term, succ_type = get_typed_term_unsafe (Const "Succ")

let increment_term term =
  Abstraction [ (name_type, succ_term); (val_type, term) ]

let zero_term, zero_type =
  get_typed_term_unsafe (Abstraction [ (name_type, zero_label_term) ])

let one_term, one_type = get_typed_term_unsafe (increment_term zero_term)
let two_term, two_type = get_typed_term_unsafe (increment_term one_term)
let three_term, three_type = get_typed_term_unsafe (increment_term two_term)
let four_term, four_type = get_typed_term_unsafe (increment_term three_term)
let five_term, five_type = get_typed_term_unsafe (increment_term four_term)
let six_term, six_type = get_typed_term_unsafe (increment_term five_term)
let seven_term, seven_type = get_typed_term_unsafe (increment_term six_term)

let three_bit_num =
  List.flatten
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

let unary_num_type = Function [ (three_bit_num, three_bit_num) ]
let binary_num_type = Function [ (three_bit_num, [ unary_num_type ]) ]

let increment_three_bit, increment_three_bit_type =
  get_typed_term_unsafe
    (Abstraction
       [
         ( List.flatten
             [
               zero_type;
               one_type;
               two_type;
               three_type;
               four_type;
               five_type;
               six_type;
             ],
           Abstraction [ (name_type, Const "Succ"); (val_type, Variable 1) ] );
         (seven_type, zero_term);
       ])

let decrement_three_bit, decrement_three_bit_type =
  get_typed_term_unsafe
    (Abstraction
       [
         ( List.flatten
             [
               one_type;
               two_type;
               three_type;
               four_type;
               five_type;
               six_type;
               seven_type;
             ],
           Application (Variable 0, val_term) );
         (zero_type, seven_term);
       ])

let add_three_bit, add_three_bit_type =
  get_typed_term_unsafe
    (Fix
       (Abstraction
          [
            ( [ binary_num_type ],
              Abstraction
                [
                  (zero_type, Abstraction [ (three_bit_num, Variable 0) ]);
                  ( List.flatten
                      [
                        one_type;
                        two_type;
                        three_type;
                        four_type;
                        five_type;
                        six_type;
                        seven_type;
                      ],
                    Abstraction
                      [
                        ( three_bit_num,
                          Application
                            ( Application
                                ( Variable 2,
                                  Application (decrement_three_bit, Variable 1)
                                ),
                              Application (increment_three_bit, Variable 0) ) );
                      ] );
                ] );
          ]))

let increment_three_bit_type_expected =
  Function
    [
      ( List.flatten
          [
            zero_type;
            one_type;
            two_type;
            three_type;
            four_type;
            five_type;
            six_type;
          ],
        List.flatten
          [
            one_type;
            two_type;
            three_type;
            four_type;
            five_type;
            six_type;
            seven_type;
          ] );
      (seven_type, zero_type);
    ]

let decrement_three_bit_type_expected =
  Function
    [
      ( List.flatten
          [
            one_type;
            two_type;
            three_type;
            four_type;
            five_type;
            six_type;
            seven_type;
          ],
        List.flatten
          [
            zero_type;
            one_type;
            two_type;
            three_type;
            four_type;
            five_type;
            six_type;
          ] );
      (zero_type, seven_type);
    ]

(*
  Types to test:
  three bit numbers, increment, decrement, addition and other wrap-around functions on this finite type
*)
