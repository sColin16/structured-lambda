open Structured
open StructuredHelpers
open StructuredBool

let split_unary_bool =
  base_to_structured_type
    (Intersection
       [
         (true_lambda.stype.union, bool_type.union);
         (false_lambda.stype.union, bool_type.union);
       ])

let split_identity_type =
  base_to_structured_type
    (Intersection
       [
         (true_lambda.stype.union, true_lambda.stype.union);
         (false_lambda.stype.union, false_lambda.stype.union);
       ])

let split_not_type =
  base_to_structured_type
    (Intersection
       [
         (true_lambda.stype.union, false_lambda.stype.union);
         (false_lambda.stype.union, true_lambda.stype.union);
       ])

let split_unary_true_type =
  base_to_structured_type
    (Intersection
       [
         (true_lambda.stype.union, true_lambda.stype.union);
         (false_lambda.stype.union, true_lambda.stype.union);
       ])

let split_unary_false_type =
  base_to_structured_type
    (Intersection
       [
         (true_lambda.stype.union, false_lambda.stype.union);
         (false_lambda.stype.union, false_lambda.stype.union);
       ])

let unary_true_type =
  func_to_structured_type (bool_type.union, true_lambda.stype.union)

let unary_false_type =
  func_to_structured_type (bool_type.union, false_lambda.stype.union)

let name = get_typed_term_unsafe (Const "Name")
let val_lambda = get_typed_term_unsafe (Const "Val")
let zero_label = get_typed_term_unsafe (Const "Zero")
let succ = get_typed_term_unsafe (Const "Succ")

let increment_term term =
  Abstraction [ (name.stype, succ.term); (val_lambda.stype, term) ]

let zero = get_typed_term_unsafe (Abstraction [ (name.stype, zero_label.term) ])
let one = get_typed_term_unsafe (increment_term zero.term)
let two = get_typed_term_unsafe (increment_term one.term)
let three = get_typed_term_unsafe (increment_term two.term)
let four = get_typed_term_unsafe (increment_term three.term)
let five = get_typed_term_unsafe (increment_term four.term)
let six = get_typed_term_unsafe (increment_term five.term)
let seven = get_typed_term_unsafe (increment_term six.term)

let three_bit_num =
  get_type_union
    [
      zero.stype;
      one.stype;
      two.stype;
      three.stype;
      four.stype;
      five.stype;
      six.stype;
      seven.stype;
    ]

let unary_num_type =
  func_to_structured_type (three_bit_num.union, three_bit_num.union)

let binary_num_type =
  func_to_structured_type (three_bit_num.union, unary_num_type.union)

let increment_three_bit =
  get_typed_term_unsafe
    (Abstraction
       [
         ( get_type_union
             [
               zero.stype;
               one.stype;
               two.stype;
               three.stype;
               four.stype;
               five.stype;
               six.stype;
             ],
           Abstraction
             [ (name.stype, Const "Succ"); (val_lambda.stype, Variable 1) ] );
         (seven.stype, zero.term);
       ])

let decrement_three_bit =
  get_typed_term_unsafe
    (Abstraction
       [
         ( get_type_union
             [
               one.stype;
               two.stype;
               three.stype;
               four.stype;
               five.stype;
               six.stype;
               seven.stype;
             ],
           Application (Variable 0, val_lambda.term) );
         (zero.stype, seven.term);
       ])

let add_three_bit =
  get_typed_term_unsafe
    (Fix
       (Abstraction
          [
            ( binary_num_type,
              Abstraction
                [
                  (zero.stype, Abstraction [ (three_bit_num, Variable 0) ]);
                  ( get_type_union
                      [
                        one.stype;
                        two.stype;
                        three.stype;
                        four.stype;
                        five.stype;
                        six.stype;
                        seven.stype;
                      ],
                    Abstraction
                      [
                        ( three_bit_num,
                          Application
                            ( Application
                                ( Variable 2,
                                  Application
                                    (decrement_three_bit.term, Variable 1) ),
                              Application (increment_three_bit.term, Variable 0)
                            ) );
                      ] );
                ] );
          ]))

let increment_three_bit_type_expected =
  base_to_structured_type
    (Intersection
       [
         ( (get_type_union
              [
                zero.stype;
                one.stype;
                two.stype;
                three.stype;
                four.stype;
                five.stype;
                six.stype;
              ])
             .union,
           (get_type_union
              [
                one.stype;
                two.stype;
                three.stype;
                four.stype;
                five.stype;
                six.stype;
                seven.stype;
              ])
             .union );
         (seven.stype.union, zero.stype.union);
       ])

let decrement_three_bit_type_expected =
  base_to_structured_type
    (Intersection
       [
         ( (get_type_union
              [
                one.stype;
                two.stype;
                three.stype;
                four.stype;
                five.stype;
                six.stype;
                seven.stype;
              ])
             .union,
           (get_type_union
              [
                zero.stype;
                one.stype;
                two.stype;
                three.stype;
                four.stype;
                five.stype;
                six.stype;
              ])
             .union );
         (zero.stype.union, seven.stype.union);
       ])
