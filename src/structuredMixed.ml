open StructuredHelpers
open StructuredArithmetic
open StructuredBool

let is_even_label = get_typed_term_unsafe (Const "isEven")
let is_odd_label = get_typed_term_unsafe (Const "isOdd")

let is_even_odd_label =
  get_type_union [ is_even_label.stype; is_odd_label.stype ]

let name = get_typed_term_unsafe (Const "Name")
let num_to_bool = func_to_structured_type (three_bit_type.union, bool_type.union)

let is_zero =
  get_typed_term_unsafe
    (Abstraction
       [
         (zero.stype, true_lambda.term);
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
           false_lambda.term );
       ])

let is_even_odd =
  get_typed_term_unsafe
    (Fix
       (Abstraction
          [
            ( func_to_structured_type
                (is_even_odd_label.union, num_to_bool.union),
              Abstraction
                [
                  ( is_even_label.stype,
                    Abstraction
                      [
                        (zero.stype, true_lambda.term);
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
                          Application
                            ( Application (Variable 2, is_odd_label.term),
                              Application (decrement.term, Variable 0) ) );
                      ] );
                  ( is_odd_label.stype,
                    Abstraction
                      [
                        (zero.stype, false_lambda.term);
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
                          Application
                            ( Application (Variable 2, is_even_label.term),
                              Application (decrement.term, Variable 0) ) );
                      ] );
                ] );
          ]))

let is_even =
  get_typed_term_unsafe (Application (is_even_odd.term, is_even_label.term))

let is_odd =
  get_typed_term_unsafe (Application (is_even_odd.term, is_odd_label.term))
