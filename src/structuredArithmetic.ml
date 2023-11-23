open StructuredHelpers

let zero = get_typed_term_unsafe (Const "Zero")
let one = get_typed_term_unsafe (Const "One")
let two = get_typed_term_unsafe (Const "Two")
let three = get_typed_term_unsafe (Const "Three")
let four = get_typed_term_unsafe (Const "Four")
let five = get_typed_term_unsafe (Const "Five")
let six = get_typed_term_unsafe (Const "Six")
let seven = get_typed_term_unsafe (Const "Seven")

let three_bit_type =
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

let unary_num_op =
  func_to_structured_type (three_bit_type.union, three_bit_type.union)

let binary_num_op =
  func_to_structured_type (three_bit_type.union, unary_num_op.union)

let increment =
  get_typed_term_unsafe
    (Abstraction
       [
         (zero.stype, one.term);
         (one.stype, two.term);
         (two.stype, three.term);
         (three.stype, four.term);
         (four.stype, five.term);
         (five.stype, six.term);
         (six.stype, seven.term);
         (seven.stype, zero.term);
       ])

let decrement =
  get_typed_term_unsafe
    (Abstraction
       [
         (zero.stype, seven.term);
         (one.stype, zero.term);
         (two.stype, one.term);
         (three.stype, two.term);
         (four.stype, three.term);
         (five.stype, four.term);
         (six.stype, five.term);
         (seven.stype, six.term);
       ])

let add =
  get_typed_term_unsafe
    (Fix
       (Abstraction
          [
            ( binary_num_op,
              Abstraction
                [
                  (zero.stype, Abstraction [ (three_bit_type, Variable 0) ]);
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
                        ( three_bit_type,
                          Application
                            ( Application
                                ( Variable 2,
                                  Application (decrement.term, Variable 1) ),
                              Application (increment.term, Variable 0) ) );
                      ] );
                ] );
          ]))

let fib =
  get_typed_term_unsafe
    (Fix
       (Abstraction
          [
            ( unary_num_op,
              Abstraction
                [
                  (get_type_union [ zero.stype; one.stype ], one.term);
                  ( get_type_union
                      [
                        two.stype;
                        three.stype;
                        four.stype;
                        five.stype;
                        six.stype;
                        seven.stype;
                      ],
                    Application
                      ( Application
                          ( add.term,
                            Application
                              ( Variable 1,
                                Application (decrement.term, Variable 0) ) ),
                        Application
                          ( Variable 1,
                            Application
                              ( decrement.term,
                                Application (decrement.term, Variable 0) ) ) )
                  );
                ] );
          ]))
