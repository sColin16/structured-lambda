open Structured

let get_type_unsafe term = Option.get (get_type term)
let zero_type = Label "Zero"
let one_type = Label "One"
let two_type = Label "Two"
let three_type = Label "Three"
let four_type = Label "Four"
let five_type = Label "Five"
let six_type = Label "Six"
let seven_type = Label "Seven"

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

let unary_num_op = Function [ (three_bit_num, three_bit_num) ]
let binary_num_op = Function [ (three_bit_num, [ unary_num_op ]) ]
let zero_term = Const "Zero"
let one_term = Const "One"
let two_term = Const "Two"
let three_term = Const "Three"
let four_term = Const "Four"
let five_term = Const "Five"
let six_term = Const "Six"
let seven_term = Const "Seven"

let increment =
  Abstraction
    [
      ([ zero_type ], one_term);
      ([ one_type ], two_term);
      ([ two_type ], three_term);
      ([ three_type ], four_term);
      ([ four_type ], five_term);
      ([ five_type ], six_term);
      ([ six_type ], seven_term);
      ([ seven_type ], zero_term);
    ]

let increment_type = get_type_unsafe increment

let decrement =
  Abstraction
    [
      ([ zero_type ], seven_term);
      ([ one_type ], zero_term);
      ([ two_type ], one_term);
      ([ three_type ], two_term);
      ([ four_type ], three_term);
      ([ five_type ], four_term);
      ([ six_type ], five_term);
      ([ seven_type ], six_term);
    ]

let decrement_type = get_type_unsafe decrement

let add =
  Fix
    (Abstraction
       [
         ( [ binary_num_op ],
           Abstraction
             [
               ([ zero_type ], Abstraction [ (three_bit_num, Variable 0) ]);
               ( [
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
                             (Variable 2, Application (decrement, Variable 1)),
                           Application (increment, Variable 0) ) );
                   ] );
             ] );
       ])

let add_type = get_type_unsafe add

let fib =
  Fix
    (Abstraction
       [
         ( [ unary_num_op ],
           Abstraction
             [
               ([ zero_type; one_type ], one_term);
               ( [
                   two_type;
                   three_type;
                   four_type;
                   five_type;
                   six_type;
                   seven_type;
                 ],
                 Application
                   ( Application
                       ( add,
                         Application
                           (Variable 1, Application (decrement, Variable 0)) ),
                     Application
                       ( Variable 1,
                         Application
                           (decrement, Application (decrement, Variable 0)) ) )
               );
             ] );
       ])
