open Structured
open StructuredArithmetic
open StructuredBool

let evaluates_to term value = eval term = value
let is_even_label_type = Label "isEven"
let is_odd_label_type = Label "isOdd"
let is_even_label_term = Const "isEven"
let is_odd_label_term = Const "isOdd"
let name_type = Label "Name"
let name_term = Const "Name"
let num_to_bool = Function [ (three_bit_num, bool_type) ]

let is_zero =
  Abstraction
    [
      ([ zero_type ], true_term);
      ( [
          one_type;
          two_type;
          three_type;
          four_type;
          five_type;
          six_type;
          seven_type;
        ],
        false_term );
    ]

let is_zero_type = get_type_unsafe is_zero

let is_even_odd =
  Fix
    (Abstraction
       [
         ( [
             Function
               [ ([ is_even_label_type; is_odd_label_type ], [ num_to_bool ]) ];
           ],
           Abstraction
             [
               ( [ is_even_label_type ],
                 Abstraction
                   [
                     ([ zero_type ], true_term);
                     ( [
                         one_type;
                         two_type;
                         three_type;
                         four_type;
                         five_type;
                         six_type;
                         seven_type;
                       ],
                       Application
                         ( Application (Variable 2, is_odd_label_term),
                           Application (decrement, Variable 0) ) );
                   ] );
               ( [ is_odd_label_type ],
                 Abstraction
                   [
                     ([ zero_type ], false_term);
                     ( [
                         one_type;
                         two_type;
                         three_type;
                         four_type;
                         five_type;
                         six_type;
                         seven_type;
                       ],
                       Application
                         ( Application (Variable 2, is_even_label_term),
                           Application (decrement, Variable 0) ) );
                   ] );
             ] );
       ])

let is_even_odd_type = get_type_unsafe is_even_odd
let is_even = Application (is_even_odd, is_even_label_term)
let is_even_type = get_type_unsafe is_even
let is_odd = Application (is_even_odd, is_odd_label_term)
let is_odd_type = get_type_unsafe is_odd
