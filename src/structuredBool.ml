open Structured

let get_type_unsafe term = Option.get (get_type term)

let true_type = Label "True"
let false_type = Label "False"
let bool_type = [ true_type; false_type ]
let unary_bool_op = Function [ (bool_type, bool_type) ]
let binary_bool_op = Function [ (bool_type, [ unary_bool_op ]) ]
let ternary_bool_op = Function [ (bool_type, [ binary_bool_op ]) ]
let true_term = Const "True"
let false_term = Const "False"
let identity = Abstraction [ (bool_type, Variable 0) ]
let identity_type = get_type_unsafe identity

let not =
  Abstraction [ ([ true_type ], false_term); ([ false_type ], true_term) ]

let not_type = get_type_unsafe not

let and_term =
  Abstraction
    [
      ([ true_type ], identity);
      ([ false_type ], Abstraction [ (bool_type, false_term) ]);
    ]

let and_type = get_type_unsafe and_term

let or_term =
  Abstraction
    [
      ([ true_type ], Abstraction [ (bool_type, true_term) ]);
      ([ false_type ], identity);
    ]

let or_type = get_type_unsafe or_term

let if_term =
  Abstraction
    [
      ( [ true_type ],
        Abstraction [ (bool_type, Abstraction [ (bool_type, Variable 1) ]) ] );
      ( [ false_type ],
        Abstraction [ (bool_type, Abstraction [ (bool_type, Variable 0) ]) ] );
    ]

let if_type = get_type_unsafe if_term