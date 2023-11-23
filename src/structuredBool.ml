open StructuredHelpers

let true_lambda = get_typed_term_unsafe (Const "True")
let false_lambda = get_typed_term_unsafe (Const "False")
let bool_type = get_type_union [ true_lambda.stype; false_lambda.stype ]
let unary_bool_op = func_to_structured_type (bool_type.union, bool_type.union)

let binary_bool_op =
  func_to_structured_type (bool_type.union, unary_bool_op.union)

let ternary_bool_op =
  func_to_structured_type (bool_type.union, binary_bool_op.union)

let identity_lambda =
  get_typed_term_unsafe (Abstraction [ (bool_type, Variable 0) ])

let not_lambda =
  get_typed_term_unsafe
    (Abstraction
       [
         (true_lambda.stype, false_lambda.term);
         (false_lambda.stype, true_lambda.term);
       ])

let and_lambda =
  get_typed_term_unsafe
    (Abstraction
       [
         (true_lambda.stype, identity_lambda.term);
         (false_lambda.stype, Abstraction [ (bool_type, false_lambda.term) ]);
       ])

let or_lambda =
  get_typed_term_unsafe
    (Abstraction
       [
         (true_lambda.stype, Abstraction [ (bool_type, true_lambda.term) ]);
         (false_lambda.stype, identity_lambda.term);
       ])

let if_lambda =
  get_typed_term_unsafe
    (Abstraction
       [
         ( true_lambda.stype,
           Abstraction [ (bool_type, Abstraction [ (bool_type, Variable 1) ]) ]
         );
         ( false_lambda.stype,
           Abstraction [ (bool_type, Abstraction [ (bool_type, Variable 0) ]) ]
         );
       ])
