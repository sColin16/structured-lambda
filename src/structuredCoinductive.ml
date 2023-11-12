open Structured
open StructuredHelpers

let name = get_typed_term_unsafe (Const "Name")
let val_lambda = get_typed_term_unsafe (Const "Val")
let zero = get_typed_term_unsafe (Const "Zero")
let succ = get_typed_term_unsafe (Const "Succ")
let pred = get_typed_term_unsafe (Const "Pred")
let zero = get_typed_term_unsafe (Abstraction [ (name.stype, zero.term) ])

let rec generate_typed_num (num : int) =
  let term = if num >= 0 then generate_pos_num num else generate_neg_num num in
  get_typed_term_unsafe term

and generate_pos_num (num : int) = generate_pos_num_rec num zero.term
and generate_neg_num (num : int) = generate_neg_num_rec num zero.term

and generate_pos_num_rec (num : int) (base_term : term) =
  if num <= 0 then base_term
  else
    generate_pos_num_rec (num - 1)
      (Abstraction [ (name.stype, succ.term); (val_lambda.stype, base_term) ])

and generate_neg_num_rec (num : int) (base_term : term) =
  if num >= 0 then base_term
  else
    generate_neg_num_rec (num + 1)
      (Abstraction [ (name.stype, pred.term); (val_lambda.stype, base_term) ])

let single_rec_step (name_type : structured_type) (val_type : union_type) =
  base_to_structured_type
    (Intersection
       [
         (name.stype.union, name_type.union); (val_lambda.stype.union, val_type);
       ])

let rec generate_rec_step (name_type : structured_type) (val_type : union_type)
    (num : int) =
  generate_rec_step_rec name_type val_type num

and generate_rec_step_rec (name_type : structured_type) (base_type : union_type)
    (num : int) =
  if num = 0 then union_to_structured_type base_type
  else
    generate_rec_step_rec name_type (single_rec_step name_type base_type).union
      (num - 1)

let generate_succ_rec_step (num : int) =
  generate_rec_step succ.stype [ TypeVar 0 ] num

let generate_pred_rec_step (num : int) =
  generate_rec_step pred.stype [ TypeVar 0 ] num

let one = generate_typed_num 1
let two = generate_typed_num 2
let neg_one = generate_typed_num (-1)
let neg_two = generate_typed_num (-2)

let positive_number =
  build_structured_type [ TypeVar 0 ]
    [ get_flat_union_type [ one.stype; generate_succ_rec_step 1 ] ]

let negative_number =
  build_structured_type [ TypeVar 0 ]
    [ get_flat_union_type [ neg_one.stype; generate_pred_rec_step 1 ] ]

let natural_number = get_type_union [ zero.stype; positive_number ]
let non_negative_number = get_type_union [ zero.stype; negative_number ]
let integer = get_type_union [ negative_number; zero.stype; positive_number ]

let pos_even_number =
  build_structured_type [ TypeVar 0 ]
    [ get_flat_union_type [ two.stype; generate_succ_rec_step 2 ] ]

let neg_even_number =
  build_structured_type [ TypeVar 0 ]
    [ get_flat_union_type [ neg_two.stype; generate_pred_rec_step 2 ] ]

let pos_odd_number =
  build_structured_type [ TypeVar 0 ]
    [ get_flat_union_type [ one.stype; generate_succ_rec_step 2 ] ]

let neg_odd_number =
  build_structured_type [ TypeVar 0 ]
    [ get_flat_union_type [ neg_one.stype; generate_pred_rec_step 2 ] ]

let even_integer =
  get_type_union [ neg_even_number; zero.stype; pos_even_number ]

let odd_integer = get_type_union [ neg_odd_number; pos_odd_number ]

let pos_infinity =
  build_structured_type [ TypeVar 0 ]
    [ get_flat_union_type [ generate_succ_rec_step 1 ] ]

let neg_infinity =
  build_structured_type [ TypeVar 0 ]
    [ get_flat_union_type [ generate_pred_rec_step 1 ] ]

let infinity = get_type_union [ pos_infinity; neg_infinity ]
