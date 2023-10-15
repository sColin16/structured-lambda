(** Lambda Calculus interpreter for calculus formalized with de Bruijn indices *)

(* TODO: consider adding a value type that we convert to when we evaluate *)
type term = Abstraction of term | Application of term * term | Variable of int

(** Converts a term into a human-interpretable string *)
let rec to_string (term : term) =
  match term with
  | Variable var_num -> Printf.sprintf "%i" var_num
  | Abstraction inner_term -> Printf.sprintf "\\.%s" (to_string inner_term)
  | Application (t1, t2) ->
      Printf.sprintf "(%s) (%s)" (to_string t1) (to_string t2)

(** Evaluates a lambda term into a value *)
let rec eval (term : term) =
  match term with
  | Abstraction _ | Variable _ | Application (Variable _, _) -> term
  | Application (Application (t1, t2), t3) ->
      let left_evaluated = eval (Application (t1, t2)) in
      eval (Application (left_evaluated, t3))
  | Application (Abstraction t1, Application (t2, t3)) ->
      let right_evaluated = eval (Application (t2, t3)) in
      eval (Application (Abstraction t1, right_evaluated))
  | Application (Abstraction t1, Abstraction t2) ->
      eval (substitute (Abstraction t2) t1)
  | Application (Abstraction t1, Variable num) ->
      eval (substitute (Variable num) t1)

(** [substitute with_term in_term] Replaces appropriate instances of the 0 variable within the in_term with the with_term
    Automatically handles the intricacies of the de Bruijn indices *)
and substitute (with_term : term) (in_term : term) =
  let shifted_with_term = shift with_term 1 in
  let substitution_result = substitute_rec 0 shifted_with_term in_term in
  let final_resut = shift substitution_result (-1) in
  final_resut

and substitute_rec (variable_num : int) (with_term : term) (in_term : term) =
  match in_term with
  | Variable internal_num ->
      if variable_num == internal_num then with_term else Variable internal_num
  | Abstraction internal_term ->
      Abstraction
        (substitute_rec (variable_num + 1) (shift with_term 1) internal_term)
  | Application (t1, t2) ->
      Application
        ( substitute_rec variable_num with_term t1,
          substitute_rec variable_num with_term t2 )

and shift (term : term) (shift_amt : int) = shift_rec term shift_amt 0

and shift_rec (term : term) (shift_amt : int) (cutoff : int) =
  match term with
  | Variable var_num ->
      if var_num >= cutoff then Variable (var_num + shift_amt)
      else Variable var_num
  | Abstraction internal_term ->
      Abstraction (shift_rec internal_term shift_amt (cutoff + 1))
  | Application (t1, t2) ->
      Application (shift_rec t1 shift_amt cutoff, shift_rec t2 shift_amt cutoff)

let true_lambda = Abstraction (Abstraction (Variable 1))
let false_lambda = Abstraction (Abstraction (Variable 0))

let if_lambda =
  Abstraction
    (Abstraction
       (Abstraction
          (Application (Application (Variable 2, Variable 1), Variable 0))))

let and_lambda =
  Abstraction
    (Abstraction
       (Application (Application (Variable 1, Variable 0), false_lambda)))

let or_lambda =
  Abstraction
    (Abstraction
       (Application (Application (Variable 1, true_lambda), Variable 0)))

let not_lambda =
  Abstraction
    (Application (Application (Variable 0, false_lambda), true_lambda))

let does_evaluate_to (start_term : term) (final_value : term) =
  let evaluation_result = eval start_term in
  if not (evaluation_result = final_value) then
    let () =
      Printf.printf
        "Evaluation check failed. Evaluated to this term:\n\
         %s\n\n\
         But expected this term:\n\
         %s\n\n"
        (to_string evaluation_result)
        (to_string final_value)
    in
    false
  else true

let does_evaluate_to_bool (term : term) (final_bool : bool) =
  let new_term =
    Application
      (Application (Application (if_lambda, term), Variable 0), Variable 1)
  in
  if final_bool then does_evaluate_to new_term (Variable 0)
  else does_evaluate_to new_term (Variable 1)

let test (name : string) (result : bool) =
  Printf.printf "%s: %s\n" (if result then "PASS" else "FAIL") name

let true_test = Application (Application (true_lambda, Variable 0), Variable 1)
let false_test = Application (Application (false_lambda, Variable 0), Variable 1)
let not_test_a = Application (not_lambda, true_lambda)
let not_test_b = Application (not_lambda, false_lambda)

let if_test_a =
  Application
    ( Application (Application (if_lambda, true_lambda), true_lambda),
      false_lambda )

let if_test_b =
  Application
    ( Application (Application (if_lambda, false_lambda), true_lambda),
      false_lambda )

let true_and_true =
  Application (Application (and_lambda, true_lambda), true_lambda)

let true_and_false =
  Application (Application (and_lambda, true_lambda), false_lambda)

let false_and_true =
  Application (Application (and_lambda, false_lambda), true_lambda)

let false_and_false =
  Application (Application (and_lambda, false_lambda), false_lambda)

let true_or_true =
  Application (Application (or_lambda, true_lambda), true_lambda)

let true_or_false =
  Application (Application (or_lambda, true_lambda), false_lambda)

let false_or_true =
  Application (Application (or_lambda, false_lambda), true_lambda)

let false_or_false =
  Application (Application (or_lambda, false_lambda), false_lambda)

let () = test "true" (does_evaluate_to true_test (Variable 0))
let () = test "false" (does_evaluate_to false_test (Variable 1))
let () = test "not true is false" (does_evaluate_to_bool not_test_a false)
let () = test "not false is true" (does_evaluate_to_bool not_test_b true)
let () = test "if true" (does_evaluate_to_bool if_test_a true)
let () = test "if false" (does_evaluate_to_bool if_test_b false)
let () = test "true and true" (does_evaluate_to_bool true_and_true true)
let () = test "true and false" (does_evaluate_to_bool true_and_false false)
let () = test "false and true" (does_evaluate_to_bool false_and_true false)
let () = test "false and false" (does_evaluate_to_bool false_and_false false)
let () = test "true or true" (does_evaluate_to_bool true_or_true true)
let () = test "true or false" (does_evaluate_to_bool true_or_false true)
let () = test "false or true" (does_evaluate_to_bool false_or_true true)
let () = test "false or false" (does_evaluate_to_bool false_or_false false)
