type lambda_type = Func of lambda_type * lambda_type | Bool

type term =
  | Abstraction of lambda_type * term
  | Application of term * term
  | Variable of int
  | If of term * term * term
  | True
  | False

module TypeContextMap = Map.Make (struct
  type t = int

  let compare = compare
end)

type type_context_map = lambda_type TypeContextMap.t

let rec type_to_string (lambda_type : lambda_type) =
  match lambda_type with
  | Bool -> "Bool"
  | Func (t1, t2) ->
      Printf.sprintf "(%s -> %s)" (type_to_string t1) (type_to_string t2)

let opt_type_to_string (lambda_type : lambda_type option) =
  match lambda_type with None -> "Ill-typed" | Some t -> type_to_string t

(* let rec term_to_string (term : term) =
   match term with
   | Variable var_num -> Printf.sprintf "%i" var_num
   | Abstraction (arg_type, inner_term) ->
       Printf.sprintf "\\:%s.%s" (type_to_string arg_type)
         (term_to_string inner_term)
   | Application (t1, t2) ->
       Printf.sprintf "(%s) (%s)" (term_to_string t1) (term_to_string t2)
   | If (t1, t2, t3) ->
       Printf.sprintf "if (%s) then (%s) else (%s)" (term_to_string t1)
         (term_to_string t2) (term_to_string t3)
   | True -> "True"
   | False -> "False" *)

let rec type_lambda_term (term : term) =
  type_lambda_term_rec term TypeContextMap.empty (-1)

and type_lambda_term_rec (term : term) (context : type_context_map)
    (level : int) =
  match term with
  | True | False -> Some Bool
  | If (t1, t2, t3) -> (
      let guard_type_opt = type_lambda_term_rec t1 context level in
      match guard_type_opt with
      | None | Some (Func (_, _)) -> None
      | Some Bool ->
          let branch1_type_opt = type_lambda_term_rec t2 context level in
          let branch2_type_opt = type_lambda_term_rec t3 context level in
          if branch1_type_opt = branch2_type_opt then
            match (branch1_type_opt, branch2_type_opt) with
            | Some branch1_type, _ -> Some branch1_type
            | _ -> None
          else None)
  | Application (t1, t2) -> (
      let left_type = type_lambda_term_rec t1 context level in
      let right_type = type_lambda_term_rec t2 context level in
      match (left_type, right_type) with
      | Some (Func (param_type, return_type)), Some arg_type ->
          if arg_type = param_type then Some return_type else None
      | Some (Func (_, _)), _ | Some Bool, _ | None, _ -> None)
  | Abstraction (arg_type, body_term) -> (
      let optional_body_type =
        type_lambda_term_rec body_term
          (TypeContextMap.add (level + 1) arg_type context)
          (level + 1)
      in
      match optional_body_type with
      | Some body_type -> Some (Func (arg_type, body_type))
      | None -> None)
  | Variable var_num -> TypeContextMap.find_opt (level - var_num) context

let not_lambda = Abstraction (Bool, If (Variable 0, False, True))
let applied_not_lambda = Application (not_lambda, True)

let and_lambda =
  Abstraction (Bool, Abstraction (Bool, If (Variable 1, Variable 0, False)))

let or_lambda =
  Abstraction (Bool, Abstraction (Bool, If (Variable 1, True, Variable 0)))

let apply_bool_operator =
  Abstraction
    (Func (Bool, Bool), Abstraction (Bool, Application (Variable 1, Variable 0)))

let apply_binary =
  Abstraction
    ( Func (Bool, Func (Bool, Bool)),
      Abstraction
        ( Bool,
          Abstraction
            ( Bool,
              Application (Application (Variable 2, Variable 1), Variable 0) )
        ) )

let apply_binary_example = Application(Application(Application(apply_binary, and_lambda), True), False)

let poorly_typed_term = Application(apply_binary, apply_bool_operator)
let poorly_typed_term2 = If(True, and_lambda, False)

let test (name : string) (result : bool) =
  Printf.printf "%s: %s\n" (if result then "PASS" else "FAIL") name

let not_lambda_type = type_lambda_term not_lambda
let applied_not_lambda_type = type_lambda_term applied_not_lambda
let and_lambda_type = type_lambda_term and_lambda
let or_lambda_type = type_lambda_term or_lambda
let apply_bool_type = type_lambda_term apply_bool_operator
let apply_binary_type = type_lambda_term apply_binary
let apply_binary_example_type = type_lambda_term apply_binary_example
let poorly_typed_term_type = type_lambda_term poorly_typed_term
let poorly_typed_term2_type = type_lambda_term poorly_typed_term2

let () = test "Not function types" (not_lambda_type = Some (Func (Bool, Bool)))
let () = test "Applied not function types" (applied_not_lambda_type = Some Bool)

let () =
  test "Or function types"
    (and_lambda_type = Some (Func (Bool, Func (Bool, Bool))))

let () =
  test "And function types"
    (or_lambda_type = Some (Func (Bool, Func (Bool, Bool))))

let () =
  test "Apply bool function types"
    (apply_bool_type = Some (Func (Func (Bool, Bool), Func (Bool, Bool))))

let () = test "Apply binary function types" (apply_binary_type = Some(Func(Func(Bool, Func(Bool, Bool)), Func(Bool, Func(Bool, Bool)))))
let () = test "Apply binary function example" (apply_binary_example_type = Some(Bool))

let () = test "Poorly typed application" (poorly_typed_term_type = None)
let () = test "Poorly typed if" (poorly_typed_term2_type = None)

let () = Printf.printf "Not: %s\n" (opt_type_to_string not_lambda_type)
let () = Printf.printf "And: %s\n" (opt_type_to_string and_lambda_type)
let () = Printf.printf "Or: %s\n" (opt_type_to_string or_lambda_type)
let () = Printf.printf "Apply: %s\n" (opt_type_to_string apply_bool_type)
let () = Printf.printf "Apply binary: %s\n" (opt_type_to_string apply_binary_type)
let () = Printf.printf "Apply binary example: %s\n" (opt_type_to_string apply_binary_example_type)
let () = Printf.printf "Poorly typed term: %s\n" (opt_type_to_string poorly_typed_term_type)
