type structured_type = base_type list
and base_type = Label of string | Function of unary_function list
and unary_function = structured_type * structured_type

type term =
  | Abstraction of (structured_type * term) list
  | Application of term * term
  | Variable of int
  | Const of string

module TypeContextMap = Map.Make (struct
  type t = int

  let compare = compare
end)

type type_context_map = structured_type TypeContextMap.t

let rec type_to_string (lambda_type : structured_type) =
  Printf.sprintf "(%s)"
    (String.concat "|" (List.map base_type_to_string lambda_type))

and base_type_to_string (base_type : base_type) =
  match base_type with
  | Label name -> name
  | Function func_list -> Printf.sprintf "{%s}" (func_type_to_string func_list)

and func_type_to_string (func_list : unary_function list) =
  String.concat "," (List.map unary_func_type_to_string func_list)

and unary_func_type_to_string ((arg, return) : unary_function) =
  Printf.sprintf "%s->%s" (type_to_string arg) (type_to_string return)

let rec term_to_string (term : term) =
  match term with
  | Const name -> name
  | Variable var_num -> Printf.sprintf "%i" var_num
  | Abstraction branches ->
      let branch_strings = List.map branch_to_string branches in
      Printf.sprintf "\\.{%s}" (String.concat "," branch_strings)
  | Application (t1, t2) ->
      Printf.sprintf "(%s) (%s)" (term_to_string t1) (term_to_string t2)

and branch_to_string (branch_type, branch_body) =
  Printf.sprintf "%s:%s"
    (type_to_string branch_type)
    (term_to_string branch_body)

let list_product (list1 : 'a list) (list2 : 'b list) =
  List.flatten (List.map (fun x1 -> List.map (fun x2 -> (x1, x2)) list2) list1)

let extract_first (list : ('a * 'b) list) =
  List.map (fun (first, _) -> first) list

let extract_second (list : ('a * 'b) list) =
  List.map (fun (_, second) -> second) list

(* TODO: remov duplicate and subtypes from the union after flattening *)
let extract_composite_args (branches : unary_function list) =
  List.flatten (extract_first branches)

let extract_composite_return (branches : unary_function list) =
  List.flatten (extract_second branches)

let flat_map_opt2 (func : 'a -> 'b -> 'c option) (opta : 'a option)
    (optb : 'b option) =
  match (opta, optb) with
  | None, _ | _, None -> None
  | Some a, Some b -> func a b

let map_opt2 (func : 'a -> 'b -> 'c) (opta : 'a option) (optb : 'b option) =
  flat_map_opt2 (fun a b -> Some (func a b)) opta optb

let opt_list_to_list_opt (input : 'a option list) : 'a list option =
  let list_opt =
    List.fold_left
      (fun acc elt_opt -> map_opt2 List.cons elt_opt acc)
      (Some []) input
  in
  (* Reverse the list to maintain the order. Shouldn't really matter, but oh well *)
  Option.map List.rev list_opt

(** [has_intersection type1 type2] determines if the intersection of the two types is inhabited
    More specfically, determines if there exists a subtype of the intersection of the two types, other than the bottom type *)
let rec has_intersection (t1 : structured_type) (t2 : structured_type) =
  (* The intersection of two union types is inhabited if any pairs in the uion of inhaboted *)
  let union_pairs = list_product t1 t2 in
  List.exists has_intersection_base union_pairs

and has_intersection_base type_pair =
  match type_pair with
  (* Two labels have an intersection only when they're equal *)
  | Label a, Label b -> a = b
  (* unit/top type intersected with any type is that type *)
  | _, Function [] | Function [], _ -> true
  (* Non-empty functions and labels have have uninhabited intersections *)
  | Label _, Function (_ :: _) | Function (_ :: _), Label _ -> false
  (* The intersection of two non-unit function types is inhabited if each pair of unary function types is inhabited *)
  | Function first, Function second ->
      let function_pairs = list_product first second in
      List.for_all has_intersection_func function_pairs

and has_intersection_func
    (((arg1, return1), (arg2, return2)) : unary_function * unary_function) =
  let args_intersect = has_intersection arg1 arg2 in
  let returns_intersect = has_intersection return1 return2 in
  (* Unary function intersection is inhabited if the argument types don't intersect (intersection
     is simply the ad-hoc polymorphic function), or if the argument types do intersect, but the return
     types do as well (the intersecting argument component maps to the intersection
     of the return types)*)
  (not args_intersect) || returns_intersect

(** [is_subtype type1 type2] determines if [type1] is a subtype of [type2] *)
let rec is_subtype (t1 : structured_type) (t2 : structured_type) =
  (* a type is a subtype of another, if for every type in the first type,
     there exists a supertype in the second type *)
  List.for_all
    (fun base_type1 ->
      List.exists (fun base_type2 -> is_base_subtype base_type1 base_type2) t2)
    t1

and is_base_subtype (t1 : base_type) (t2 : base_type) =
  match (t1, t2) with
  (* Labels are subtypes when they are the same label *)
  | Label a, Label b -> a = b
  (* Labels are considered a subtype of the unit/top type *)
  | Label _, Function [] -> true
  (* Otherwise, labels and functios have no subtype relation between them *)
  | Label _, Function (_ :: _) | Function _, Label _ -> false
  (* Two functions are subtypes if the first function accepts at least as many
     argument types, and returns subtypes for every argument types that intersects *)
  | Function first, Function second ->
      let first_args = extract_composite_args first in
      let second_args = extract_composite_args second in
      let function_pairs = list_product first second in
      let exhaustive_arg_coverage = is_subtype second_args first_args in
      let return_type_constaint =
        List.for_all is_unary_func_subtype function_pairs
      in
      exhaustive_arg_coverage && return_type_constaint

and is_unary_func_subtype
    (((arg1, return1), (arg2, return2)) : unary_function * unary_function) =
  let args_intersect = has_intersection arg1 arg2 in
  let return_subtype = is_subtype return1 return2 in
  (* Two unary function are subtype-compatible if their arguments don't intersect (other check will
      confirm arguments are exhaustive), or they do intersect, but the return type is a subtype
     (to guarantee thefunction cannot return a supertype for the intersecting argument) *)
  (not args_intersect) || return_subtype

(** [get_application_type func_type arg_type] determines the resulting type of
    applying a term of type [arg_type] to a term of type [func_type], if
    the function can be applied to the argument *)
let rec get_application_type (func : structured_type) (arg : structured_type) =
  (* The argument should be applicable to any function in the union, so acquire the type of applying the arg to each option *)
  let return_types_opt = List.map (get_application_option_type arg) func in
  (* Aggregate the return types - if anyof them were none, the application is not well-typed *)
  let return_types = opt_list_to_list_opt return_types_opt in
  (* Join all of the return types into a single union types *)
  Option.map List.flatten return_types

and get_application_option_type (arg : structured_type)
    (func_option : base_type) =
  match func_option with
  (* A label type cannot be applied *)
  | Label _ -> None
  (* An application against a funfction type is well-typed if the function accepts at least as many arguments.
     The return type is the union of all return types that the argument might match with *)
  | Function func_list ->
      let func_params = extract_composite_args func_list in
      let exhaustive_arg_coverage = is_subtype arg func_params in
      if not exhaustive_arg_coverage then None
      else
        Some
          (List.fold_left
             (fun acc (func_arg, func_return) ->
               if has_intersection arg func_arg then acc @ func_return
               else acc)
             [] func_list)

(** [type_lambda_term term] determines the type of a term, if it is well-typed *)
let rec type_lambda_term (term : term) =
  type_lambda_term_rec term TypeContextMap.empty (-1)

and type_lambda_term_rec (term : term) (context : type_context_map)
    (level : int) : structured_type option =
  match term with
  | Const name -> Some [ Label name ]
  | Application (t1, t2) ->
      let left_type = type_lambda_term_rec t1 context level in
      let right_type = type_lambda_term_rec t2 context level in
      flat_map_opt2 get_application_type left_type right_type
  (* TODO: confirm that the argument types all have apriwise empty intersections *)
  | Abstraction definitions ->
      let arg_types = extract_first definitions in
      (* let arg_pairs = list_product arg_types arg_types in *)
      let disjoint_args = true in
      (* TODO: check all pairs not with self for disjointedness. Might need a new function for that *)
      if not disjoint_args then None
      else
        let body_types_opt =
          List.map (type_abstraction_branch context level) definitions
        in
        let return_types_opt = opt_list_to_list_opt body_types_opt in
        Option.map
          (fun return_types ->
            [ Function (List.combine arg_types return_types) ])
          return_types_opt
  | Variable var_num -> TypeContextMap.find_opt (level - var_num) context

and type_abstraction_branch (context : type_context_map) (level : int)
    ((branch_type, branch_body) : structured_type * term) =
  type_lambda_term_rec branch_body
    (TypeContextMap.add (level + 1) branch_type context)
    (level + 1)

let rec eval (term : term) =
  match term with
  (* Application of a const should't happen under the type system *)
  | Abstraction _ | Variable _
  | Application (Variable _, _)
  | Const _
  | Application (Const _, _) ->
      term
  | Application (Application (t1, t2), t3) ->
      let left_evaluated = eval (Application (t1, t2)) in
      eval (Application (left_evaluated, t3))
  | Application (Abstraction t1, Application (t2, t3)) ->
      let right_evaluated = eval (Application (t2, t3)) in
      eval (Application (Abstraction t1, right_evaluated))
  | Application (Abstraction branches, t2) ->
      let executed_branch = resolve_branch branches t2 in
      eval (substitute t2 executed_branch)

and resolve_branch branches argument =
  (* TODO: can I always associate a base type with arguments to guarantee I can determine
     the appropriate branch, without needing to recompute each time? *)
  let argument_type =
    match type_lambda_term argument with
    | None -> raise (Invalid_argument "Yep")
    | Some a -> a
  in
  let _, resolved_branch =
    List.find
      (fun (branch_type, _) -> is_subtype argument_type branch_type)
      branches
  in
  resolved_branch

and substitute (with_term : term) (in_term : term) =
  let shifted_with_term = shift with_term 1 in
  let substitution_result = substitute_rec 0 shifted_with_term in_term in
  let final_resut = shift substitution_result (-1) in
  final_resut

and substitute_rec (variable_num : int) (with_term : term) (in_term : term) =
  match in_term with
  | Variable internal_num ->
      if variable_num == internal_num then with_term else in_term
  | Abstraction internal_term ->
      (* TODO: I can definitely opimize to prevent duplicate shifts *)
      let substituted_bodies =
        List.map
          (fun (branch_type, branch_body) ->
            ( branch_type,
              substitute_rec (variable_num + 1) (shift with_term 1) branch_body
            ))
          internal_term
      in
      Abstraction substituted_bodies
  | Application (t1, t2) ->
      Application
        ( substitute_rec variable_num with_term t1,
          substitute_rec variable_num with_term t2 )
  | Const _ -> in_term

and shift (term : term) (shift_amt : int) = shift_rec term shift_amt 0

and shift_rec (term : term) (shift_amt : int) (cutoff : int) =
  match term with
  | Variable var_num ->
      if var_num >= cutoff then Variable (var_num + shift_amt)
      else Variable var_num
  | Abstraction internal_term ->
      let mapped_branches =
        List.map
          (fun (branch_type, branch_body) ->
            (branch_type, shift_rec branch_body shift_amt (cutoff + 1)))
          internal_term
      in
      Abstraction mapped_branches
  | Application (t1, t2) ->
      Application (shift_rec t1 shift_amt cutoff, shift_rec t2 shift_amt cutoff)
  | Const _ -> term

let test (name : string) (result : bool) =
  Printf.printf "%s: %s\n" (if result then "PASS" else "FAIL") name

let b = [ Label "A"; Function [ ([ Label "A" ], [ Label "B" ]) ] ]
let c = [ Function [ ([ Label "A" ], [ Label "B" ]) ]; Label "A" ]
let a_label = Label "A"
let b_label = Label "B"
let c_label = Label "C"
let d_label = Label "D"
let e_label = Label "E"
let name_label = Label "Name"
let val_label = Label "Val"
let zero_label = Label "Zero"
let succ_label = Label "Succ"
let zero = Function [ ([ name_label ], [ zero_label ]) ]

let one =
  Function [ ([ name_label ], [ succ_label ]); ([ val_label ], [ zero ]) ]

let two =
  Function [ ([ name_label ], [ succ_label ]); ([ val_label ], [ one ]) ]

(* A -> (B -> C | D) *)
let nested_a =
  Function
    [ ([ a_label ], [ Function [ ([ b_label ], [ c_label; d_label ]) ] ]) ]

(* A -> (B -> D | E) *)
let nested_b =
  Function
    [ ([ a_label ], [ Function [ ([ b_label ], [ d_label; e_label ]) ] ]) ]

let a_to_b = ([ a_label ], [ b_label ])
let a_to_c = ([ a_label ], [ c_label ])
let b_to_c = ([ b_label ], [ c_label ])
let ab_to_c = ([ a_label; b_label ], [ c_label ])
let a_to_bc = ([ a_label ], [ b_label; c_label ])
let a_to_cd = ([ a_label ], [ c_label; d_label ])
let joinable_a = Function [ a_to_b ]
let joinable_b = Function [ b_to_c ]
let unit_type = Function []

let large_arg_split_subtype =
  [
    Function
      [
        ([ a_label; b_label; c_label ], [ c_label; d_label ]);
        ([ a_label; b_label ], [ c_label ]);
      ];
  ]

let large_arg_split_supertype =
  [ Function [ ([ a_label; b_label ], [ c_label; d_label; e_label ]) ] ]

let () = test "simple empty" (not (has_intersection [ a_label ] [ b_label ]))

let () =
  test "simple identical" (has_intersection [ a_label ] [ a_label ])

let () = test "out of order identical" (has_intersection b c)

let () =
  test "single label inhabited"
    (has_intersection [ a_label; b_label ] [ b_label; c_label ])

let () = test "zero and zero" (has_intersection [ zero ] [ zero ])
let () = test "zero and one" (not (has_intersection [ zero ] [ one ]))
let () = test "one and two" (not (has_intersection [ one ] [ two ]))
let () = test "zero and two" (not (has_intersection [ zero ] [ two ]))

let () =
  test "nested test" (has_intersection [ nested_a ] [ nested_b ])

let () =
  test "joinable" (has_intersection [ joinable_a ] [ joinable_b ])

let () = test "label reflexivity" (is_subtype [ a_label ] [ a_label ])
let () = test "function reflexivity" (is_subtype [ one ] [ one ])

let () =
  test "label union subtyping A"
    (is_subtype [ a_label ] [ a_label; b_label; one; zero ])

let () =
  test "label union subtyping B"
    (not (is_subtype [ a_label; b_label; one; zero ] [ a_label ]))

let () =
  test "function union subtyping A" (is_subtype [ two ] [ two; one; a_label ])

let () =
  test "function union subtyping B"
    (not (is_subtype [ two; one; a_label ] [ two ]))

let () = test "different labels A" (not (is_subtype [ a_label ] [ b_label ]))
let () = test "different labels B" (not (is_subtype [ b_label ] [ a_label ]))

let () =
  test "disjoint labels"
    (not (is_subtype [ a_label; b_label ] [ c_label; d_label ]))

let () =
  test "intersecting labels A"
    (not (is_subtype [ a_label; b_label ] [ b_label; c_label ]))

let () =
  test "intersecting labels B"
    (not (is_subtype [ b_label; c_label ] [ a_label; b_label ]))

let () = test "different functions A" (not (is_subtype [ one ] [ two ]))
let () = test "different functions B" (not (is_subtype [ two ] [ one ]))
let () = test "top type of label A" (is_subtype [ a_label ] [ unit_type ])
let () = test "top type of label B" (not (is_subtype [ unit_type ] [ a_label ]))
let () = test "top type of function A" (is_subtype [ two ] [ unit_type ])
let () = test "top type of function B" (not (is_subtype [ unit_type ] [ two ]))
let () = test "bottom type of label A" (is_subtype [] [ a_label ])
let () = test "bottom type of label B" (not (is_subtype [ a_label ] []))

let () =
  test "extended function arg A"
    (is_subtype [ Function [ a_to_b; b_to_c ] ] [ Function [ a_to_b ] ])

let () =
  test "extended function arg B"
    (not (is_subtype [ Function [ a_to_b ] ] [ Function [ a_to_b; b_to_c ] ]))

let () =
  test "basic function subtyping A"
    (is_subtype [ Function [ ab_to_c ] ] [ Function [ a_to_bc ] ])

let () =
  test "basic function subtyping B"
    (not (is_subtype [ Function [ a_to_bc ] ] [ Function [ ab_to_c ] ]))

let () =
  test "function arg split A"
    (is_subtype [ Function [ a_to_c; b_to_c ] ] [ Function [ ab_to_c ] ])

let () =
  test "function arg split B"
    (is_subtype [ Function [ ab_to_c ] ] [ Function [ a_to_c; b_to_c ] ])

let () =
  test "large arg split A"
    (is_subtype large_arg_split_subtype large_arg_split_supertype)

let () =
  test "large arg split B"
    (not (is_subtype large_arg_split_supertype large_arg_split_subtype))

(* This potential property is not considered valid, we assume argument types don't have inhabited intersection *)
let () =
  test "invalid function return split A"
    (not (is_subtype [ Function [ a_to_bc; a_to_cd ] ] [ Function [ a_to_c ] ]))

(* But the invrse is true within the system *)
let () =
  test "function return split B"
    (is_subtype [ Function [ a_to_c ] ] [ Function [ a_to_bc; a_to_cd ] ])

(* We have not applied this property, and don't want to. We'd need to have unary argument types to split inthis way *)
let () =
  test "invalid function return split A"
    (not
       (is_subtype
          [ Function [ ([ a_label; b_label ], [ a_label; b_label ]) ] ]
          [
            Function
              [
                ([ a_label; b_label ], [ a_label ]);
                ([ a_label; b_label ], [ b_label ]);
              ];
          ]))

(* But again, the reverse is true, and this is expected *)
let () =
  test "invalid function return split B"
    (is_subtype
       [
         Function
           [
             ([ a_label; b_label ], [ a_label ]);
             ([ a_label; b_label ], [ b_label ]);
           ];
       ]
       [ Function [ ([ a_label; b_label ], [ a_label; b_label ]) ] ])

(* This subtyping relation has also not been applied *)
let () =
  test "invalid fuction arg split A"
    (not
       (is_subtype
          [ Function [ ([ Function [ a_to_b; b_to_c ] ], [ a_label ]) ] ]
          [
            Function [ ([ Function [ a_to_b ] ], [ a_label ]) ];
            Function [ ([ Function [ b_to_c ] ], [ a_label ]) ];
          ]))

(* But the inverse should be true *)
let () =
  test "invalid fuction arg split B"
    (is_subtype
       [
         Function [ ([ Function [ a_to_b ] ], [ a_label ]) ];
         Function [ ([ Function [ b_to_c ] ], [ a_label ]) ];
       ]
       [ Function [ ([ Function [ a_to_b; b_to_c ] ], [ a_label ]) ] ])

let () =
  test "basic application types"
    (get_application_type
       [ Function [ ([ a_label ], [ b_label ]) ] ]
       [ a_label ]
    = Some [ b_label ])

let () =
  test "application against label fails"
    (get_application_type [ a_label ] [ a_label ] = None)

let () =
  test "basic mismatched application"
    (get_application_type
       [ Function [ ([ b_label ], [ b_label ]) ] ]
       [ a_label ]
    = None)

let () =
  test "contravariant function application A"
    (get_application_type
       [ Function [ ([ a_label; b_label ], [ c_label ]) ] ]
       [ a_label ]
    = Some [ c_label ])

let () =
  test "contravariant function application B"
    (get_application_type
       [ Function [ ([ a_label ], [ c_label ]); ([ b_label ], [ d_label ]) ] ]
       [ a_label ]
    = Some [ c_label ])

let () =
  test "union function application A"
    (get_application_type
       [ Function [ ([ a_label; b_label ], [ c_label ]) ] ]
       [ a_label; b_label ]
    = Some [ c_label ])

let () =
  test "union function application B"
    (get_application_type
       [ Function [ ([ a_label ], [ c_label ]); ([ b_label ], [ d_label ]) ] ]
       [ a_label; b_label ]
    = Some [ c_label; d_label ])

let () =
  test "application fails when label in union"
    (get_application_type
       [ a_label; Function [ ([ a_label ], [ b_label ]) ] ]
       [ a_label ]
    = None)

let () =
  test "application fails when not all functios can be applied"
    (get_application_type
       [
         Function [ ([ b_label ], [ a_label ]) ];
         Function [ ([ a_label ], [ b_label ]) ];
       ]
       [ a_label ]
    = None)

let () =
  test "union against union application fails"
    (get_application_type
       [
         Function [ ([ b_label ], [ a_label ]) ];
         Function [ ([ a_label ], [ b_label ]) ];
       ]
       [ a_label; b_label ]
    = None)

let () =
  test "union of functions unions return types"
    (get_application_type
       [
         Function [ ([ a_label ], [ c_label ]) ];
         Function [ ([ a_label ], [ d_label ]) ];
       ]
       [ a_label ]
    = Some [ c_label; d_label ])

let () = print_string (type_to_string large_arg_split_subtype)
let true_label = Label "True"
let false_label = Label "False"
let bool_type = [ true_label; false_label ]
let unary_bool_type = Function [ (bool_type, bool_type) ]
let binary_bool_type = Function [ (bool_type, [ unary_bool_type ]) ]
let tertiary_bool_type = Function [ (bool_type, [ binary_bool_type ]) ]

let not_term =
  Abstraction
    [ ([ true_label ], Const "False"); ([ false_label ], Const "True") ]

let and_term =
  Abstraction
    [
      ( [ true_label ],
        Abstraction
          [ ([ true_label ], Const "True"); ([ false_label ], Const "False") ]
      );
      ([ false_label ], Abstraction [ (bool_type, Const "False") ]);
    ]

let or_term =
  Abstraction
    [
      ([ true_label ], Abstraction [ (bool_type, Const "True") ]);
      ( [ false_label ],
        Abstraction
          [ ([ true_label ], Const "True"); ([ false_label ], Const "False") ]
      );
    ]

let if_bool_term =
  Abstraction
    [
      ( [ true_label ],
        Abstraction [ (bool_type, Abstraction [ (bool_type, Variable 1) ]) ] );
      ( [ false_label ],
        Abstraction [ (bool_type, Abstraction [ (bool_type, Variable 0) ]) ] );
    ]

let not_true = Application (not_term, Const "True")
let not_false = Application (not_term, Const "False")

let apply_bool =
  Abstraction
    [
      ( [ unary_bool_type ],
        Abstraction [ (bool_type, Application (Variable 1, Variable 0)) ] );
    ]

let apply_binary_bool =
  Abstraction
    [
      ( [ binary_bool_type ],
        Abstraction
          [
            ( bool_type,
              Abstraction
                [
                  ( bool_type,
                    Application
                      (Application (Variable 2, Variable 1), Variable 0) );
                ] );
          ] );
    ]

let apply_not = Application (Application (apply_bool, not_term), Const "True")

let apply_and =
  Application
    ( Application (Application (apply_binary_bool, and_term), Const "True"),
      Const "False" )

let apply_or =
  Application
    ( Application (Application (apply_binary_bool, or_term), Const "False"),
      Const "True" )

let apply_not_eval = eval apply_not
let apply_and_eval = eval apply_and
let apply_or_eval = eval apply_or
let not_term_type = Option.get (type_lambda_term not_term)
let not_true_type = Option.get (type_lambda_term not_true)
let not_false_type = Option.get (type_lambda_term not_false)
let apply_bool_type = Option.get (type_lambda_term apply_bool)
let apply_not_type = Option.get (type_lambda_term apply_not)
let and_type = Option.get (type_lambda_term and_term)
let or_type = Option.get (type_lambda_term or_term)
let if_bool_type = Option.get (type_lambda_term if_bool_term)
let apply_binary_type = Option.get (type_lambda_term apply_binary_bool)
let apply_and_type = Option.get (type_lambda_term apply_and)
let apply_or_type = Option.get (type_lambda_term apply_or)
let () = Printf.printf "%s\n" (type_to_string not_term_type)
let () = Printf.printf "%s\n" (type_to_string not_true_type)
let () = Printf.printf "%s\n" (type_to_string not_false_type)
let () = Printf.printf "%s\n" (type_to_string apply_bool_type)
let () = Printf.printf "%s\n" (type_to_string apply_not_type)
let () = Printf.printf "%s\n" (type_to_string and_type)
let () = Printf.printf "%s\n" (type_to_string or_type)
let () = Printf.printf "%s\n" (type_to_string if_bool_type)
let () = Printf.printf "%s\n" (type_to_string apply_and_type)
let () = Printf.printf "%s\n" (type_to_string apply_or_type)
let () = Printf.printf "%s\n" (type_to_string apply_binary_type)
let () = Printf.printf "%s\n" (term_to_string apply_not)
let () = Printf.printf "%s\n" (term_to_string apply_not_eval)
let () = Printf.printf "%s\n" (term_to_string apply_and_eval)
let () = Printf.printf "%s\n" (term_to_string apply_or_eval)
let () = Printf.printf "%b\n" (is_subtype if_bool_type [ tertiary_bool_type ])