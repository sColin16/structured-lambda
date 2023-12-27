open Structured.Metatypes
open Structured.TermTypes
open Structured.TypeOperations.Context
open Structured.TypeOperations.Create
open Structured.TermOperations.Typing

type typed_term = { term : term; stype : structured_type }

let build_typed_term (term : term) (stype : structured_type) = { term; stype }
let get_type_unsafe term = Option.get (get_type term)
let get_typed_term_unsafe term = build_typed_term term (get_type_unsafe term)

let get_type_union (types : structured_type list) : structured_type =
  let union_type, recursive_context =
    List.fold_left
      (fun (acc_union_type, acc_recursive_context) next_type ->
        let new_type = get_type_in_context next_type acc_recursive_context in
        (acc_union_type @ new_type.union, new_type.context))
      ([], []) types
  in
  build_structured_type union_type recursive_context

let union_to_structured_type (union_type : union_type) =
  build_structured_type union_type []

let base_to_structured_type (base_type : base_type) =
  union_to_structured_type [ base_type ]

let func_to_structured_type (unary_function : unary_function) =
  base_to_structured_type (Intersection [ unary_function ])

let label_to_structured_type (label : string) =
  base_to_structured_type (Label label)

let get_type_intersection (types : structured_type list) : structured_type =
  let intersection =
    List.fold_left
      (fun acc_intersection next_type ->
        match next_type.union with
        | [ Intersection functions ] -> acc_intersection @ functions
        | _ -> raise (invalid_arg "a type wasn't just an intersection"))
      [] types
  in
  base_to_structured_type (Intersection intersection)

let get_flat_union_type (union_types : structured_type list) : flat_union_type =
  let union_type = get_type_union union_types in
  List.map
    (fun base_type ->
      match base_type with
      | Label a -> FLabel a
      | Intersection a -> FIntersection a
      | _ -> raise (Invalid_argument "got non-flat type"))
    union_type.union

(* Constructs the Z-combinator for a function of a given type, a fixed-point
    combinator for call-by-value semantics *)
let build_fix (arg_type : union_type) (return_type : union_type) =
  let func_type = (func_to_structured_type (arg_type, return_type)).union in
  let fix_context =
    build_recursive_context
      [ (Coinductive, [ FIntersection [ ([ TypeVar 0 ], func_type) ] ]) ]
  in
  let fix =
    get_typed_term_unsafe
      (Abstraction
         [
           ( func_to_structured_type (func_type, func_type),
             Application
               ( Abstraction
                   [
                     ( build_structured_type [ TypeVar 0 ] fix_context,
                       Application
                         ( Variable 1,
                           Abstraction
                             [
                               ( union_to_structured_type arg_type,
                                 Application
                                   ( Application (Variable 1, Variable 1),
                                     Variable 0 ) );
                             ] ) );
                   ],
                 Abstraction
                   [
                     ( build_structured_type [ TypeVar 0 ] fix_context,
                       Application
                         ( Variable 1,
                           Abstraction
                             [
                               ( union_to_structured_type arg_type,
                                 Application
                                   ( Application (Variable 1, Variable 1),
                                     Variable 0 ) );
                             ] ) );
                   ] ) );
         ])
  in
  fix

(* Fixes a provided abstraction with the given arg and return type *)
let fix (arg_type : union_type) (return_type : union_type) (term : term) =
  let fix_term = build_fix arg_type return_type in
  Application (fix_term.term, term)
