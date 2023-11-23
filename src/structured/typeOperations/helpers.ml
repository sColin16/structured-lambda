open Metatypes

let build_structured_type (union : union_type) (context : recursive_context) =
  { union; context }

let build_recursive_def (kind : recursive_kind) (flat_union : flat_union_type) :
    recursive_def =
  { kind; flat_union }

let build_recursive_context (defs : (recursive_kind * flat_union_type) list) :
    recursive_context =
  List.map (fun (kind, union) -> build_recursive_def kind union) defs

let extract_first (list : ('a * 'b) list) =
  List.map (fun (first, _) -> first) list

let extract_second (list : ('a * 'b) list) =
  List.map (fun (_, second) -> second) list

(* TODO: remove duplicate and subtypes from the union after flattening *)
let extract_composite_args (branches : unary_function list) =
  List.flatten (extract_first branches)

let extract_composite_return (branches : unary_function list) =
  List.flatten (extract_second branches)

(* TODO: consider just accepting a structured type here *)
let flatten_union (union : union_type) (context : recursive_context) :
    flat_union_type =
  List.flatten
    (List.map
       (fun base_type ->
         match base_type with
         | Label a -> [ FLabel a ]
         | Intersection a -> [ FIntersection a ]
         | TypeVar n -> (List.nth context n).flat_union)
       union)

(* TODO: consider just accepted a structured type here *)
let flatten_union_contractive (union : union_type) (context : recursive_context)
    =
  let flat_union = flatten_union union context in
  let converted_union =
    List.map
      (fun base_type ->
        match base_type with
        | FLabel a -> Label a
        | FIntersection functions -> Intersection functions)
      flat_union
  in
  build_structured_type converted_union context

let expand_type_var_contractive (var_num : int) (context : recursive_context) =
  let flat_union = (List.nth context var_num).flat_union in
  let converted_union =
    List.map
      (fun base_type ->
        match base_type with
        | FLabel a -> Label a
        | FIntersection a -> Intersection a)
      flat_union
  in
  build_structured_type converted_union context
