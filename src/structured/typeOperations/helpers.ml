open Metatypes

let extract_first (list : ('a * 'b) list) =
  List.map (fun (first, _) -> first) list

let extract_second (list : ('a * 'b) list) =
  List.map (fun (_, second) -> second) list

(* TODO: remove duplicate and subtypes from the union after flattening *)
let extract_composite_args (branches : unary_function list) =
  List.flatten (extract_first branches)

let extract_composite_return (branches : unary_function list) =
  List.flatten (extract_second branches)

let get_type_from_context (var_num : int) (context : recursive_context) =
  List.nth context var_num

let flatten_base (context : recursive_context) (base_type : base_type) :
    flat_union_type =
  match base_type with
  | Label a -> [ FLabel a ]
  | Intersection a -> [ FIntersection a ]
  | TypeVar n -> (get_type_from_context n context).flat_union

let flatten_union (union : union_type) (context : recursive_context) :
    flat_union_type =
  List.flatten (List.map (flatten_base context) union)

let unflatten_base (flat_base : flat_base_type) : base_type =
  match flat_base with FLabel a -> Label a | FIntersection a -> Intersection a

let unflatten_union (flat_union : flat_union_type) : union_type =
  List.map unflatten_base flat_union

(** Converts a union to a union that contains no type vars, while maintaining the union_type *)
let to_contractive_union (union : union_type) (context : recursive_context) =
  let flat_union = flatten_union union context in
  unflatten_union flat_union

(* Expands a type variable into a contractive union type (no type variables in the union) *)
let expand_type_var_to_union (var_num : int) (context : recursive_context) =
  let flat_union = (get_type_from_context var_num context).flat_union in
  unflatten_union flat_union
