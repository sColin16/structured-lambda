open Metatypes
open Helpers
open WellFounded

let build_structured_type (union : union_type) (context : recursive_context) =
  { union; context }

let build_recursive_def (kind : recursive_kind) (flat_union : flat_union_type) :
    recursive_def =
  { kind; flat_union }

(* TODO: check that the context has well-founded inductive types here? *)
let build_recursive_context (defs : (recursive_kind * flat_union_type) list) :
    recursive_context =
  let context = List.map (fun (kind, union) -> build_recursive_def kind union) defs in
  let valid_well_founded = is_valid_well_founded_context context in
  if valid_well_founded then context else raise (Invalid_argument "Context was not properly well-founded")

let expand_type_var (var_num : int) (context : recursive_context) =
  build_structured_type (expand_type_var_to_union var_num context) context

let to_contractive_type (union: union_type) (context: recursive_context) =
  build_structured_type (to_contractive_union union context) context
