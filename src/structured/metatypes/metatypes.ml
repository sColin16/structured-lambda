type 'a union = 'a list
type 'a intersection = 'a list

type structured_type = { union : union_type; context : recursive_context }
and union_type = base_type list

and base_type =
  | Label of string
  | Intersection of unary_function list
  | RecTypeVar of int
  (* TODO: could these be part of an intersection type when subtypes exist? *)
  | UnivTypeVar of int
  (* TODO: should this have intersection abilities with bounded quantification? Like Base applications? *)
  | UnivQuantification of union_type

and unary_function = union_type * union_type
and recursive_context = recursive_def list
and flat_union_type = flat_base_type list

(* TODO: maybe this should be called contractive instead of flat? *)
and flat_base_type =
  | FLabel of string
  | FIntersection of unary_function list
  | FUnivTypeVar of int
  | FUnivQuantification of union_type

and recursive_def = { kind : recursive_kind; flat_union : flat_union_type }
and recursive_kind = Inductive | Coinductive

(* TODO: consider requiring that recursive types are non-empty lists *)

module TypeVarUnionSet = Set.Make (struct
  type t = int * union_type

  let compare = compare
end)
