type 'a union = 'a list
type 'a intersection = 'a list

type structured_type = { union : union_type; context : recursive_context }
and union_type = base_type list

and base_type =
  | Label of string
  | Intersection of unary_function list
  | TypeVar of int

and unary_function = union_type * union_type
and recursive_context = recursive_def list
and flat_union_type = flat_base_type list
and flat_base_type = FLabel of string | FIntersection of unary_function list
and recursive_def = { kind : recursive_kind; flat_union : flat_union_type }
and recursive_kind = Inductive | Coinductive

(* TODO: consider requiring that inductive types are indeed well-founded, at least at this level of abstraction *)
(* TODO: consider requiring that recursive types are non-empty lists *)

module TypeVarUnionSet = Set.Make (struct
  type t = int * union_type

  let compare = compare
end)
