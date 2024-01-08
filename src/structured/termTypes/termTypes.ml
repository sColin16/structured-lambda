open Metatypes

type term =
  | Abstraction of (structured_type * term) list
  | Application of term * term
  | Variable of int
  | Const of string
  | UnivQuantifier of term
  | UnivApplication of term * structured_type

and value =
  | Closure of (structured_type * term) list * environment
  | VUnivQuantifier of term
  | VConst of string

and environment = value list
