open Metatypes

type term =
  | Abstraction of (structured_type * term) list
  | Application of term * term
  | Variable of int
  | Const of string
  | TypeAbstraction of term
  | TypeApplication of term * structured_type

and value =
  | Closure of (structured_type * term) list * environment
  | VConst of string

and environment = value list
