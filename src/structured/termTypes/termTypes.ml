open Metatypes

type term =
  | Abstraction of (structured_type * term) list
  | Application of term * term
  | Variable of int
  | Const of string
  | Fix of term
  | TypeAbstraction of term
  | TypeApplication of term * structured_type
