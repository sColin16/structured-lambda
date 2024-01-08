open TermTypes
open Metatypes

(* Converts a value into an equivalent term, resolving all the free variables in
   closures into direct abstractions. We use this as a simple way to resolve
   the branch to execute during an application. There may be alternatives *)
let rec value_to_term (value : value) : term =
  match value with
  (* Constants can be translated directly *)
  | VConst label -> Const label
  (* Universal quantification can be translated directly *)
  | VUnivQuantifier inner_term -> UnivQuantifier inner_term
  (* The bodies of closures are converted using the closure's environment *)
  | Closure (branches, env) ->
      let converted_branches =
        List.map (substitute_abstraction_branch env 1) branches
      in
      Abstraction converted_branches

and substitute_abstraction_branch (env : environment) (depth : int)
    ((arg_type, body) : structured_type * term) =
  (* Perform the substitution on the branch of abstraction, but leave the type the same *)
  let substituted_body = substitute_in_term body env depth in
  (arg_type, substituted_body)

and substitute_in_term (term : term) (env : environment) (depth : int) =
  match term with
  (* Constants are converted directly*)
  | Const label -> Const label
  (* Abstractions must have their branches substituted, at the next depth down *)
  | Abstraction branches ->
      let substituted_branches =
        List.map (substitute_abstraction_branch env (depth + 1)) branches
      in
      Abstraction substituted_branches
  (* Applications are substituted recursively *)
  | Application (left_term, right_term) ->
      Application
        ( substitute_in_term left_term env depth,
          substitute_in_term right_term env depth)
  (* If a variable references a free variable, we pull it from the env, otherwise, leave it
     because it references a bound variable within this abstraction *)
  | Variable num ->
      if num - depth < 0 then Variable num
      else value_to_term (List.nth env (num - depth))
  (* Universal quantifiers are substituted recursively *)
  | UnivQuantifier inner_term ->
    UnivQuantifier (substitute_in_term inner_term env depth)
  (* Universal application requires a substitution in the term, but leaves the type the same *)
  | UnivApplication (inner_term, inner_type) ->
    UnivApplication
    ( substitute_in_term inner_term env depth,
      inner_type)
