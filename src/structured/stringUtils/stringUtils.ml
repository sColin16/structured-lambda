open Metatypes
open TermTypes

let rec type_to_string (t : structured_type) =
  Printf.sprintf "%s with %s"
    (union_type_to_string t.union)
    (recursive_context_to_string t.context)

and union_type_to_string (union_type : union_type) =
  let base_type_strings = List.map base_type_to_string union_type in
  Printf.sprintf "(%s)" (String.concat "|" base_type_strings)

and recursive_context_to_string (recursive_context : recursive_context) =
  let mapping_strings =
    List.mapi (fun idx def -> recursive_def_to_string idx def) recursive_context
  in
  Printf.sprintf "{%s}" (String.concat "," mapping_strings)

and recursive_def_to_string (num : int) (def : recursive_def) =
  if def.kind = Coinductive then
    Printf.sprintf "Coind:%i->%s" num (flat_union_type_to_string def.flat_union)
  else
    Printf.sprintf "Ind:%i->%s" num (flat_union_type_to_string def.flat_union)

and flat_union_type_to_string (flat_union : flat_union_type) =
  let union_type =
    List.map
      (function
        | FLabel a -> Label a
        | FIntersection functions -> Intersection functions
        | FUnivTypeVar a -> UnivTypeVar a
        | FUnivQuantification a -> UnivQuantification a)
      flat_union
  in
  union_type_to_string union_type

and base_type_to_string (base_type : base_type) =
  match base_type with
  | Label name -> name
  | Intersection func_list ->
      Printf.sprintf "{%s}" (func_type_to_string func_list)
  | RecTypeVar n -> Printf.sprintf "R(%i)" n
  | UnivTypeVar n -> Printf.sprintf "U(%i)" n
  | UnivQuantification t ->
      Printf.sprintf "forall.(%s)" (union_type_to_string t)

and func_type_to_string (func_list : unary_function list) =
  String.concat "," (List.map unary_func_type_to_string func_list)

and unary_func_type_to_string ((arg, return) : unary_function) =
  Printf.sprintf "%s->%s" (union_type_to_string arg)
    (union_type_to_string return)

let rec term_to_string (term : term) =
  match term with
  | Const name -> name
  | Variable var_num -> Printf.sprintf "%i" var_num
  | Abstraction branches ->
      let branch_strings = List.map branch_to_string branches in
      Printf.sprintf "\\.{%s}" (String.concat "," branch_strings)
  | Application (t1, t2) ->
      Printf.sprintf "(%s) (%s)" (term_to_string t1) (term_to_string t2)
  | TypeAbstraction inner_term ->
      Printf.sprintf "\\T.{%s}" (term_to_string inner_term)
  | TypeApplication (inner_term, inner_type) ->
      Printf.sprintf "(%s) [%s]" (term_to_string inner_term) (type_to_string inner_type)

and branch_to_string (branch_type, branch_body) =
  Printf.sprintf "%s:%s"
    (type_to_string branch_type)
    (term_to_string branch_body)
