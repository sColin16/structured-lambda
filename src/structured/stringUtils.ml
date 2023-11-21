open Type
open Term

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
  else Printf.sprintf "Ind:%i->%s" num (flat_union_type_to_string def.flat_union)

and flat_union_type_to_string (flat_union : flat_union_type) =
  let union_type =
    List.map
      (fun flat_base ->
        match flat_base with
        | FLabel a -> Label a
        | FIntersection functions -> Intersection functions)
      flat_union
  in
  union_type_to_string union_type

and base_type_to_string (base_type : base_type) =
  match base_type with
  | Label name -> name
  | Intersection func_list ->
      Printf.sprintf "{%s}" (func_type_to_string func_list)
  | TypeVar n -> Printf.sprintf "R(%i)" n

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
  | Fix term ->
      let inner_string = term_to_string term in
      Printf.sprintf "Fix(%s)" inner_string

and branch_to_string (branch_type, branch_body) =
  Printf.sprintf "%s:%s"
    (type_to_string branch_type)
    (term_to_string branch_body)
