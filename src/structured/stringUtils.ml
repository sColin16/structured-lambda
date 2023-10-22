open Type
open Term

let rec type_to_string (lambda_type : structured_type) =
  Printf.sprintf "(%s)"
    (String.concat "|" (List.map base_type_to_string lambda_type))

and base_type_to_string (base_type : base_type) =
  match base_type with
  | Label name -> name
  | Function func_list -> Printf.sprintf "{%s}" (func_type_to_string func_list)

and func_type_to_string (func_list : unary_function list) =
  String.concat "," (List.map unary_func_type_to_string func_list)

and unary_func_type_to_string ((arg, return) : unary_function) =
  Printf.sprintf "%s->%s" (type_to_string arg) (type_to_string return)

let rec term_to_string (term : term) =
  match term with
  | Const name -> name
  | Variable var_num -> Printf.sprintf "%i" var_num
  | Abstraction branches ->
      let branch_strings = List.map branch_to_string branches in
      Printf.sprintf "\\.{%s}" (String.concat "," branch_strings)
  | Application (t1, t2) ->
      Printf.sprintf "(%s) (%s)" (term_to_string t1) (term_to_string t2)
  | FixAbs branches ->
    let branc_strings = List.map branch_to_string branches in
    Printf.sprintf "\\rec.{%s}" (String.concat "," branc_strings)

and branch_to_string (branch_type, branch_body) =
  Printf.sprintf "%s:%s"
    (type_to_string branch_type)
    (term_to_string branch_body)
