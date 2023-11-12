open Structured

type typed_term = { term : term; stype : structured_type }

let build_typed_term (term : term) (stype : structured_type) = { term; stype }
let get_type_unsafe term = Option.get (get_type term)
let get_typed_term_unsafe term = build_typed_term term (get_type_unsafe term)

let get_type_union (types : structured_type list) : structured_type =
  let union_type, recursive_context =
    List.fold_left
      (fun (acc_union_type, acc_recursive_context) next_type ->
        let new_type = get_type_in_context next_type acc_recursive_context in
        (acc_union_type @ new_type.union, new_type.context))
      ([], []) types
  in
  build_structured_type union_type recursive_context

let union_to_structured_type (union_type : union_type) =
  build_structured_type union_type []

let base_to_structured_type (base_type : base_type) =
  union_to_structured_type [ base_type ]

let func_to_structured_type (unary_function : unary_function) =
  base_to_structured_type (Intersection [ unary_function ])

let label_to_structured_type (label : string) =
  base_to_structured_type (Label label)

let get_type_intersection (types : structured_type list) : structured_type =
  let intersection =
    List.fold_left
      (fun acc_intersection next_type ->
        match next_type.union with
        | [ Intersection functions ] -> acc_intersection @ functions
        | _ -> raise (invalid_arg "a type wasn't just an intersection"))
      [] types
  in
  base_to_structured_type (Intersection intersection)
