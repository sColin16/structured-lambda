open Metatypes
open Context
open Create

(* Would it be useful to have a pairwise union that the list version uses? *)

(** Constructs a new type that is the union of the given list of types *)
let get_type_union (types : structured_type list) : structured_type =
  let union_type, recursive_context =
    (* Join each union and context pairwise via fold *)
    List.fold_left
      (fun (acc_union_type, acc_recursive_context) next_type ->
        (* Get the next type in the accumulated context to obtain the joined context
           and the next type in the context of that new accumulated context *)
        let new_type = get_type_in_context next_type acc_recursive_context in
        (* Append this union to the accumulated union, use the new context from above *)
        (acc_union_type @ new_type.union, new_type.context))
      ([], []) types
  in
  (* Finally, construct the type from the accumulated union and context *)
  build_structured_type union_type recursive_context
