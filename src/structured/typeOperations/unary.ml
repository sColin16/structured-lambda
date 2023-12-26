open Helpers
open Create
open Metatypes

module TypeVarSet = Set.Make (struct
  type t = int

  let compare = compare
end)

(** [is_unary union_type] determines if a type cannot be written as the union of two distinct, unrelated types *)
let rec is_unary (t : structured_type) = is_unary_rec t TypeVarSet.empty

and is_unary_rec (t : structured_type) (encountered_type_vars : TypeVarSet.t) =
  let type_var_num =
    if List.length t.union = 1 then
      match List.hd t.union with RecTypeVar n -> Some n | _ -> None
    else None
  in
  let is_type_var = Option.is_some type_var_num in
  let loop_encountered =
    is_type_var
    && TypeVarSet.mem (Option.get type_var_num) encountered_type_vars
  in
  (* If we encounter a type variable loop, then we can assume it is unary, barring evidence along other branches *)
  if loop_encountered then true
  else
    (* Add the type variable to the set to track the next loops, if applicable *)
    let new_encountered_vars =
      if is_type_var then
        TypeVarSet.add (Option.get type_var_num) encountered_type_vars
      else encountered_type_vars
    in
    let flat_union = flatten_union t.union t.context in
    match flat_union with
    (* Under the rewriting equality definition, the empty type is considered "unary" even though it's really more nullary *)
    | [] -> true
    (* A single type in a union is considered unary if the corresponding base type is *)
    | [ base ] -> (
        match base with
        (* Labels are unary be definition *)
        | FLabel _ -> true
        (* Functions are unary if all their argument and return types are unary *)
        | FIntersection functions ->
            List.for_all
              (fun (arg, return) ->
                is_unary_rec
                  (build_structured_type arg t.context)
                  new_encountered_vars
                && is_unary_rec
                     (build_structured_type return t.context)
                     new_encountered_vars)
              functions)
    (* A multiple type union is not considered unary. In theory it may be possible to rewrite as a single base type
       but we can do that later *)
    | _ :: _ -> false
