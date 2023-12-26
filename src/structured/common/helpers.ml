let list_product (list1 : 'a list) (list2 : 'b list) =
  List.flatten (List.map (fun x1 -> List.map (fun x2 -> (x1, x2)) list2) list1)

(** Gets all pairs of items in the list, not in any paticular order, excluding pairs with the same index *)
let self_pairs (list : 'a list) =
  let pair_list =
    List.flatten
      (List.mapi
         (fun idx1 x1 -> List.mapi (fun idx2 x2 -> (idx2 > idx1, x1, x2)) list)
         list)
  in
  List.filter_map
    (fun (should_include, x1, x2) ->
      if should_include then Some (x1, x2) else None)
    pair_list

let flat_map_opt2 (func : 'a -> 'b -> 'c option) (opta : 'a option)
    (optb : 'b option) =
  match (opta, optb) with
  | None, _ | _, None -> None
  | Some a, Some b -> func a b

let map_opt2 (func : 'a -> 'b -> 'c) (opta : 'a option) (optb : 'b option) =
  flat_map_opt2 (fun a b -> Some (func a b)) opta optb

let opt_list_to_list_opt (input : 'a option list) : 'a list option =
  let list_opt =
    List.fold_left
      (fun acc elt_opt -> map_opt2 List.cons elt_opt acc)
      (Some []) input
  in
  (* Reverse the list to maintain the order. Shouldn't really matter, but oh well *)
  Option.map List.rev list_opt

type 'a tuple = 'a list

let rec multi_list_product (nested_list: 'a list tuple): 'a tuple list =
  let rec helper (acc: 'a tuple list) (l1: 'a list) (l2: 'a list tuple) =
    match l1, l2 with
    | [], _ | _, [] -> acc
    | h1::t1, h2::t2 ->
      let acc = (h1::h2)::acc in
      let acc = helper acc t1 l2 in
      helper acc [ h1 ] t2
  in match nested_list with
  | [] -> []
  | [l1] -> List.map (fun x -> [x]) l1
  | l1::tail ->
    let tail_product = multi_list_product tail in
    helper [] l1 tail_product

let short_circuit_and (exp1: unit -> bool) (exp2: unit -> bool) =
  if exp1 () then exp2 () else false

let short_circuit_or (exp1: unit -> bool) (exp2: unit -> bool) =
  if exp1() then true else exp2 ()
