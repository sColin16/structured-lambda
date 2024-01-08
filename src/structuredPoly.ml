open Structured.Metatypes
open Structured.TermTypes
open Structured.TypeOperations.Create
open StructuredHelpers

let name_label = get_typed_term_unsafe (Const "Name")
let val_label = get_typed_term_unsafe (Const "Val")
let next_label = get_typed_term_unsafe (Const "Next")
let nil_label = get_typed_term_unsafe (Const "Nil")
let cons_label = get_typed_term_unsafe (Const "Cons")

let polymoprhic_identity =
  get_typed_term_unsafe
    (UnivQuantifier
       (Abstraction [ (base_to_structured_type (UnivTypeVar 0), Variable 0) ]))

let polymorphic_double =
  get_typed_term_unsafe
    (UnivQuantifier
       (Abstraction
          [
            ( func_to_structured_type ([ UnivTypeVar 0 ], [ UnivTypeVar 0 ]),
              Abstraction
                [
                  ( base_to_structured_type (UnivTypeVar 0),
                    Application
                      (Variable 1, Application (Variable 1, Variable 0)) );
                ] );
          ]))

let polymorphic_quadruple =
  get_typed_term_unsafe
    (UnivQuantifier
       (Application
          ( UnivApplication
              ( polymorphic_double.term,
                func_to_structured_type ([ UnivTypeVar 0 ], [ UnivTypeVar 0 ])
              ),
            UnivApplication
              (polymorphic_double.term, base_to_structured_type (UnivTypeVar 0))
          )))

let ind_poly_list_union = [ UnivQuantification [ RecTypeVar 0 ] ]

let ind_poly_list_context =
  [
    ( Inductive,
      [
        FIntersection [ (name_label.stype.union, nil_label.stype.union) ];
        FIntersection
          [
            (name_label.stype.union, cons_label.stype.union);
            (val_label.stype.union, [ UnivTypeVar 0 ]);
            (next_label.stype.union, [ RecTypeVar 0 ]);
          ];
      ] );
  ]

(* Serves as a "higher-kinded" type for polymorphic lists*)
(* TODO: accept a structured type so that the element type can be recursive *)
let build_ind_list (elt_type : union_type) =
  let union_type = [ RecTypeVar 0 ] in
  let context =
    [
      ( Inductive,
        [
          FIntersection [ (name_label.stype.union, nil_label.stype.union) ];
          FIntersection
            [
              (name_label.stype.union, cons_label.stype.union);
              (val_label.stype.union, elt_type);
              (next_label.stype.union, [ RecTypeVar 0 ]);
            ];
        ] );
    ]
  in
  build_structured_type union_type (build_recursive_context context)

let ind_poly_list_type =
  build_structured_type ind_poly_list_union
    (build_recursive_context ind_poly_list_context)

let poly_nil =
  get_typed_term_unsafe
    (UnivQuantifier (Abstraction [ (name_label.stype, nil_label.term) ]))

let poly_cons =
  get_typed_term_unsafe
    (UnivQuantifier
       (Abstraction
          [
            ( base_to_structured_type (UnivTypeVar 0),
              Abstraction
                [
                  ( build_ind_list [ UnivTypeVar 0 ],
                    Abstraction
                      [
                        (name_label.stype, cons_label.term);
                        (val_label.stype, Variable 2);
                        (next_label.stype, Variable 1);
                      ] );
                ] );
          ]))
