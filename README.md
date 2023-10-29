# Structured Lambda {λ}
A structurally-typed lambda calculus that serves as a basis for
structurally-typed functional languages

## Overview
Structured Lambda is a simply-typed lambda calculus, augmented with the following features:
- Arbitrary constants with corresponding singleton types
- Union types
- Ad-hoc polymorphic functions (corresponding to intersections of unary function types)
- Subtyping
- General recursion

Structured Lambda's differentiating feature is its structural type system, which allows
is to directly and umambiguously represent a wide range of common language constructs,
all while providing a set-theoretic subtyping sytem that is intuitive to use and accepts
a huge range of correctly typed programs

Here are some of the language constructs Structured Lambda can represent:
- Booleans
- Enums
- Sum types
- Product types
- Nominative types
- Tuples
- Records
  - Including records with optional fields
- Integers/strings in a finite capacity
- Functions
  - Including overloaded functions (ad-hoc polymorphism)
- Classes

Unlike most simply-typed lambda calculi that represent sum and product types as
first-class language constructs, Structured Lambda defines more foundational types
from which sum and product types can be defined. Whereas sum and product types are
typically nominative in nature, the more foundational types that Structured Lambda
provides allows sum and product types to be structurally typed. This means that
product types like record types have the expected width and depth subtyping from
their representation as the intersection of function types. It also mean that sum
types like option types have subtyping relationships with their components due to
the nature of union types. The non-optional type is a subtype of the optional
version of that same type.

## Features on the Roadmap
- AST's that support named terms, instead of De Bruijn encodings of terms
- Lexer/Parser to support writing programs outside of the embedded context of OCaml's language
- Let constructs to enable more intuitively expressive programs
  - These simply provide syntactic sugar over abstractions
- Recursive types to enable representations of truely infinite types, like integers and strings
  functions, while maintaining the integrity of the type system
- Universal type quantification to enable parametric polymorphism (aka "Generics")
  - Bounded quantification to assert properties of the quantified type
- Existential type quantification to enable ML-style modules
- Type ascription to abstract details of a type away and support information hiding
- Type-level programming, including type aliases for more expressiveness surrounding types
- Effect systems to augment the type system and express when exceptions are
  thrown or impure operations occur
- Type inference to avoid the requirement for type annotations everywhere

## Inspiration
Structured Lambda is inspired by TypeScript's structural type system, which includes union,
intersection, and literal types. In fact, Structured Lambda was born from an attempt
to formalize the sorts of type constructs that TypeScript provides

## Open Questions
- How to efficiently implement the type-based branching of lambda terms. It is similar
  in nature to pattern matching, but the expressivness of the type system adds complexity
  and opens questions abot the extent to which a value can be introspected to determine
  a more specific type, especially in the context of impure computation
- What sorts type inference are possible and how do they interact with advanced language
  constructs. Is a full type inference ala Hindley-Milner possibe? Would such type inference
  require universal quantification type contructs? Or would universal type constructs interfere
  with such type inference? Would bidirectional type inference be possible? Would that eliminate
  the need for universal quantification or be compatible with it? How would we identify where
  type annotations are required in such a case?
