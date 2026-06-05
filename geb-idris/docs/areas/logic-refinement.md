# Logic, refinement, effects, and language assembly

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Purpose](#purpose)
- [Mathematical context](#mathematical-context)
- [Modules](#modules)
- [Dependencies](#dependencies)
- [Pointers](#pointers)

<!-- END doctoc -->

## Purpose

This area collects the logic, refinement-type, effect, and
embedded-language explorations of the Idris-2 predecessor
implementation, together with the umbrella module that draws its
constituent layers into a single importable surface. The material
runs from the ground-level atom sort (the leaves of Geb
s-expressions) through quotient types, finite refinement types,
refined algebraic data types, and placeholder logic, effect, and
embedded-language layers. Like the rest of the Idris codebase it is
early exploratory architecture, largely superseded by the Lean
continuation under `geb-lean/`; several of its modules remain stubs.

## Mathematical context

The area spans several standard mathematical concepts adapted for
Idris 2.

*Quotient types* (`QType`): a quotient type is a type together with
a proof-relevant equivalence relation (`PrEquivRel`); morphisms must
preserve the relation. The impredicative coequalizer `impredCoeq` is
the Church-encoding analogue of the set-theoretic coequalizer,
following the standard impredicative encoding of colimits in type
theory (Hofmann, *Extensional Concepts in Intensional Type Theory*,
§4). The self-internalization (`QTypeQT`) makes the universe of
quotient types itself a quotient type.

*Refinement types over finite domains* (`RQFin`): the module presents
finite sets equipped with explicit refinements (equalizers) and
quotients (coequalizers) within a Lawvere-theory-style categorical
framework. Morphism types are represented as slice objects over
product monads, following the presentation of spans as a category of
relations (Benabou, *Les distributeurs*, §1).

*Polynomial and refinement ADTs* (`RefinedADT`): polynomial
endofunctors on a skeleton of `FinSet` are represented as arenas
(`FSArena`, `Arena`, `CArena`) paired with direction maps; lenses are
the morphisms between arenas (Spivak, *Polynomial Functors: A General
Theory of Interaction*, §2). The module extends this through zeroth-
and higher-order ADTs, substitution categories, and refined
expression categories, exploring a substrate for a Geb type
language.

*Atoms* (`Atom`): a three-layer enumerated sort (core atoms,
language atoms, implementation atoms) whose decidable equality,
ordering, and string representation are implemented manually, as
Idris 2 has no built-in enum-deriving mechanism.

*Computational effects* and *embedded language*: both modules are
stubs — reserved extension points for the algebraic-effects layer
and the embedded-language layer respectively; their content is
anticipated but not yet present.

## Modules

- [`src/LanguageDef/Logic.idr`](../../src/LanguageDef/Logic.idr)
  — placeholder module for propositional and predicate logic
  support; it imports `LanguageDef.Metaprogramming` and declares
  no independent definitions at present. Its role is to provide
  the eventual logic substrate (propositional connectives,
  predicate-logic quantifiers) for the Geb language layer.
  The eventual logic substrate would follow the standard
  Curry–Howard correspondence and the internal logic of a topos
  (Johnstone, *Sketches of an Elephant*, vol. I, §1.1).

- [`src/LanguageDef/QType.idr`](../../src/LanguageDef/QType.idr)
  — quotient types as pairs of a carrier type and a
  proof-relevant equivalence relation, with the impredicative
  coequalizer construction and pushout specialization.
  `QType` packages a type with a `PrEquivRel`; `QMorph` carries
  a function with a proof of relation preservation; `impredCoeq`
  is the Church-encoded coequalizer; and `QTypeQT` makes `QType`
  itself a quotient type via `QTEquiv`.
  Impredicative coequalizers are standard in intensional type theory;
  nearest reference is Hofmann, *Extensional Concepts in Intensional
  Type Theory*, §4, and nLab
  [quotient type](https://ncatlab.org/nlab/show/quotient+type).

- [`src/LanguageDef/RQFin.idr`](../../src/LanguageDef/RQFin.idr)
  — finite sets with explicit refinements (equalizers) and
  quotients (coequalizers), presented as a Lawvere-theory-style
  categorical framework over types and morphisms as slice objects.
  `MorType` represents morphisms as slice objects over product
  monads; `ObjMorType` bundles object and morphism types; and
  `RQTermObj` is the (free) terminal object. The module imports
  `QType` and `InternalCat` to build the categorical infrastructure
  of finite-set refinements.
  Equalizers and coequalizers in finite-set categories are standard
  (Mac Lane, *Categories for the Working Mathematician*, §V.2); the
  Lawvere-theory framing follows Lawvere, *Functorial Semantics of
  Algebraic Theories*.

- [`src/LanguageDef/RefinedADT.idr`](../../src/LanguageDef/RefinedADT.idr)
  — polynomial endofunctors and their arenas on a skeleton of
  `FinSet`, extended to dependent polynomial functors, zeroth-
  and higher-order ADTs, substitution categories, and refined
  expression categories. `FSArena` is the list-of-directions
  representation of a polynomial; `Arena`/`Lens` are the
  standard covariant polynomial arena and its lenses
  (morphisms); `RefinedExpCategory_Obj` packages a refined
  expression category object.
  Arenas and lenses as polynomial functors and their natural
  transformations follow Spivak, *Polynomial Functors: A General
  Theory of Interaction*, §2, and Kock, *Polynomial Functors and
  Trees*; the ADT / substitution layers are standard (nLab,
  [polynomial functor](https://ncatlab.org/nlab/show/polynomial+functor)).

- [`src/LanguageDef/Atom.idr`](../../src/LanguageDef/Atom.idr)
  — the three-layer enumerated atom sort used in Geb
  s-expressions, together with its decidable equality, ordering,
  and string representation. `CoreAtom` carries the atoms
  reserved for the core logic; `LangAtom` those reserved for
  language-level definitions; `ImplAtom` the implementation
  atoms bounded by `IMPL_ATOM_SZ`; and `SyntaxAtom` is their
  coproduct. `OldAtom` is a legacy 32-element enumeration with a
  manually written `VectDecoder`/`NatEncoder` pair.
  Enumerated atom sorts with decidable equality are standard
  (Pierce, *Types and Programming Languages*, §11); the
  `VectDecoder`/`FinDecEncoding` infrastructure reuses
  `Library.IdrisUtils` combinators.

- [`src/LanguageDef/ComputationalEffects.idr`](../../src/LanguageDef/ComputationalEffects.idr)
  — placeholder module for the algebraic-effects layer; it
  imports `LanguageDef.Logic` and declares no independent
  definitions at present. Its role is to provide the eventual
  treatment of computational effects (state, exceptions,
  nondeterminism) for the Geb language.
  Algebraic effects and effect handlers are a standard topic
  (Plotkin–Power, *Algebraic Operations and Generic Effects*,
  MSCS 2004; nLab,
  [algebraic effect](https://ncatlab.org/nlab/show/algebraic+effect)).

- [`src/LanguageDef/Embedded.idr`](../../src/LanguageDef/Embedded.idr)
  — placeholder module for the embedded-language layer; it
  imports `LanguageDef.ComputationalEffects` and declares no
  independent definitions at present. Its role is to provide the
  eventual mechanism for specifying languages embedded within
  Geb's core.
  Embedded languages and object/meta-language separation are
  standard (Reynolds, *Definitional Interpreters for Higher-Order
  Programming Languages*, 1972).

- [`src/LanguageDef/FullLanguageDef.idr`](../../src/LanguageDef/FullLanguageDef.idr)
  — the assembly capstone that re-exports all language layers
  as a single surface. It imports `RefinedADT`,
  `UniversalCategory`, `Interpretation`, `Syntax`, `Expression`,
  `Metaprogramming`, `Logic`, `ComputationalEffects`, and
  `Embedded`, and declares no independent definitions; it is the
  single module that downstream consumers (in particular
  `Library.CategoryTheory`) import to obtain the entire
  language definition.
  The module contains no mathematical content; it is organizational
  infrastructure only.

## Dependencies

- [Library](library.md) — this area builds on
  `Library.IdrisUtils`, `Library.IdrisCategories`, and
  `Library.IdrisAlgebra` for foundational utilities, the
  categorical vocabulary over `Type`, and F-algebra
  infrastructure.
- geb-language (`FullLanguageDef` ties together the language
  layer, importing from `UniversalCategory`, `Interpretation`,
  `Syntax`, `Expression`, and `Metaprogramming` in addition to
  the modules of this area).

## Pointers

The Idris codebase is the predecessor implementation; the
formalization here has been substantially superseded by the
Lean 4 continuation in `geb-lean`. The logic and effects
modules are stubs whose content has not yet been ported to
either implementation. Readers looking for the actively
maintained categorical formulation should consult
`geb-lean/docs/areas/category-judgments.md`.
