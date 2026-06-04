# Quivers, semicategories, acyclic categories

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Purpose](#purpose)
- [Mathematical context](#mathematical-context)
- [Modules](#modules)
- [Alternative formulations](#alternative-formulations)
- [Dependencies](#dependencies)
- [Pointers](#pointers)

<!-- END doctoc -->

## Purpose

This area defines the foundational graph layer on which Geb's
categories are built: quivers (directed graphs), their finite
and acyclic variants, semicategories (quivers with associative
composition but no identities), acyclic categories (semicategories
whose quiver is acyclic), and the presentation of categories by
generators and relations on a quiver. It also contains the cofree
category on a polynomial endofunctor, which is the categorical
counterpart of the cofree comonad on polynomial coalgebras. This
layer underlies the [category-judgments area](category-judgments.md),
whose reflection `L` quotients free morphisms produced here.

## Mathematical context

A *quiver* is a directed multigraph: a set of vertices together with
a set of edges between each ordered pair of vertices. Quivers are the
generating data for free categories: the free category on a quiver
`V` has `V` as objects and finite paths in `V` as morphisms, with
path concatenation as composition (Mac Lane, *Categories for the
Working Mathematician*, §II.7; Borceux, *Handbook of Categorical
Algebra* I, §3.7). Mathlib formalizes quivers as
`CategoryTheory.Quiver` and free categories as `Quiver.Paths`.

A *semicategory* (also called a *semigroupoid*) is a quiver with
associative composition but no required identity morphisms (Mitchell,
*Theory of Categories*, §I.2). Identities can always be freely
adjoined, producing a category whose non-identity morphisms are
exactly those of the original semicategory.

An *acyclic quiver* is a quiver equipped with a topological order on
vertices such that every edge goes strictly upward in the order; this
condition implies there are no directed cycles. An *acyclic category*
combines an acyclic quiver with a semicategory structure. Acyclic
categories arise naturally as poset-like structures where morphisms
record reachability without backtracking; their category of presheaves
is used in combinatorics and directed topology.

A *presentation of a category by generators and relations* starts
from a quiver (generators), forms the free category (paths), and
quotients by a congruence relation (Mac Lane, §II.7; nLab,
"presentation of a category"). Mathlib provides
`CategoryTheory.Quotient` for this construction.

The *cofree category* on a polynomial endofunctor `P` is the category
corresponding to the cofree comonad on `P`-coalgebras, with objects
pairs of a base element and a `P`-shaped tree (an M-type), and
morphisms being positions in that tree (Adámek–Porst, *On tree
coalgebras and coalgebra presentations*, 2004; Spivak, *Poly: An
abundant universe of functors*, 2021).

## Modules

- [`GebLean/FiniteQuiver.lean`](../../GebLean/FiniteQuiver.lean) —
  finiteness witness and typeclass for quivers, and the full
  subcategory of finite quivers inside `Quiv`.
  `FinQuiverWitness` bundles `FintypeData` for vertices and each
  edge set; `FiniteQuiver` is the typeclass version; `FiniteQuiverCat`
  is the full subcategory of `Quiv` cut out by `IsFiniteQuiver`.
  Mathlib formalizes `Quiv` and finite quivers indirectly via
  `CategoryTheory.Category.Quiv` and `Fintype`; the explicit
  `FinQuiverWitness` bundling is a local convenience over those
  mathlib primitives.

- [`GebLean/Semicategory.lean`](../../GebLean/Semicategory.lean) —
  the `Semicategory` typeclass, `Semifunctor`, the bundled category
  `SemicategoryCat`, and the identity-adjunction construction.
  `AdjoinedIdHom` is the inductive type of morphisms in the category
  obtained by freely adjoining identities to a semicategory;
  `adjoinedIdCategory` gives the resulting `Category` instance;
  `liftToFunctor` lifts a `Semifunctor` to a functor between the
  identity-adjoined categories; `toCat` is the inclusion functor
  `SemicategoryCat ⥤ Cat`.
  Semicategories and the identity-adjunction construction are standard
  (Mitchell, *Theory of Categories*, §I.2).

- [`GebLean/AcyclicQuiver.lean`](../../GebLean/AcyclicQuiver.lean) —
  acyclic quivers witnessed by a topological order on vertices, and
  the category of acyclic quivers.
  `AcyclicQuiver` extends `Quiver` with a `TopologicalOrder` and the
  condition `QuiverEdgesIncrease`; `AcyclicQuiverWitness` is the
  bundled-structure form; `AcyclicQuiverCat` is the large bundled
  category of acyclic quivers with order-preserving prefunctors as
  morphisms; `no_cycles` establishes that any path from a vertex to
  itself must be `nil`.
  Acyclic quivers via topological ordering are standard graph theory
  (Bang-Jensen–Gutin, *Digraphs*, §1.2).

- [`GebLean/AcyclicCat.lean`](../../GebLean/AcyclicCat.lean) —
  acyclic categories, the bundled category `AcyclicCategoryCat`, and
  the full subcategory of finite acyclic categories.
  `AcyclicCategory` is an `AcyclicQuiver` with a `SemicategoryStruct`;
  `AcyclicCategoryHom` is a `Semifunctor` that additionally preserves
  the strict vertex order; `AcyclicCategoryCat` is the resulting
  large category; `AcyclicCategory.toCat` factors through
  `Semicategory.toCat`; `adjoinedId_edges_nonstrictly_increase`
  records that after identity adjunction each morphism either
  strictly increases or is an identity on equal vertices.
  Acyclic categories (also called acyclic directed categories or strict
  poset-enriched categories) appear in directed homology and
  combinatorics.

- [`GebLean/CategoryPresentation.lean`](../../GebLean/CategoryPresentation.lean)
  — presentation of a category by generators and relations via
  free category then quotient.
  `CategoryPresentation` bundles a quiver `generators` and a
  `HomRel` on `Paths generators`; `toCategory` forms the quotient
  via `CategoryTheory.Quotient`; `categoryToCategory` gives the
  resulting `Category` instance.
  The generators-and-relations construction is standard (Mac Lane,
  *Categories for the Working Mathematician*, §II.7) and is directly
  supported by mathlib's `CategoryTheory.Quotient` and `Quiv.free`;
  this module is a thin wrapper packaging those mathlib primitives.

- [`GebLean/AcyclicPresentation.lean`](../../GebLean/AcyclicPresentation.lean)
  — specialization of `CategoryPresentation` to acyclic and finite
  acyclic generators, with path-length bounds and finite path
  enumeration.
  `AcyclicPresentation` extends `CategoryPresentation` with an
  `AcyclicQuiverWitness` on the generators;
  `FiniteAcyclicPresentation` further adds a `FinQuiverWitness`;
  `path_length_bounded` proves that in a finite acyclic quiver
  every path has length strictly less than the vertex count;
  `finite_paths_in_finite_acyclic_quiver` derives `Fintype` for
  all paths between two vertices in such a quiver via
  `finsetPathsBounded` and `fintypePathsBounded`.
  The path-length bound via topological ordering is standard
  (Bang-Jensen–Gutin, *Digraphs*, §1.2).

- [`GebLean/CofreeCategory.lean`](../../GebLean/CofreeCategory.lean)
  — the cofree category on a polynomial endofunctor, built from
  M-type trees, and the copresheaf functor associating a coalgebra
  to a presheaf on this category.
  `PolyCofreeCat` has objects `⟨fiber, shape⟩` (a base element and
  a `PolyCofreeShape` M-type tree); `PolyCofreeCatHom` records a
  depth and position in the source tree; `polyCofreeCatCategory`
  assembles the category laws via path-concatenation in the M-type;
  `polyCofreeCatHomEquiv` exhibits the hom-set as annotation
  positions in the source shape; `coalgCopresheaf` constructs the
  copresheaf `PolyCofreeCat P ⥤ Type u` associated to a
  `P`-coalgebra.
  The cofree category on a polynomial endofunctor and the equivalence
  of coalgebras with copresheaves on it is treated in Adámek–Porst
  (2004) and Spivak (2021, §3.3).

## Alternative formulations

There are no duplicate formulations within this area. The
acyclic-quiver condition is stated once (via `TopologicalOrder` and
`QuiverEdgesIncrease`) and reused by `AcyclicCat`,
`AcyclicPresentation`, and the acyclic-finiteness predicate in
`FiniteQuiver`.

## Dependencies

This area is foundational and does not build on other area docs.
It imports mathlib's `CategoryTheory.Quiver`, `Quiver.Paths`,
`CategoryTheory.Quotient`, `Quiv`, and `ObjectProperty.FullSubcategory`,
as well as `GebLean.PolyAlg` (polynomial coalgebra infrastructure) for
`CofreeCategory.lean`.

## Pointers

- The [category-judgments area](category-judgments.md) builds
  directly on this layer: the reflection functor `L` in `L ⊣ Φ`
  quotients free morphisms (paths in the generator quiver) by the
  composition and identity relations recorded in a copresheaf on `J`.
- The research note
  [`docs/research/polynomial-algebra-coalgebra-categories.md`](../research/polynomial-algebra-coalgebra-categories.md)
  contains prior-art analysis and mathematical context for the
  cofree-comonad and cofree-category constructions in
  `CofreeCategory.lean`.
