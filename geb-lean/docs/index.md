# geb-lean documentation

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Directory structure](#directory-structure)
- [Area documents](#area-documents)
  - [Quivers, semicategories, acyclic categories](#quivers-semicategories-acyclic-categories)
  - [Category-judgment encodings](#category-judgment-encodings)
  - [Polynomial / W- / M-types and PFunctors](#polynomial--w---m-types-and-pfunctors)
  - [Profunctors and end machinery](#profunctors-and-end-machinery)
  - [Internal-presheaf Grothendieck equivalence](#internal-presheaf-grothendieck-equivalence)
  - [PshRelEdge and edge-of-presheaf machinery](#pshreledge-and-edge-of-presheaf-machinery)
  - [Tree calculus Phase 2](#tree-calculus-phase-2)
  - [K_sim hierarchy and ER ↔ K_sim_2 equivalence](#k_sim-hierarchy-and-er--k_sim_2-equivalence)
  - [NNO, arithmetic, and topos-theoretic primitives](#nno-arithmetic-and-topos-theoretic-primitives)
  - [Utilities (residual)](#utilities-residual)
- [CSLib](#cslib)
- [Coverage](#coverage)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

This index combines a directory layout for the source tree with
a topological narrative of the formalised mathematical content.
The directory layout below describes the namespace structure;
the area sections that follow describe each major area,
giving the central mathematical concepts it formalises and the
dependencies it has on other entries, and linking to the area
document under `docs/areas/` that carries the per-module detail.
The index is adequate rather than exhaustive: every major area
is reachable, and gaps are filled in as workstreams complete.

## Directory structure

The repository is laid out narrow-and-deep, with one indexing
`.lean` file per directory.

- `GebLean/` — root namespace, hosting the Lean source for the
  formalisation.
- `GebLean/Utilities/` — shared helpers used across the library.
- `GebLeanTests/` — test library, structured as `lake test`
  targets including `#guard` assertions and Plausible property
  tests.

## Area documents

The areas below partition the non-test source tree. Each is a
short orientation followed by a link to its area document; the
build-order dependencies are noted inline.

### Quivers, semicategories, acyclic categories

Directed graphs as quivers, free and cofree categories on a
quiver, semicategories (categories without identities), acyclic
quivers and the categories they freely generate, and
presentations of categories by generators and relations. This is
the foundational graph layer used by the category-judgment
encodings. See [`areas/quivers.md`](areas/quivers.md).

### Category-judgment encodings

Judgment-style presentations of categories and dependent
categories, the equivalence between judgmental and structural
presentations, and the `L ⊣ Φ` adjunction between categories and
copresheaves on `CategoryJudgments` (reflective right adjoint,
fully faithful Φ), together with its universal-property
preservation analysis. Builds on the quiver layer for the
underlying graph data. See
[`areas/category-judgments.md`](areas/category-judgments.md).

### Polynomial / W- / M-types and PFunctors

Polynomial endofunctors and their categories of algebras,
universal-morphism characterisations (products, coproducts,
equalizers, coequalizers, exponentials, left Kan extensions),
regular projective covers by representables, distributive laws
and GSOS, paranatural transformations, the Lawvere theory of
parameterized binary tree objects, the comonad bar resolution,
and the Bunge-Carboni free (co)equalizer completions. Builds on
the quiver layer; the profunctor, tree-calculus, and
lawvere-er-ksim areas build on this one. See
[`areas/polynomial-functors.md`](areas/polynomial-functors.md).

### Profunctors and end machinery

Profunctors as functors `Cᵒᵖ × C ⥤ D` with their two left and
right actions, the hexagon diagram for dialgebra-of-profunctor
data, ends and coends over the twisted-arrow category,
Mendler-Lambek end powers, weighted and (strong-)restricted
(co)wedges and their reductions to standard (co)wedges, the
Street-Walters comprehensive factorization, and the
Grothendieck presentations of twisted-arrow categories. Builds
on the polynomial-functor area. See
[`areas/profunctors-ends.md`](areas/profunctors-ends.md).

### Internal-presheaf Grothendieck equivalence

Internal categories in a presheaf topos, externalisation to a
`Cᵒᵖ ⥤ Cat` functor, the comparison functor from
internal-presheaves to presheaves on the Grothendieck
construction, and the equivalence
`PSh(C_int) ≃ PSh(Gr(ext(C_int)))`. Builds on the
profunctor area for the ends used in pointwise extraction and on
the polynomial-functor area for the presheaf-PRA layer. See
[`areas/internal-presheaf.md`](areas/internal-presheaf.md).

### PshRelEdge and edge-of-presheaf machinery

The edge-of-presheaf double category `PshRelEdge(C)`, its
cartesian-closed structure, separation properties, the
reflective chain `PSh(C) ⊣ Arr(PSh(C)) ⊣ PshRelEdge(C) ⊣
PshSpanCat`, the Hermida-Reddy-Robinson reflexive graph category
with identity-extension property, the `Subfunctor` / `WSubfunctor`
presentations of `PshRel` and `YonedaRel`, and the equivalence
`PshRelEdge C ≌ FullSubcategory IsSeparatedSpan`. Builds on the
profunctor area for ends and shares the presheaf-of-spans
setting with the internal-presheaf area. See
[`areas/pshreledge.md`](areas/pshreledge.md).

### Tree calculus Phase 2

Barendregt-style tree calculus over a binary-tree base,
polynomial combinators presenting the computation polynomial as a
two-sorted construction, value and behaviour polynomials as
reduction coalgebra, partial combinatory algebra structure,
confluence, derived combinators, and the primitive-recursive
fragment. Builds on the polynomial-functor area for the
polynomial-functor base and on the profunctor area for the
bialgebraic GSOS layer. See
[`areas/tree-calculus.md`](areas/tree-calculus.md).

### K_sim hierarchy and ER ↔ K_sim_2 equivalence

Tourlakis's K^sim hierarchy as a Lawvere category with
simultaneous-recursion constructors, the elementary-recursive
Lawvere category `LawvereERCat`, the forward
`kToERFunctor` witnessing `K^sim_2 ⊆ ER` with polynomial-bound
and A-majorant infrastructure, the reverse `erToKFunctor` via URM
simulation, and the packaged categorical equivalence
`erKSimEquiv : LawvereERCat ≌ LawvereKSimDCat 2` (Tourlakis 2018
Corollary 0.1.0.44 at `n = 2`). Builds on the polynomial-functor
area for the Lawvere-categorical setting and shares the
primitive-recursive layer with the tree-calculus area. See
[`areas/lawvere-er-ksim.md`](areas/lawvere-er-ksim.md).

### NNO, arithmetic, and topos-theoretic primitives

Natural-number-object, arithmetic, and topos-theoretic
primitives that the other areas draw on as ambient categorical
infrastructure. See
[`areas/nno-arithmetic-topos.md`](areas/nno-arithmetic-topos.md).

### Utilities (residual)

The cross-cutting `Utilities/*.lean` helpers not claimed by a
topical area, together with the `Utilities.lean` and `GebLean.lean`
aggregators. See [`areas/utilities.md`](areas/utilities.md).

## CSLib

CSLib is a peer dependency, not a source area of this repository.
It provides computability and concurrency formalisations (URM,
automata, process calculi), pinned by a tagged release tracking
the Lean toolchain RC. It is consumed by the lawvere-er-ksim area
(URM simulation lemmas) and the tree-calculus area (LTS layer for
reduction).

## Coverage

The area documents partition every non-test `.lean` file (215 =
214 under `GebLean/` plus the root `GebLean.lean`) into exactly
one area. The assignment is recorded in
[`areas/_partition-notes.md`](areas/_partition-notes.md) and
checked by `docs/tools/check-area-coverage.sh lean`.
