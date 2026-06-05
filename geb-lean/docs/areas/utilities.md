# Utilities (residual)

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Purpose](#purpose)
- [Mathematical context](#mathematical-context)
- [Modules](#modules)
  - [Aggregators](#aggregators)
  - [Arrow and cospan adjunctions](#arrow-and-cospan-adjunctions)
  - [Computable limits](#computable-limits)
  - [Dagger categories](#dagger-categories)
  - [Distributive laws](#distributive-laws)
  - [Double categories](#double-categories)
  - [Transport and equality lemmas](#transport-and-equality-lemmas)
  - [Families and completions](#families-and-completions)
  - [Finite types](#finite-types)
  - [Graph span diagram category](#graph-span-diagram-category)
  - [Opposite categories (`op'`)](#opposite-categories-op)
  - [Presheaves and copresheaves](#presheaves-and-copresheaves)
  - [Representable density](#representable-density)
  - [Setoid categories](#setoid-categories)
  - [Sigma type utilities](#sigma-type-utilities)
  - [Skeletons](#skeletons)
  - [Slice and coslice utilities](#slice-and-coslice-utilities)
- [Dependencies](#dependencies)
- [Pointers](#pointers)

<!-- END doctoc -->

## Purpose

This area collects general-purpose helper modules that are used across
multiple topical areas but are not claimed by any one of them. It also
contains the two top-level re-export aggregators that define the
library's public import surface.

## Mathematical context

The helpers span a range of standard category-theoretic structures:
dagger categories, strict double categories, distributive laws, free
coproduct and product completions via the Grothendieck construction,
slice and coslice category utilities, presheaf and copresheaf
construction functors (including the subobject classifier and covariant
Yoneda lemmas), representable density, setoid categories, skeletons,
sigma-type and transport lemmas, and small computable variants of
standard limit notions. Each module transcribes or extends a
well-established standard concept; novelty, where it exists, is
recorded in the module's own description.

## Modules

### Aggregators

- [`GebLean.lean`](../../GebLean.lean) — root re-export aggregator for
  the entire library; imports every topical area and every utility
  module.

- [`GebLean/Utilities.lean`](../../GebLean/Utilities.lean) — Utilities
  sub-library aggregator; re-exports all modules under
  `GebLean/Utilities/`.

### Arrow and cospan adjunctions

- [`GebLean/Utilities/Arrow.lean`](../../GebLean/Utilities/Arrow.lean)
  — the adjoint triple `Arrow.rightFunc ⊣ Arrow.idInclusion ⊣
  Arrow.leftFunc` for an arbitrary category `C`.
  `Arrow.idInclusion` (the fully faithful inclusion of `C` into its
  arrow category via identity arrows) is simultaneously reflective and
  coreflective, giving `Arrow.idInclusionTriple`.
  A standard adjoint triple on the arrow category
  (mathlib `CategoryTheory.Comma.Arrow`).

- [`GebLean/Utilities/ArrowCospanAdjunction.lean`](../../GebLean/Utilities/ArrowCospanAdjunction.lean)
  — the coreflective adjunction `arrowCospanInclusion C ⊣
  cospanArrowCoreflector` exhibiting `Arrow C` as a coreflective
  subcategory of the cospan-diagram category, parameterized by an
  explicit (constructive) choice of pullback cones.
  A standard adjunction dual to the arrow-span adjunction.

### Computable limits

- [`GebLean/Utilities/ComputableLimits.lean`](../../GebLean/Utilities/ComputableLimits.lean)
  — `Type`-valued (constructive) counterparts of mathlib's
  `Prop`-valued `HasLimit` / `HasFiniteProducts` / `HasEqualizers`.
  `HasChosenFiniteProducts`, `HasChosenEqualizers`, and
  `HasChosenFiniteLimits` carry chosen limit cones as data; each
  implies its mathlib counterpart via derivation instances.
  A constructive restatement of standard limit existence.

### Dagger categories

- [`GebLean/Utilities/DaggerCategory.lean`](../../GebLean/Utilities/DaggerCategory.lean)
  — the `DaggerCategory` typeclass: an involutive, identity-on-objects,
  contravariant endoperation on morphisms satisfying `dagger_id`,
  `dagger_comp`, and `dagger_involutive`.
  The dagger category is a standard concept.

### Distributive laws

- [`GebLean/Utilities/DistributiveLaw.lean`](../../GebLean/Utilities/DistributiveLaw.lean)
  — the `DistributiveLaw` structure for a monad `T` over a comonad `D`:
  a natural transformation `D ⋙ T ⟶ T ⋙ D` satisfying four
  coherence axioms (unit, multiplication, counit, comultiplication).
  A standard distributive law of a monad over a comonad
  (Beck 1969; Street 1972).

### Double categories

- [`GebLean/Utilities/DoubleCategory.lean`](../../GebLean/Utilities/DoubleCategory.lean)
  — strict double categories as categories internal to `Cat`.
  `DoubleCategoryData` bundles vertical and horizontal category
  operations together with vertical and horizontal square compositions
  and their laws (associativity, identity, interchange).
  `DoubleFunctorData` and `VertTransData` provide the corresponding
  notion of strict double functor and vertical transformation.
  Standard strict double categories (Ehresmann 1963;
  Grandis–Paré 1999).

### Transport and equality lemmas

- [`GebLean/Utilities/Equalities.lean`](../../GebLean/Utilities/Equalities.lean)
  — a large collection of `@[simp]` lemmas about `Eq.rec` (transport),
  sigma types, subtypes, and `Over`-category morphisms under equality
  and heterogeneous-equality hypotheses. Also defines the
  `intermediate_eq` tactic macro (`refine Eq.trans (b := _) ?_ ?_`).
  Standard transport bookkeeping.

### Families and completions

- [`GebLean/Utilities/Families.lean`](../../GebLean/Utilities/Families.lean)
  — the family functor `familyFunctor C : (Type w)ᵒᵖ ⥤ Cat` and its
  Grothendieck constructions yielding the four standard completions:
  `FreeCoprodCompletionCat`, `FreeProdCompletionCat`,
  `CoprodCovarRepCat` (polynomial functors), and
  `ProdContravarRepCat`. Also provides `CoprodData` / `ProdData`
  typeclasses with computable instances for `Over X`, and proves
  `ccrNewEvalCatFullyFaithful` (full faithfulness of evaluation for
  `CoprodCovarRepCat`).
  Standard free-completion constructions via the Grothendieck
  construction (nLab: free coproduct completion, Dirichlet
  functors, polynomial functors).

### Finite types

- [`GebLean/Utilities/Fintype.lean`](../../GebLean/Utilities/Fintype.lean)
  — `FintypeData`: a structure-based counterpart to the `Fintype`
  typeclass, bundling a `Finset` with the completeness property.
  `fintypeDataOfFintype` extracts data from a `Fintype` instance.
  A standard finite-type interface.

### Graph span diagram category

- [`GebLean/Utilities/Graph.lean`](../../GebLean/Utilities/Graph.lean)
  — the graph span diagram category `GraphSpanObj V E` (a small
  category with vertex-nodes and edge-nodes, with projections from
  each edge-node to its endpoints), and `graphSpanCollageIso` proving
  it isomorphic to the collage of `graphSpanProfunctor V E`.
  A standard collage / profunctor construction.

### Opposite categories (`op'`)

- [`GebLean/Utilities/Opposites.lean`](../../GebLean/Utilities/Opposites.lean)
  — an alternative opposite-category construction `CategoryOp'`
  (notation `Cᵒᵖ'`) satisfying `(Cᵒᵖ')ᵒᵖ' = C` definitionally,
  unlike mathlib's `Opposite` which satisfies this only
  propositionally. Provides `opToOp'` / `op'ToOp`, `opIsoOp'`,
  `Cat.opFunctor'` (the strictly involutive endofunctor on `Cat`),
  and all derived functor-category isomorphisms and coercions.

### Presheaves and copresheaves

- [`GebLean/Utilities/Presheaf.lean`](../../GebLean/Utilities/Presheaf.lean)
  — the contravariant `copresheafConstruction` and
  `presheafConstruction` functors `Catᵒᵖ' ⥤ Cat`; computable
  pointwise pullbacks for copresheaf morphisms
  (`presheafPullbackCone`, `presheafPullbackIsLimit`); the subobject
  classifier for `Cᵒᵖ ⥤ Type` (`pshClassifierData`, `PshClassifier`)
  and for `C ⥤ Type` (`CoPshClassifier`); and covariant Yoneda
  equivalences (`coyonedaEquivOfNatIso`,
  `coyonedaNatIsoOfNatIso`, `uliftCoyonedaNatIsoOfNatIso`).
  Standard presheaf constructions and the Yoneda lemma.

### Representable density

- [`GebLean/Utilities/RepresentableDensity.lean`](../../GebLean/Utilities/RepresentableDensity.lean)
  — density of the representable embedding
  `pshRelEdgeRepresentableFunctor` in `PshRelEdge C`, proved via the
  density of `uliftCoyoneda` and preservation of the density colimit
  by the separation adjunction `pshRelEdgeSepAdjunction`.
  `pshRelEdgeRepresentableIsDense` is the headline instance.
  The standard density theorem for representable presheaves
  (Yoneda density); the application to the `PshRelEdge`
  construction is specific to this development.

### Setoid categories

- [`GebLean/Utilities/SetoidCat.lean`](../../GebLean/Utilities/SetoidCat.lean)
  — the category `SetoidCat` of setoids (`SetoidBundle` objects,
  `SetoidHom` morphisms), with `quotientFunctor` and
  `forgetful` functors to `Type`. Also defines `SetoidNatTrans`,
  `SetoidNatIso`, and `SetoidEquivalence` (an up-to-setoid-relation
  analogue of a categorical equivalence).
  The setoid category is a standard concept.

### Sigma type utilities

- [`GebLean/Utilities/Sigma.lean`](../../GebLean/Utilities/Sigma.lean)
  — `sigmaTrivialSubtype` (equivalence from a doubly-indexed subtype to
  a fiber), and `simp` lemmas about `cast` on sigma types along family
  equalities (`sigma_cast_of_funEq`, `sigma_cast_fst_of_funEq`).
  Standard sigma-type bookkeeping.

### Skeletons

- [`GebLean/Utilities/Skeleton.lean`](../../GebLean/Utilities/Skeleton.lean)
  — a constructive quotient of a category by isomorphism: `Skeleton C
  := Quotient (isIsomorphicSetoid C)`, defined using only the
  constructive `Quotient` API. Provides `toSkeleton`, `Skeleton.lift`,
  and `Skeleton.lift₂`.
  The skeleton (isomorphism classes) is a standard construction;
  this formulation uses only the constructive `Quotient` API,
  unlike mathlib's `CategoryTheory.Skeleton` which uses
  `Quotient.out` (non-constructive).

### Slice and coslice utilities

- [`GebLean/Utilities/Slice.lean`](../../GebLean/Utilities/Slice.lean)
  — utilities for `Over` and `Under` categories: accessor abbreviations
  (`Over.left`, `Under.right`, `Over.leftOp'`), the equivalence
  `underEquivOverOp'Op'` between `Under X` and `(Over X)ᵒᵖ'` in
  `Dᵒᵖ'`, the functors `overOpMapFunctor` and
  `overCopresheafFunctor`, and the constructive self-product
  `overSelfProd` with its functor.
  Standard over/under category constructions
  (mathlib `CategoryTheory.Comma.Over`).

## Dependencies

The modules in this area are dependencies for all other topical areas
in the library; they supply the foundational helpers that topical
modules import. In particular, the two aggregators
[`GebLean.lean`](../../GebLean.lean) and
[`GebLean/Utilities.lean`](../../GebLean/Utilities.lean) define the
library's import surface and are the entry points for consumers of the
full library.

## Pointers

- The category-judgments area uses `Utilities/Category.lean` and
  `Utilities/OverCategoryEquiv.lean` for its unbundled category and
  functor data; those two modules are documented in the
  [category-judgments area doc](category-judgments.md).
