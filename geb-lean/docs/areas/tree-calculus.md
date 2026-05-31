# Tree calculus Phase 2

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Purpose](#purpose)
- [Mathematical context](#mathematical-context)
- [Modules](#modules)
- [Dependencies](#dependencies)
- [Pointers](#pointers)

<!-- END doctoc -->

## Purpose

This area formalises the binary-tree calculus of Barry Jay as a
polynomial-functor system, presenting the value type, reduction
rules, and computation as an algebra–coalgebra (lambda-bialgebra)
structure, and providing the abstract GSOS/bialgebraic layer that
relates the two.  It supplies Geb with a computationally
executable model of a reflective programming language whose
programs and data share a single tree type.

## Mathematical context

Tree calculus (*Reflective Programs in Tree Calculus*, Barry Jay,
2021; *Typed Program Analysis without Encodings*, Jay and
Vergauwen, PEPM 2025) is a Barendregt-style combinator calculus
whose sole base type is the binary tree.  The three value
constructors — leaf, stem, and fork — give a partial combinatory
algebra (PCA) with leaf as the sole primitive and five triage
reduction rules as the computation laws.  Confluence is proved
via the diamond property of parallel reduction (Tait–Martin-Loef
method).

Jay provides an associated Coq formalisation of the core
calculus; see
[`docs/research/tree-calculus.md`](../research/tree-calculus.md)
for the external reference record.

In this formalisation the value type is the initial algebra of a
three-summand polynomial endofunctor `polyValue` on `Over PUnit`;
computation is the coalgebra of a four-position behavior
polynomial `polyBehavior`; and the one-step reduction function
`step` packages the two as a polynomial coalgebra.  The
polynomial combinators from the polynomial-functors area provide
the base machinery; the GSOS rule and lambda-bialgebra structures
express the operational semantics in a categorical language
following Turi–Plotkin (*Towards a Mathematical Operational
Semantics*, LICS 1997) — a Geb-specific polynomial/bialgebraic
presentation for which no prior Lean formalisation is known.

The area also includes supporting constructions: a finite-alphabet
generalization of the binary-tree Gödel numbering (`BTα`,
`equivBTnNat`), an indexed essentially algebraic theory layer
(`IndexedEAT`, `EATModel`) sitting between the raw polynomial
algebra and the tree-calculus models, and a judgment-universe
organising the forgetful hierarchy from categories down to plain
types.

## Modules

- [`GebLean/PLang/BTPair.lean`](../../GebLean/PLang/BTPair.lean)
  — bijections between finite-alphabet binary trees and `ℕ`.
  `BTα` is the free monad of `polyProdType` over a labeled
  alphabet; `equivBTnNat` is the bijection
  `BTα (Fin (n+1)) ≃ ℕ`; `encodeBTn_le_fullBTn_iff_depth_le`
  characterizes trees of bounded depth as exactly those whose
  encoding is at most the code of the perfect tree of that depth.
  Provenance: known maths (Gödel/Cantor tree-pairing, Nat.pair
  from mathlib), first Lean formalisation of the labeled-alphabet
  generalization; searched 2026-05-31, scope Mathlib
  (leansearch/loogle), nLab.

- [`GebLean/PLang/IndexedEAT.lean`](../../GebLean/PLang/IndexedEAT.lean)
  — essentially algebraic theories indexed by a type `X`,
  modelling operations as polynomial endofunctors and equations
  as equivalence relations on the initial algebra.  `IndexedEAT`
  bundles `poly`, `equations`, and `eqIsEquiv`; `EATModel` is a
  P-algebra for which the canonical fold respects the equations;
  `EATHasQuotient` axiomatises the existence and universal
  property of a quotient algebra.
  Provenance: known maths (essentially algebraic theories:
  Adámek–Rosický, *Locally Presentable and Accessible Categories*
  1994; Johnstone, *Sketches of an Elephant* II), first Lean
  formalisation of this indexed-polynomial presentation; searched
  2026-05-31, scope Mathlib (leansearch), nLab.

- [`GebLean/PLang/JudgmentUniverse.lean`](../../GebLean/PLang/JudgmentUniverse.lean)
  — the judgment category `JudgmentLevel` (objects: `obj`,
  `quiv`, `cat`) and the judgment universe functor
  `JudgmentUniverse : JudgmentLevel ⥤ Cat`, which maps each
  level to the corresponding copresheaf category.  Morphisms in
  `JudgmentLevel` represent forgetful relations between levels of
  categorical structure.
  Provenance: novel mathematics — this specific three-object
  index category organising the forgetful hierarchy has no prior
  formalisation found; nearest antecedent is the walking-quiver
  and walking-category structures in mathlib; searched
  2026-05-31, scope Mathlib (leansearch), nLab. `unverified`

- [`GebLean/PLang/Syntax.lean`](../../GebLean/PLang/Syntax.lean)
  — the product polynomial endofunctor `polyProd` on `Over X`
  (one position, two-element fiber), the free monad of `polyProd`
  giving binary trees as the generic syntax type, and the
  associated evaluation functors and `Type`-specializations.
  Provenance: known maths, first Lean formalisation — `polyProd`
  is the standard "product" polynomial over a slice category;
  the free-monad construction reuses `polyFreeFunctor` from the
  polynomial-functors area; searched 2026-05-31, scope Mathlib
  (leansearch/loogle).

- [`GebLean/PLang/TermCat.lean`](../../GebLean/PLang/TermCat.lean)
  — stub module for the term category constructed from binary
  trees; imports `Syntax.lean` and provides the namespace
  `GebLean` as the entry point for future term-category
  development.
  Provenance: skeleton; no declarations beyond namespace opening;
  searched 2026-05-31.

- [`GebLean/PLang/TreeCalcMeta.lean`](../../GebLean/PLang/TreeCalcMeta.lean)
  — PCA structure and confluence for tree calculus.
  `Value.apply` forms the application of two values as a
  `CompTree`; `pcaK` and `pcaS` are the designated combinators;
  `ParReduces` is the parallel-reduction inductive and
  `Confluent` is the confluence statement (detailed diamond-
  property proof deferred).
  Provenance: category 3 (known maths, prior Coq formalisation by
  Jay) for the PCA axioms and confluence statement; the
  `CompTree` / `CompValue` split and polynomial packaging are
  Geb-specific; searched 2026-05-31, scope Jay's Coq repo, Mathlib
  (leansearch).

- [`GebLean/PLang/TreeCalcPoly.lean`](../../GebLean/PLang/TreeCalcPoly.lean)
  — the value polynomial `polyValue` (three summands: leaf, stem,
  fork) and the `Value` type as its initial algebra.  `Value.leaf`,
  `Value.stem`, `Value.fork`, and `Value.fold` are the
  constructors and catamorphism; `Value.cases` is the
  non-recursive eliminator.
  Provenance: category 3 (known maths, prior Coq formalisation by
  Jay) for the tree-calculus value grammar; the polynomial
  presentation via `polyValue` is Geb-specific; searched
  2026-05-31, scope Jay's Coq repo, Mathlib (leansearch).

- [`GebLean/PLang/TreeCalcPrograms.lean`](../../GebLean/PLang/TreeCalcPrograms.lean)
  — derived combinators defined as `Value` terms.  `Value.K`,
  `Value.S`, and `Value.I` are the standard combinators;
  `Value.triage` is the triage combinator; `Value.appArgs`
  performs left-associated application to a list.
  Provenance: category 3 (known maths, prior Coq formalisation by
  Jay) for the combinator definitions; searched 2026-05-31, scope
  Jay's Coq repo.

- [`GebLean/PLang/TreeCalcReduction.lean`](../../GebLean/PLang/TreeCalcReduction.lean)
  — the behavior polynomial `polyBehavior` (four positions:
  done-leaf, done-stem, done-fork, continuation), one-step
  reduction `reduce1`, the coalgebra structure map `step`,
  `stepCoalg` packaging `CompTree` as a `PolyCoalg`, and the
  evaluation anamorphism `eval` into the terminal coalgebra.
  `Reduces` is the multi-step reduction relation.
  Provenance: category 1 (Geb-specific polynomial/coalgebraic
  presentation) for `polyBehavior`, `stepCoalg`, and `eval`; the
  reduction rules follow Jay's Coq formalisation (category 3);
  searched 2026-05-31, scope Jay's Coq repo, Mathlib (leansearch).

- [`GebLean/Utilities/GSOSRule.lean`](../../GebLean/Utilities/GSOSRule.lean)
  — abstract GSOS rule in the sense of Turi–Plotkin,
  parameterized by a signature endofunctor `Sigma`, a behavior
  endofunctor `B`, a monad `T`, and chosen binary products.
  `idBehaviorFunctor` builds `X ↦ X × B(X)` from chosen
  products; `GSOSRule` is the structure carrying a natural
  transformation `Sigma(X × B(X)) → B(T(X))`.
  Provenance: known maths (Turi–Plotkin LICS 1997), first Lean
  formalisation of this abstract formulation; searched 2026-05-31,
  scope Mathlib (leansearch), nLab.

- [`GebLean/Utilities/LambdaBialgebra.lean`](../../GebLean/Utilities/LambdaBialgebra.lean)
  — lambda-bialgebra for a distributive law `T ∘ D ⟹ D ∘ T`:
  an object with a compatible `T`-algebra and `D`-coalgebra
  structure subject to a pentagonal compatibility condition.
  `LambdaBialgebra` is the structure; `LambdaBialgebra.Hom`
  packages simultaneous algebra and coalgebra homomorphisms;
  `toMonadAlgebra` and `toComonadCoalgebra` extract the
  components.
  Provenance: known maths (Turi–Plotkin LICS 1997; Power–Watanabe
  distributive laws for bialgebras), first Lean formalisation;
  searched 2026-05-31, scope Mathlib (leansearch), nLab.

## Dependencies

- Polynomial functors: `GebLean/Utilities/PolyCombinators.lean`
  and the wider polynomial-functor area supply `PolyEndo`,
  `PolyFix`, `PolyCofix`, `polyFixFoldAtWithProof`,
  `polyCofixUnfoldAt`, and `polyFreeFunctor`, which are the
  direct substrate for `polyValue`, `Value`, and `stepCoalg`.
- Profunctors and ends (bialgebraic GSOS layer): the
  distributive-law infrastructure in
  `GebLean/Utilities/DistributiveLaw.lean`, imported by
  `LambdaBialgebra.lean`, connects to the profunctors-ends area.

## Pointers

- [`docs/research/tree-calculus.md`](../research/tree-calculus.md)
  — external reference record: Jay's 2021 monograph, PEPM 2025
  paper, and associated Coq formalisation.
- [`docs/superpowers/specs/2026-03-22-tree-calculus-phase2-design.md`](../superpowers/specs/2026-03-22-tree-calculus-phase2-design.md)
  — design spec for Tree Calculus Phase 2: polynomial presentation
  of the value type, behavior polynomial, reduction coalgebra, and
  GSOS/bialgebra layer.
