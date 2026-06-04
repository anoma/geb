# NNO, arithmetic, and topos-theoretic primitives

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

This area covers the categorical arithmetic of natural numbers
in Geb — NNO recursion derived from the parameterized binary
tree object (PBTO), internal arithmetic operations on
right-spine naturals, list-type objects (PSO, PLO) and their
relationship to the tree type — together with the
topos-theoretic and presheaf infrastructure that supports
parametric right adjoint (PRA) polynomial functors between
presheaf categories and the paranatural topos investigation.

## Mathematical context

A natural number object (NNO) in a category with finite products
is an object `N` together with `z : 1 → N` and `s : N → N`
universal for parameterized recursion (Lawvere, *Quantifiers and
Sheaves*, 1970). In Geb the NNO is derived from the parameterized
binary tree object (PBTO) by restricting to the right-spine
subalgebra. Arithmetic operations — predecessor, truncated
subtraction, addition, equality, Cantor pairing, and triangular
numbers — are built as morphisms in any category carrying the
PBTO structure, following Lambek–Scott style categorical
arithmetic (*Introduction to Higher-Order Categorical Logic*,
1986).

Parameterized snoclist objects (PSO) and cons-list objects (PLO)
are initial algebras of the functors `X ↦ 1 + X × B` and
`X ↦ 1 + B × X` respectively, generalizing the NNO (which
corresponds to `B = 1`). They supply an alternative route to
NNO-style recursion and connect the tree type to list
combinatorics via reversal.

Parametric right adjoints (PRAs) on presheaf categories are
characterized by the formula
`P(Z)(j) = ∐_{a ∈ A(j)} Hom(E_j(a), Z)` (Weber, *Generic
morphisms, parametric representations, and weakly cartesian
monads*, TAC 2004; Gambino–Kock, *Polynomial functors and
polynomial monads*, Math. Proc. Cambridge 2013). The `PresheafPRA*`
modules formalize the category of such functors as
`Jᵒᵖ ⥤ CoprodCovarRepCat (Iᵒᵖ ⥤ Type w)`, together with limits
in `CoprodCovarRepCat` and a discrete-base equivalence
`Over X ≌ (Discrete X)ᵒᵖ ⥤ Type`.

The paranatural topos investigation in `ParanaturalTopos.lean`
probes whether certain subcategories of profunctors with
paranatural transformations carry topos structure, developing an
assembly functor and diagonal-determinedness condition toward that
question.

Except where a construction is noted below as new, we have found
no prior Lean formalization of the material in this area.

## Modules

- [`GebLean/NatArith.lean`](../../GebLean/NatArith.lean) —
  arithmetic operations on right-spine naturals as morphisms in
  any category with a PBTO. `natTruncSub`, `natEq`, `cantorPair`,
  `natTri`, and `natPlus_assoc` / `natPlus_cancel_right` are the
  headline declarations; the file establishes that right-spine
  naturals form a commutative cancellative monoid under `natPlus`
  and that `natEq` is an equality test.
  The operations themselves are standard recursive-function-theory
  arithmetic (Lambek–Scott; nLab).

- [`GebLean/NatNNO.lean`](../../GebLean/NatNNO.lean) — NNO
  recursion interface derived from the PBTO, and Cantor
  unpairing. `nnoElim` wraps the PBTO fold with a
  `toRSpineNat`-normalization pre-step; `nnoElim_uniq` is its
  uniqueness theorem; `cantorUnpair` and
  `cantorUnpair_cantorPair` establish the retraction
  `cantorUnpair ; cantorPair = toRSpineNat`.
  The NNO universal property is standard and Cantor pairing and
  unpairing are classical.

- [`GebLean/PSO.lean`](../../GebLean/PSO.lean) — parameterized
  snoclist object (PSO): initial algebra of `X ↦ 1 + X × B`.
  `IsPSO` is the typeclass with `nil`, `snoc`, `elim`,
  `elim_nil`, `elim_snoc`, and `elim_uniq`; `IsPSTO` is the
  self-referential specialization (`B = L`); `nnoToIsPSO` derives
  a `PSO cfpTerminal nno.N` instance from any NNO.
  Parameterized list objects appear in categorical type theory
  (Uustalu–Vene, *Primitive (co)recursion and course-of-value
  (co)iteration*, 1999).

- [`GebLean/PLO.lean`](../../GebLean/PLO.lean) — parameterized
  cons-list object (PLO): initial algebra of `X ↦ 1 + B × X`,
  the cons-ordered dual of the PSO. `IsPLO` carries `nil`,
  `cons`, `elim`, `elim_nil`, `elim_cons`, and `elim_uniq`;
  `IsPLTO` is the self-referential specialization; `ploParaElim`
  is a paramorphism whose step sees the element, raw tail, and
  recursive result simultaneously.
  Parameterized list algebras are known mathematics (see PSO note
  above).

- [`GebLean/PSTONat.lean`](../../GebLean/PSTONat.lean) — NNO
  recursion derived from the PSTO (snoclist-of-trees) rather than
  the PBTO. `pstoNatSucc` is the PSTO successor (`n ↦ snoc(n, nil)`);
  `pstoToRSpineNat` is the normalization fold; the file's
  `nnoElim`-analogue derives `nnoElim_ℓ` and `nnoElim_s`
  computation rules for the PSTO-based recursion.
  The derivation of NNO recursion from a PSTO by replacing every
  element with `nil` is an instance of the general PSO-to-NNO
  reduction.

- [`GebLean/ParanaturalTopos.lean`](../../GebLean/ParanaturalTopos.lean)
  — investigation of topos structure on profunctor subcategories
  with paranatural transformations. `assemblyFunctor` is the
  central construction: given `F : TwistedArrow C ⥤ Cat` and a
  twisted arrow `tw`, it assembles decorated factorizations into
  `F(tw)` by transporting diagonal fiber elements along
  factorization morphisms. `IsDiagDetermined` and
  `IsDiagDeterminedEverywhere` state when a functor is controlled
  by diagonal data. The file also constructs terminal and binary
  product structures for endo-profunctors
  (`endoProfTerminal_isTerminal`, `endoProfBinaryFan_isLimit`) and
  a diagonal equalizer `diagEqualizer`.
  The assembly-functor approach and diagonal-determinedness
  condition for a paranatural topos do not appear in prior
  literature or mathlib; related background in
  [`docs/research/paranatural-topos-research.md`](../research/paranatural-topos-research.md)
  and
  [`docs/research/parametric-copresheaf-topos.md`](../research/parametric-copresheaf-topos.md).

- [`GebLean/PresheafPRA.lean`](../../GebLean/PresheafPRA.lean) —
  the category of PRA polynomial functors between presheaf
  categories. `PresheafPRACat` is the main object, built as
  `presheafPRACatFunctor.obj (op Iᵒᵖ)` where
  `presheafPRACatBifunctor` assembles `Jᵒᵖ ⥤ CoprodCovarRepCat
  (Iᵒᵖ ⥤ Type w)` from the hom-profunctor and a whiskering by
  `ccrPresheafCatFunctor`; `praPositions`, `praDirectionsAt`, and
  `praEvalAtFunctor` are the accessor maps.
  The Weber/Gambino–Kock PRA theory is known mathematics (Weber
  2004; Gambino–Kock 2013); its formalization as a
  bifunctor-assembled presheaf category is plausibly novel;
  background in
  [`docs/research/presheaf-pra.md`](../research/presheaf-pra.md).

- [`GebLean/PresheafPRADiscrete.lean`](../../GebLean/PresheafPRADiscrete.lean)
  — the discrete-base specialization: `overDiscretePresheafEquiv`
  is the equivalence `Over X ≌ (Discrete X)ᵒᵖ ⥤ Type`; `ccrMapEquiv`
  transports `CoprodCovarRepCat` across an equivalence of base
  categories; `polyBetweenPresheafPRAEquiv` establishes that
  polynomial functors between presheaf categories on discrete
  categories correspond to PRAs via the over-presheaf equivalence.
  `Over X ≌ presheaves on discrete X` is standard and mathlib
  has `piEquivalenceFunctorDiscrete`.

- [`GebLean/PresheafPRAUMorph.lean`](../../GebLean/PresheafPRAUMorph.lean)
  — limits in `CoprodCovarRepCat C`, enabling presheaf PRA
  composition. `ccrHasLimit`, `ccrHasLimitsOfShape`, and
  `ccrHasLimitsOfSize` are the main results, proved by identifying
  `CoprodCovarRepCat C` with `(Grothendieck (familyFunctor C))ᵒᵖ`
  and then appealing to mathlib's `hasLimits_op_of_hasColimits`.
  `ccrLimFunctor` and `ccrConstLimAdj` package the limit as a
  functor with adjoint, and `praReassemble` realizes a PRA's
  positions-and-directions data inside the limit.
  The limit construction for `CoprodCovarRepCat` via Grothendieck
  is specific to this setting; the underlying limit techniques are
  standard mathlib material.

## Alternative formulations

Two distinct routes derive NNO recursion. The PBTO-based route
in [`GebLean/NatNNO.lean`](../../GebLean/NatNNO.lean)
pre-normalizes via `toRSpineNat` before applying `p.elim`
directly. The PSTO-based route in
[`GebLean/PSTONat.lean`](../../GebLean/PSTONat.lean) applies the
PSO fold to replace every element with `nil`, arriving at
`pstoToRSpineNat` with the same result. These are two
implementations of the same NNO universal property, differing in
which initial-algebra interface they reduce to; no formal
equivalence between the routes has been proved.

## Dependencies

This area builds on:

- Polynomial functors and the PBTO / tree-logic layer (the
  `HasPBTO` typeclass, `TreeLogic`, `TreeGoedel`); see the
  quivers and polynomial-functors sections of the documentation
  index.
- Profunctors and the hexagon-cat/paranatural infrastructure
  (`GebLean/Utilities/Profunctors.lean`,
  `GebLean/HexagonCat.lean`, `GebLean/Paranatural.lean`) for
  `ParanaturalTopos.lean` and `PresheafPRA*`.
- The `CoprodCovarRepCat` and `Polynomial` modules
  (`GebLean/Polynomial.lean`) for the presheaf-PRA category.

## Pointers

- [`docs/research/presheaf-pra.md`](../research/presheaf-pra.md)
  — background on the PRA formula and Weber's characterization.
- [`docs/research/paranatural-topos-research.md`](../research/paranatural-topos-research.md)
  — exploratory notes on paranatural subcategory topos conditions.
- [`docs/research/parametric-copresheaf-topos.md`](../research/parametric-copresheaf-topos.md)
  — companion notes on the parametric copresheaf topos
  construction.
- [`docs/research/parameterized-list-object.md`](../research/parameterized-list-object.md)
  — background on parameterized list objects and their
  relationship to the NNO.
