# Ramified recurrence and the elementary characterization

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Purpose](#purpose)
- [Mathematical context](#mathematical-context)
- [Modules](#modules)
  - [The generic core](#the-generic-core)
  - [The higher-order system](#the-higher-order-system)
  - [Algebra instances and first-order sub-theories](#algebra-instances-and-first-order-sub-theories)
  - [Definability (`GebLean/Ramified/Definability/`)](#definability-gebleanramifieddefinability)
  - [Soundness (`GebLean/Ramified/Soundness/`)](#soundness-gebleanramifiedsoundness)
  - [Characterization](#characterization)
  - [Ramified recurrence on the polynomial-functor stack (`GebLean/Ramified/Polynomial/`)](#ramified-recurrence-on-the-polynomial-functor-stack-gebleanramifiedpolynomial)
- [Statement inventory](#statement-inventory)
- [Deferred and future work](#deferred-and-future-work)
- [Dependencies](#dependencies)
- [Pointers](#pointers)
- [References](#references)

<!-- END doctoc -->

## Purpose

This area formalizes Leivant's higher-type ramified recurrence
system `RMRec-omega` as a multi-sorted Lawvere theory and proves,
relative to the elementary-recursive Lawvere category
`LawvereERCat`, the denotational form of the two directions of
Leivant III's Theorem 14: every elementary-recursive morphism is
ramified-definable (definability), and every morphism of the
first-order syntactic category has elementary denotation
(soundness), the latter packaged as a faithful functor
`collapseFunctor : SynCatFO ⥤ LawvereERCat`. The characterization
transfers across the equivalence
`erKSimEquiv : LawvereERCat ≌ LawvereKSimDCat 2` to Tourlakis's
degree-2 `K^sim` level.

## Mathematical context

Ramified (tiered) recurrence stratifies the arguments of a
recurrence by a sort discipline that prevents the recursive result
from re-entering the recurrence position, so that iteration cannot
be nested to produce super-elementary growth. Leivant III raises
the first-order word-recurrence characterizations of the earlier
papers in the series to higher type: `RMRec-omega` is a
higher-order equational system whose object sorts are the base
sort `o` and its `Omega`-shifts, whose universes are all copies of
a single carrier `A` (Leivant III section 2.7), and whose
principal result (Theorem 14) identifies the functions definable
over `A = ℕ` with the Kalmár-elementary functions.

The formalization presents `RMRec-omega` as a multi-sorted Lawvere
theory: a signature of sorted operations (`SortedSig`) over the
ramified types (`RType`), a term layer with clone laws (`Term`),
sorted models with the standard interpretation and its
interpretative setoid (`Interp`), and the generic syntactic
category with finite products `RMRecCat` (`SynCat`). The
elementary-recursive functions are the reference class, taken from
the adjacent `LawvereERCat` (see the
[K_sim hierarchy and ER ↔ K_sim_2 equivalence](lawvere-er-ksim.md)
area). The two directions of the characterization follow the
literature's proof routes (spec section 1.2, transcription-only
policy):

- Definability (the machine route, Leivant III section 6.2): an
  elementary-recursive morphism is compiled to a register machine
  and its runtime bound is put into Leivant's clock format, and
  Lemma 6 exhibits the machine's computation as a ramified realizer
  between object-sort contexts.
- Soundness (the normalization route, Leivant III section 6.3): a
  ramified identifier is translated to the object-sorted
  applicative calculus `RλMR_o^ω` (Proposition 7) and then to the
  simply-typed calculus `1λ(A)`, whose normalization (Lemma 12) is
  realized as an elementary deterministic normalizer on term codes
  and landed in `LawvereERCat`.

## Modules

Each source module below has a mirrored test module of the same
name under `GebLeanTests/Ramified/`. The directory index is
[`GebLean/Ramified.lean`](../../GebLean/Ramified.lean).

### The generic core

- [`GebLean/Ramified/AlgSig.lean`](../../GebLean/Ramified/AlgSig.lean)
  — free-algebra signatures `AlgSig` and the free algebra
  `FreeAlg`, with the numeric reading `natToFreeAlg` / `freeAlgToNat`
  of the standard carrier `FreeAlg natAlgSig`.
- [`GebLean/Ramified/SortedSig.lean`](../../GebLean/Ramified/SortedSig.lean)
  — multi-sorted signatures with the constructor summand.
- [`GebLean/Ramified/Term.lean`](../../GebLean/Ramified/Term.lean)
  — the sorted term layer with its clone laws.
- [`GebLean/Ramified/Interp.lean`](../../GebLean/Ramified/Interp.lean)
  — sorted models, the standard interpretation, and the
  interpretative setoid.
- [`GebLean/Ramified/SynCat.lean`](../../GebLean/Ramified/SynCat.lean)
  — the generic syntactic category with finite products `RMRecCat`.

### The higher-order system

- [`GebLean/Ramified/RType.lean`](../../GebLean/Ramified/RType.lean)
  — the ramified types, their object sorts, and the tower predicate
  `RType.IsTower`.
- [`GebLean/Ramified/HigherOrder.lean`](../../GebLean/Ramified/HigherOrder.lean)
  — the higher-order presentation `higherOrder` with its
  schema-generated identifiers `RIdent`.
- [`GebLean/Ramified/OmegaShift.lean`](../../GebLean/Ramified/OmegaShift.lean)
  — the sort-level `omegaShift` and the coercion `kappaHat`.
- [`GebLean/Ramified/Examples.lean`](../../GebLean/Ramified/Examples.lean)
  — the section 2.4 example ladder over the `1 + X` word algebra
  (`kappa`, `delta`, addition, multiplication, the second-order
  exponential `ramExp`, the `2_m` ladder `ramTwoPow`, the size
  function), each with its interpretation lemma.

### Algebra instances and first-order sub-theories

- [`GebLean/Ramified/Algebras.lean`](../../GebLean/Ramified/Algebras.lean)
  — the canonical instances `natAlgSig` / `binWordAlgSig` /
  `treeAlgSig`, the numeric equivalence `natFreeAlgEquiv :
  FreeAlg natAlgSig ≃ ℕ`, and the signature morphisms `AlgSigHom`
  with their carrier transport `freeAlgMap` and image-point
  naturality.
- The first-order sub-theory lives on the polynomial-functor stack,
  in
  [`GebLean/Ramified/Polynomial/FirstOrder.lean`](../../GebLean/Ramified/Polynomial/FirstOrder.lean);
  see the inventory entry under [Ramified recurrence on the
  polynomial-functor stack](#ramified-recurrence-on-the-polynomial-functor-stack-gebleanramifiedpolynomial).

### Definability (`GebLean/Ramified/Definability/`)

The directory index is
[`GebLean/Ramified/Definability.lean`](../../GebLean/Ramified/Definability.lean).

- [`GebLean/Ramified/Definability/Simultaneous.lean`](../../GebLean/Ramified/Definability/Simultaneous.lean)
  — the case function `ramCase`, the destructor `ramDstr`, and the
  selector `chooseIdent`, the building blocks of Lemma 2's
  reduction of simultaneous recurrence to plain recurrence.
- [`GebLean/Ramified/Definability/Flat.lean`](../../GebLean/Ramified/Definability/Flat.lean)
  — the destructor/case summand generic in the algebra, its
  flat-recurrence realization (Lemma 1), and the O-variant
  presentation `RMRec_o^omega`.
- [`GebLean/Ramified/Definability/Bounds.lean`](../../GebLean/Ramified/Definability/Bounds.lean)
  — the natural-number inequalities converting the ER runtime tower
  bound into Leivant's clock format `c · 2_q(sz)` (Lemma 6
  hypothesis).
- [`GebLean/Ramified/Definability/Ladder.lean`](../../GebLean/Ramified/Definability/Ladder.lean)
  — the section 2.4 numeric family generalized from the base sort
  `o` to an arbitrary object sort, aligned with `objToNat` and
  `GebLean.tower`.
- [`GebLean/Ramified/Definability/Machine.lean`](../../GebLean/Ramified/Definability/Machine.lean)
  — Lemma 6's machine-state simulation: the zero-test URM tracked by
  the simultaneous family over program-counter and register
  components.
- [`GebLean/Ramified/Definability/Top.lean`](../../GebLean/Ramified/Definability/Top.lean)
  — the object-sort contexts `ObjCtx`, the numeric denotation
  `ramifiedDenotation`, and the definability families
  `erMor_ramified_definable` / `erMorN_ramified_definable`.

### Soundness (`GebLean/Ramified/Soundness/`)

The directory index is
[`GebLean/Ramified/Soundness.lean`](../../GebLean/Ramified/Soundness.lean).

- [`GebLean/Ramified/Soundness/Applicative.lean`](../../GebLean/Ramified/Soundness/Applicative.lean)
  — the object-sorted applicative λ-calculus `RλMR_o^ω` as a
  binding signature, and Proposition 7's soundness arm `(1) ⟹ (4)`.
- [`GebLean/Ramified/Soundness/OneLambda.lean`](../../GebLean/Ramified/Soundness/OneLambda.lean)
  — the simply-typed calculus `1λ(A)` with its congruence-closed
  reduction.
- [`GebLean/Ramified/Soundness/BarRep.lean`](../../GebLean/Ramified/Soundness/BarRep.lean)
  — the Berarducci-Böhm representation of free-algebra values as
  closed `1λ(A)` terms.
- [`GebLean/Ramified/Soundness/Represents.lean`](../../GebLean/Ramified/Soundness/Represents.lean)
  — the logical relation `Represents` tying an `RλMR_o^ω` term to
  the `1λ(A)` term computing its value.
- [`GebLean/Ramified/Soundness/Normalization.lean`](../../GebLean/Ramified/Soundness/Normalization.lean)
  — Lemma 12's normalization bound from the type-order measure
  `RType.ord`.
- [`GebLean/Ramified/Soundness/OneLambdaEval.lean`](../../GebLean/Ramified/Soundness/OneLambdaEval.lean)
  — the standard evaluator `oneEval` of `1λ(A)` with its renaming-
  and substitution-fusion laws.
- [`GebLean/Ramified/Soundness/DetStep.lean`](../../GebLean/Ramified/Soundness/DetStep.lean)
  — the total computable deterministic reduction step `detStep`.
- [`GebLean/Ramified/Soundness/CodeTm.lean`](../../GebLean/Ramified/Soundness/CodeTm.lean)
  — the Gödel coding of the ramified types and `1λ(A)` terms, with
  the order-off-code lemma `ordCode_codeRType`.
- [`GebLean/Ramified/Soundness/CodeNormalizer.lean`](../../GebLean/Ramified/Soundness/CodeNormalizer.lean)
  — the code-level substitution `subCode` and weakening `shiftCode`,
  the numeric images of the binder operations under `codeTm`.
- [`GebLean/Ramified/Soundness/NormStepER.lean`](../../GebLean/Ramified/Soundness/NormStepER.lean)
  — the deterministic normalizer step `normStep` realized as an
  `ERMor1` morphism, with its evaluation lemmas.
- [`GebLean/Ramified/Soundness/Collapse.lean`](../../GebLean/Ramified/Soundness/Collapse.lean)
  — the first-order syntactic category `SynCatFO`, its denotation
  `collapseDenotation`, and the faithful soundness functor
  `collapseFunctor : SynCatFO ⥤ LawvereERCat`.

### Characterization

- [`GebLean/Ramified/Characterization.lean`](../../GebLean/Ramified/Characterization.lean)
  — the assembled definability statement `ramified_definability`,
  the K-valued soundness functor `collapseKFunctor` with its
  faithfulness, and the transferred `ramified_definability_kSim`.

### Ramified recurrence on the polynomial-functor stack (`GebLean/Ramified/Polynomial/`)

A reimplementation of the generic-core carrier and the ramified
types on the vendored `geb-mathlib` `SlicePFunctor` stack, connected
to the modules above by the generic bridge
`GebLean/PolyBridge/` (see
[polynomial / W- / M-types and PFunctors](polynomial-functors.md)).
The directory index is
[`GebLean/Ramified/Polynomial.lean`](../../GebLean/Ramified/Polynomial.lean).

- [`GebLean/Ramified/Polynomial/FreeAlg.lean`](../../GebLean/Ramified/Polynomial/FreeAlg.lean)
  — the free algebra `FreeAlg'` on the slice `W`-type and its native
  recurrence `FreeAlg'.recurse`, the bridge equivalence
  `freeAlgSliceEquiv : FreeAlg' A ≃ FreeAlg A`, and the numeric
  carrier equivalence `natFreeAlgEquiv' : FreeAlg' natAlgSig ≃ ℕ`.
- [`GebLean/Ramified/Polynomial/RType.lean`](../../GebLean/Ramified/Polynomial/RType.lean)
  — the ramified types `RType'` and their operations reimplemented
  on `FreeAlg'`, and the bridge equivalence `rTypeSliceEquiv : RType'
  ≃ RType`, with a compatibility lemma per operation across it.
- [`GebLean/Ramified/Polynomial/Term.lean`](../../GebLean/Ramified/Polynomial/Term.lean)
  — the sorted term layer `Tm'` on the slice free monad
  `SlicePFunctor.FreeM`, with `var`, `op`, and `subst` (the free
  monad's `pure`, `node`, and `bind`) and the clone laws as instances
  of the monad laws, and the bridge equivalence `tmSliceEquiv : Tm' sig
  Γ s ≃ Tm sig Γ s`, with a compatibility lemma for `var`, `op`, and
  `subst` across it.
- [`GebLean/Ramified/Polynomial/Interp.lean`](../../GebLean/Ramified/Polynomial/Interp.lean)
  — primed evaluation `Tm'.eval` by the slice free monad's fold, the
  interpretative setoid `interpQuotRel'`, and the evaluation
  agreement `tmSliceEquiv_eval` across the term bridge.
- [`GebLean/Ramified/Polynomial/SynCat.lean`](../../GebLean/Ramified/Polynomial/SynCat.lean)
  — the primed syntactic category `SynCat'` over the primed term
  layer, with context concatenation as chosen finite products.
- [`GebLean/Ramified/Polynomial/SynCatEquiv.lean`](../../GebLean/Ramified/Polynomial/SynCatEquiv.lean)
  — the term-layer equivalence `synCatSliceEquiv : SynCat' P
  (interpQuotRel' P) ≌ SynCat P (interpQuotRel P)`, the identity on
  objects and `tmSliceEquiv` componentwise on morphisms.
- [`GebLean/Ramified/Polynomial/Ident.lean`](../../GebLean/Ramified/Polynomial/Ident.lean)
  — the primed schema identifiers `RIdent'` as a fiber of the slice
  `W`-type, with the application signature, the curried arrow sort,
  and the denotation `RIdent'.interp` by `SlicePFunctor.W.elim`.
- [`GebLean/Ramified/Polynomial/HigherOrder.lean`](../../GebLean/Ramified/Polynomial/HigherOrder.lean)
  — the primed higher-order presentation `higherOrder'`, its
  syntactic category `RMRecCat'`, and the identifier morphism
  `identHom'`.
- [`GebLean/Ramified/Polynomial/IdentEquiv.lean`](../../GebLean/Ramified/Polynomial/IdentEquiv.lean)
  — the identifier bridge `identSliceEquiv`, assembled from a
  container isomorphism of the two identifier signature
  endofunctors, base change, and the initial-algebra comparison.
- [`GebLean/Ramified/Polynomial/HigherOrderEquiv.lean`](../../GebLean/Ramified/Polynomial/HigherOrderEquiv.lean)
  — the presentation equivalence `higherOrderPresEquiv` and the
  category equivalence `rmRecCatSliceEquiv : RMRecCat' A ≌ RMRecCat
  A`.
- [`GebLean/Ramified/Polynomial/FirstOrder.lean`](../../GebLean/Ramified/Polynomial/FirstOrder.lean)
  — the first-order identifier predicate `RIdent'.FirstOrder`, the
  sub-theory presentation `firstOrderPresentation`, and the
  inclusion functor `foInclusion` into the host `RMRecCat'`.
- [`GebLean/Ramified/Polynomial/Collapse.lean`](../../GebLean/Ramified/Polynomial/Collapse.lean)
  — the primed first-order syntactic category `SynCatFO'`, its
  numeric denotation `collapseDenotation'`, the restriction
  equivalence `synCatFOSliceEquiv : SynCatFO' ≌ SynCatFO`, and the
  denotation agreement `collapseDenotation_sliceEquiv` across it.
- [`GebLean/Ramified/Polynomial/Characterization.lean`](../../GebLean/Ramified/Polynomial/Characterization.lean)
  — the primed soundness functors `collapseFunctor'` and
  `collapseKFunctor'` with their faithfulness, and the transferred
  endpoints `ramified_definability'` and
  `ramified_definability_kSim'`.

## Statement inventory

The characterization is delivered as the pair of statements
constituting the denotational form of Leivant III Theorem 14 items
(1)-(2), relative to `LawvereERCat` as the reference definition of
elementary.

- `collapseFunctor : SynCatFO ⥤ LawvereERCat` with
  `instance : collapseFunctor.Faithful`
  ([`Soundness/Collapse.lean`](../../GebLean/Ramified/Soundness/Collapse.lean),
  Phase 6.5) — the soundness functor from the first-order syntactic
  category to the elementary-recursive Lawvere category, faithful.
- `ramified_definability`
  ([`Characterization.lean`](../../GebLean/Ramified/Characterization.lean))
  — for every `f : n ⟶ m` in `LawvereERCat` there exist an
  object-sort context `Γ : ObjCtx n` and a morphism
  `g : Γ.toSynCatFO ⟶ (oCtx m).toSynCatFO` whose collapse
  denotation, read across the arity identifications by
  `arityCongr`, equals `f.interp`.
- `collapseKFunctor : SynCatFO ⥤ LawvereKSimDCat 2` with
  `instance : collapseKFunctor.Faithful`
  ([`Characterization.lean`](../../GebLean/Ramified/Characterization.lean))
  — the K-valued soundness functor `collapseFunctor ⋙ erToKFunctor`,
  faithful as a composite of faithful functors.
- `ramified_definability_kSim`
  ([`Characterization.lean`](../../GebLean/Ramified/Characterization.lean))
  — the same existential for every `f` in `LawvereKSimDCat 2`, with
  the `K^sim` interpretation `f.hom.interp` in place of `f.interp`,
  transferred across `erKSimEquiv` through `kToERFunctor_map_interp`.

The same pair is stated over the polynomial-functor stack, in
[`Polynomial/Characterization.lean`](../../GebLean/Ramified/Polynomial/Characterization.lean),
with no part of the elementary-definability or soundness argument
redone: `collapseFunctor' : SynCatFO' ⥤ LawvereERCat` and
`collapseKFunctor' : SynCatFO' ⥤ LawvereKSimDCat 2` are the
composites of the restriction equivalence `synCatFOSliceEquiv` with
`collapseFunctor` and `collapseKFunctor`, faithful as composites,
and `ramified_definability'` / `ramified_definability_kSim'` read
the legacy witnesses back through that equivalence's fully faithful
preimage, with `collapseDenotation'` and the primed object-sort
contexts `ObjCtx'` in place of their legacy counterparts.

Both directions are existential and denotational. The
quantification in `ramified_definability` ranges over all
object-sort contexts, beyond the tower sorts, as the source
requires (Leivant III Lemma 6's realizer takes its input at an
object sort and the section-2.4(1) coercions run downward only).
The statement is not fullness of `collapseFunctor`: sort-uniform
hom-sets are strictly smaller than elementary. The categorical
packaging of the two statements (spec open question 7) is not
asserted: no equivalence of categories between `SynCatFO` and
`LawvereERCat`, and no fullness of `collapseFunctor` or
`collapseKFunctor`, is claimed.

## Deferred and future work

Mathematical future work is catalogued in the spec:
[deferred and future work](../superpowers/specs/2026-07-01-ramified-recurrence-approaches-design.md)
(section 9) and
[open questions](../superpowers/specs/2026-07-01-ramified-recurrence-approaches-design.md)
(section 10). Principal items: the equational presentation and its
soundness against the standard interpretation built here; the
first-order complexity characterizations (linear space, polynomial
time); the applicative calculi `RλMR-omega` as goals (Theorem 14
items (3)-(5)); the arbitrary-infinite-free-algebra corollary via a
categorical equivalence internal to the ramified framework; ramified
corecursion over M-types; the `Omega`-shift endofunctor status (open
question 3); and the categorical packaging of section 6.1 (open
question 7).

Refactoring items deferred at completion, none blocking: three
private copies of the child-descent inequality (natural home the
public `argCode_lt_of_shape_one` family in `CodeTm.lean`); a
`pair_le_pair` duplicate of a private lemma in
[`GebLean/PLang/BTPair.lean`](../../GebLean/PLang/BTPair.lean);
`clockERN` / `budgetERN` duplicating the unary composite trees;
`interp_comp_singleton` / `interp_comp_three` and
`natBProd_le_one_of_body_le_one_of_lt` awaiting a second consumer to
promote or home; the pure-move splits at the `NormStepER.lean`
clocked-iteration seam and for `sourceApps`; the Phase-5-subject
helpers homed in `Collapse.lean` (`ramifiedDenotation_id` / `_comp`
/ `_apply` / `_injective`, `objFromNat_objToNat`) relocating to
`Definability` / `SynCat`; the `interp_transport_arrow_apply` /
`cast_arrow_apply` unification across `NormStepER.lean` and
`OmegaShift.lean`; the `singletonEnv` migration beside the binding
kit; and a `private`-marking pass over `Collapse.lean`'s file-local
plumbing.

## Dependencies

- The polynomial / W- / M-types and polynomial-functors layer
  supplies the W-type realization of syntax and the Lawvere-theory
  setting; see
  [polynomial / W- / M-types and PFunctors](polynomial-functors.md).
- The elementary-recursive Lawvere category `LawvereERCat`, the
  degree-2 `K^sim` category `LawvereKSimDCat 2`, and the equivalence
  `erKSimEquiv` are the reference targets; see
  [K_sim hierarchy and ER ↔ K_sim_2 equivalence](lawvere-er-ksim.md).
- The indexed binder-substitution kit under `GebLean/Binding/`
  realizes the applicative and simply-typed calculi of the
  soundness route as binding signatures.
- CSLib supplies the URM model used by the definability route; see
  the [CSLib integration](../index.md#cslib) section of the
  documentation index.

## Pointers

Specification and plan (co-evolved on-branch with the code):

- [`docs/superpowers/specs/2026-07-01-ramified-recurrence-approaches-design.md`](../superpowers/specs/2026-07-01-ramified-recurrence-approaches-design.md)
  — the design spec (section 6.1 fixes the statement shape;
  sections 9-10 the deferred items and open questions).
- [`docs/superpowers/plans/2026-07-02-ramified-recurrence-plan.md`](../superpowers/plans/2026-07-02-ramified-recurrence-plan.md)
  — the master plan (Phases 1-7).
- [`docs/superpowers/specs/2026-07-19-ramified-polynomial-design.md`](../superpowers/specs/2026-07-19-ramified-polynomial-design.md)
  and
  [`docs/superpowers/plans/2026-07-19-ramified-polynomial-plan.md`](../superpowers/plans/2026-07-19-ramified-polynomial-plan.md)
  — the design spec and plan for the polynomial-functor-stack
  reimplementation (`GebLean/Ramified/Polynomial/`).
- [`docs/superpowers/specs/2026-07-22-verso-ramified-manual-design.md`](../superpowers/specs/2026-07-22-verso-ramified-manual-design.md)
  and
  [`docs/superpowers/plans/2026-07-22-verso-ramified-manual-plan.md`](../superpowers/plans/2026-07-22-verso-ramified-manual-plan.md)
  — the design spec and plan for the `GebLeanDocs` Verso manual
  (tutorial and reference parts over this area), generated by
  `lake exe geblean-docs`.

## References

- D. Leivant, "Ramified recurrence and computational complexity
  III: Higher type recurrence and elementary complexity", Annals of
  Pure and Applied Logic 96 (1999) 209-229. DOI
  `10.1016/S0168-0072(98)00040-2`.
