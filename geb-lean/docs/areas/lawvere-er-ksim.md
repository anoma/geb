# Lawvere ER, Gödel-T, the K_sim hierarchy, and the ER ≌ K_sim_2 equivalence

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Purpose](#purpose)
- [Mathematical context](#mathematical-context)
- [Modules](#modules)
  - [ER (elementary-recursive) Lawvere category](#er-elementary-recursive-lawvere-category)
  - [K_sim (Tourlakis) Lawvere category](#k_sim-tourlakis-lawvere-category)
  - [Gödel System T](#g%C3%B6del-system-t)
  - [NatBT (binary-tree naturals)](#natbt-binary-tree-naturals)
  - [Tree-ER and tree-Gödel](#tree-er-and-tree-g%C3%B6del)
  - [ER to K_sim compiler and equivalence (`GebLean/LawvereERKSim/`)](#er-to-k_sim-compiler-and-equivalence-gebleanlawvereerksim)
  - [Equivalence assembly and miscellaneous](#equivalence-assembly-and-miscellaneous)
  - [ER and K_sim utility libraries (`GebLean/Utilities/`)](#er-and-k_sim-utility-libraries-gebleanutilities)
- [Alternative formulations](#alternative-formulations)
  - [The Lawvere category of binary-tree naturals: V1 vs. V2](#the-lawvere-category-of-binary-tree-naturals-v1-vs-v2)
  - [K_sim_2 included in ER: majorization vs. direct Szudzik route](#k_sim_2-included-in-er-majorization-vs-direct-szudzik-route)
- [Dependencies](#dependencies)
- [Pointers](#pointers)
- [Provenance](#provenance)

<!-- END doctoc -->

## Purpose

This area packages two classical models of subrecursive
computation as Lawvere categories and proves them equivalent: the
elementary-recursive functions (`LawvereERCat`) and the degree-2
level of Tourlakis's K^sim hierarchy (`LawvereKSimDCat 2`). It
also carries the supporting growth-rate analysis (tower bounds,
polynomial bounds, A-majorants), a Gödel System-T layer, a
tree-native primitive-recursive layer, and the URM machinery that
realises the reverse translation.

## Mathematical context

The elementary-recursive (Kalmár-elementary) functions are the
smallest class containing zero, successor, projections, and
modified subtraction, closed under composition and bounded sum and
product. Tourlakis's K^sim hierarchy stratifies the same universe
by the nesting depth of simultaneous bounded recursion (the `sim`
constructor), with K^sim_2 the level that coincides with the
elementary-recursive functions (Tourlakis, *Theory of
Computation*, Wiley 2012; the equivalence is Corollary 0.1.0.44 at
`n = 2`). Each class is presented here as a Lawvere category: a
category with finite-product structure whose object `n` is the
`n`-fold power of a generic object and whose morphisms `n ⟶ m` are
`m`-tuples of term-level functions of `n` inputs, taken modulo
extensional equality of their standard interpretation in `ℕ`.

The forward inclusion K^sim_2 ⊆ ER is realised by
`kToERFunctor : LawvereKSimDCat 2 ⥤ LawvereERCat`: each K^sim_2
generator is translated to an ER term, and the `sim` constructor
is discharged by majorization — a polynomial bound on the
simultaneous recursion (from Tourlakis A-majorants and a tower
bound) lets the recursion be re-expressed with the bounded
recursion available to ER, with multi-output recursion packed into
a single channel by Szudzik pairing. The reverse inclusion ER ⊆
K^sim_2 is realised by `erToKFunctor : LawvereERCat ⥤
LawvereKSimDCat 2` through URM simulation: an ER term is compiled
to an unlimited-register-machine program (`compileER`), the URM is
simulated by a K^sim_2 morphism (`KSimURMSimulator`), and a
runtime bound (`boundExprK`) supplies the bounded-search budget so
the simulation runs within K^sim_2. The two functors are packaged
as a categorical equivalence `erKSimEquiv : LawvereERCat ≌
LawvereKSimDCat 2`.

The Gödel System-T layer (`GodelTTerm`) and the tree-native ER
layer (`LawvereTreeER` and the tree-Gödel modules) are adjacent
developments: the former is a typed term calculus with reduction
and a structural tower bound, the latter realises ER computation
directly over binary trees using the tree-calculus primitive
recursor and a Gödel numbering of trees.

## Modules

### ER (elementary-recursive) Lawvere category

- [`GebLean/LawvereER.lean`](../../GebLean/LawvereER.lean) — the
  generator inductive `ERMor1` and tuple type `ERMorN`; `natBSum`
  and `natBProd` give the bounded-sum/product semantics.
- [`GebLean/LawvereERQuot.lean`](../../GebLean/LawvereERQuot.lean)
  — the quotient by extensional equality, yielding the category
  `LawvereERCat`.
- [`GebLean/LawvereERInterp.lean`](../../GebLean/LawvereERInterp.lean)
  — the faithful interpretation functor `erInterpFunctor` into
  `Type`, with `erInterpFunctor_not_full` (Ackermann is not ER).
- [`GebLean/LawvereERArith.lean`](../../GebLean/LawvereERArith.lean)
  — derived arithmetic beyond the generators (`ERMor1.expER`).
- [`GebLean/LawvereERBound.lean`](../../GebLean/LawvereERBound.lean)
  — the fixed-height tower bound `ERMor1.exists_lt_tower` on every
  term's interpretation.
- [`GebLean/LawvereERBoundComputable.lean`](../../GebLean/LawvereERBoundComputable.lean)
  — constructive counterpart: a structural `towerHeight` and the
  ER term `ERMor1.towerBound` dominating the interpretation.
- [`GebLean/LawvereERPolynomialBound.lean`](../../GebLean/LawvereERPolynomialBound.lean)
  — the `ERMor1.PolyBound` certificate and its per-constructor
  builders, supplying the polynomial bounds the K-side consumes.
- [`GebLean/LawvereERPrimrec.lean`](../../GebLean/LawvereERPrimrec.lean)
  — `ERMor1.toPrimrec'`, embedding ER terms into mathlib's
  `Nat.Primrec` predicate.
- ER feature modules:
  [`GebLean/LawvereERBool.lean`](../../GebLean/LawvereERBool.lean)
  (`boolNot`/`boolAnd`/`boolEqNat` as `ERMor1` terms with `≤ 1`
  bounds),
  [`GebLean/LawvereERTetration.lean`](../../GebLean/LawvereERTetration.lean)
  (`tetration_not_ER`, the negative result from the tower bound),
  [`GebLean/LawvereERLex.lean`](../../GebLean/LawvereERLex.lean)
  (`ERBoolPred` decidable predicates and equalizer data) and
  [`GebLean/LawvereERDelta.lean`](../../GebLean/LawvereERDelta.lean)
  (the `erDeltaFunctor` into the predicate category).
- [`GebLean/LawvereERNatBTV2Equiv.lean`](../../GebLean/LawvereERNatBTV2Equiv.lean)
  — `erToNatBTV2Functor`, the equivalence of `LawvereERCat` with
  the `m = 0` subcategory of the binary-tree-naturals theory (see
  Alternative formulations).

### K_sim (Tourlakis) Lawvere category

- [`GebLean/LawvereKSim.lean`](../../GebLean/LawvereKSim.lean) —
  the generator inductive `KMor1` (including the `sim`
  simultaneous-recursion constructor) and the finite-product
  combinators on `KMorN`.
- [`GebLean/LawvereKSimInterp.lean`](../../GebLean/LawvereKSimInterp.lean)
  — `KMor1.interp` into `ℕ`, with `simrecVec` the standard
  semantics of `sim` and its agreement with `Nat.simRecVec`.
- [`GebLean/LawvereKSimQuot.lean`](../../GebLean/LawvereKSimQuot.lean)
  and
  [`GebLean/LawvereKSimDCatInterp.lean`](../../GebLean/LawvereKSimDCatInterp.lean)
  — the extensional quotient `KMorNQuo` (the category
  `LawvereKSimDCat`) and its faithful `kInterpFunctor`.
- [`GebLean/LawvereKSimPolynomialBound.lean`](../../GebLean/LawvereKSimPolynomialBound.lean)
  — `KMor1.level0Shape`/`KMor1.linearBound`, the shape and linear
  bound for low-level K^sim morphisms.
- [`GebLean/LawvereKSimMajorization.lean`](../../GebLean/LawvereKSimMajorization.lean)
  — the majorization chain (Tourlakis A-majorants vs. tower
  bounds) bridging K^sim growth to ER-expressible bounds.
- The two routes for K^sim_2 ⊆ ER (see Alternative formulations):
  [`GebLean/LawvereKSimER.lean`](../../GebLean/LawvereKSimER.lean)
  (`kToER` via the structural majorization argument) and
  [`GebLean/LawvereKSimERDirect.lean`](../../GebLean/LawvereKSimERDirect.lean)
  (`kToERDirect` via Szudzik-packed direct simulation).

### Gödel System T

- [`GebLean/LawvereGodelT.lean`](../../GebLean/LawvereGodelT.lean)
  — base types `GodelTBase`, the type syntax `GodelTType`, and its
  `level`.
- [`GebLean/LawvereGodelTTerm.lean`](../../GebLean/LawvereGodelTTerm.lean)
  — the typed term inductive `GodelTTerm` with `interp`, `subst`,
  and `interp_subst`.
- [`GebLean/LawvereGodelTReduces.lean`](../../GebLean/LawvereGodelTReduces.lean)
  — the reduction relation `GodelTTerm.Reduces` with its
  reflexive-transitive `Star` and `Equiv` closures.
- [`GebLean/LawvereGodelTLemma16.lean`](../../GebLean/LawvereGodelTLemma16.lean)
  — the structural tower-bound apparatus (`lh`, `d`, `G`, bracket
  levels) for `GodelTTerm`.

### NatBT (binary-tree naturals)

- V1 family:
  [`GebLean/LawvereNatBT.lean`](../../GebLean/LawvereNatBT.lean)
  (the two-sort theory `NatBTMor1` over `ℕ` and labeled binary
  trees `BTL`),
  [`GebLean/LawvereNatBTQuot.lean`](../../GebLean/LawvereNatBTQuot.lean)
  /
  [`GebLean/LawvereNatBTInterp.lean`](../../GebLean/LawvereNatBTInterp.lean)
  (the category `LawvereNatBTCat` and its faithful interpretation
  functor),
  [`GebLean/LawvereNatBT0.lean`](../../GebLean/LawvereNatBT0.lean)
  (the `m = 0` full subcategory `LawvereNatBT0Cat` with its
  product/terminal structure) and
  [`GebLean/LawvereNatBTBackTrans.lean`](../../GebLean/LawvereNatBTBackTrans.lean)
  (`NatBTMor1.toER`, the fold-free back-translation to ER).
- V2 family:
  [`GebLean/LawvereNatBTV2.lean`](../../GebLean/LawvereNatBTV2.lean)
  (the bottom-up theory `NatBTMor1V2` defined over ER),
  [`GebLean/LawvereNatBTV2Quot.lean`](../../GebLean/LawvereNatBTV2Quot.lean)
  /
  [`GebLean/LawvereNatBTV2Interp.lean`](../../GebLean/LawvereNatBTV2Interp.lean)
  (the category `LawvereNatBTV2Cat` and its faithful interpretation
  functor) and
  [`GebLean/LawvereNatBTV20.lean`](../../GebLean/LawvereNatBTV20.lean)
  (the `m = 0` subcategory `LawvereNatBTV20Cat`).

### Tree-ER and tree-Gödel

- [`GebLean/LawvereTreeER.lean`](../../GebLean/LawvereTreeER.lean)
  — tree-native ER morphisms `TreeMor1` with `foldDepth` and
  `toBTMor1`.
- [`GebLean/LawvereTreeERArith.lean`](../../GebLean/LawvereTreeERArith.lean)
  — tree-syntactic arithmetic (`treeFoldOnCode`, `mutuFoldOnCode`,
  `RegisterMachineRealization`).
- [`GebLean/LawvereTreeERQuot.lean`](../../GebLean/LawvereTreeERQuot.lean)
  /
  [`GebLean/LawvereTreeERInterp.lean`](../../GebLean/LawvereTreeERInterp.lean)
  — the quotient category `TreeERMorNQuo` and its faithful
  `treeErInterpFunctor`.
- [`GebLean/TreeGoedel.lean`](../../GebLean/TreeGoedel.lean) —
  `treeToNat`, the Gödel numbering of trees built from
  `elegantPair`.
- [`GebLean/TreeEqGoedel.lean`](../../GebLean/TreeEqGoedel.lean) —
  `treeEqG`, decidable tree equality via the Gödel encoding.
- [`GebLean/TreeLogic.lean`](../../GebLean/TreeLogic.lean) —
  Boolean logic on trees (`paraElim` parametric eliminator,
  `treeFalse` and friends).

### ER to K_sim compiler and equivalence (`GebLean/LawvereERKSim/`)

- [`GebLean/LawvereERKSim/Compiler.lean`](../../GebLean/LawvereERKSim/Compiler.lean)
  — `URMInstrRaw` and the `compileER` ER → URM compiler with its
  register-bound bookkeeping.
- [`GebLean/LawvereERKSim/Embedding.lean`](../../GebLean/LawvereERKSim/Embedding.lean)
  and
  [`GebLean/LawvereERKSim/Loops.lean`](../../GebLean/LawvereERKSim/Loops.lean)
  — `ProgramEmbedsFragment` and the transfer-loop correctness
  lemmas underpinning the per-constructor proofs.
- [`GebLean/LawvereERKSim/Atoms.lean`](../../GebLean/LawvereERKSim/Atoms.lean),
  [`GebLean/LawvereERKSim/Comp.lean`](../../GebLean/LawvereERKSim/Comp.lean),
  [`GebLean/LawvereERKSim/BSum.lean`](../../GebLean/LawvereERKSim/BSum.lean),
  [`GebLean/LawvereERKSim/BProd.lean`](../../GebLean/LawvereERKSim/BProd.lean)
  — the `compileER_pre_stop_correct_*` correctness theorems, one
  family per ER constructor (atoms, composition, bounded sum,
  bounded product).
- [`GebLean/LawvereERKSim/Top.lean`](../../GebLean/LawvereERKSim/Top.lean)
  — the assembled `compileER_pre_stop_correct` and
  `compileER_runFor` end-to-end compiler correctness.
- [`GebLean/LawvereERKSim/RuntimeBound.lean`](../../GebLean/LawvereERKSim/RuntimeBound.lean)
  — `boundExprKParams`/`boundExprK` and
  `boundExprKParams_dominates`, the K-side runtime budget for the
  simulation.
- [`GebLean/LawvereERKSim/ErToK.lean`](../../GebLean/LawvereERKSim/ErToK.lean)
  /
  [`GebLean/LawvereERKSim/ErToKFunctor.lean`](../../GebLean/LawvereERKSim/ErToKFunctor.lean)
  — `erToK`/`erToKN` (single- and multi-output translators) and the
  functor data `erToKFunctor_map`, with level and interpretation
  agreement.
- [`GebLean/LawvereERKSim/Equivalence.lean`](../../GebLean/LawvereERKSim/Equivalence.lean)
  — the round-trip isomorphisms and the packaged equivalence
  `erKSimEquiv : LawvereERCat ≌ LawvereKSimDCat 2`.
- [`GebLean/LawvereERKSim.lean`](../../GebLean/LawvereERKSim.lean)
  — re-export aggregator for the `LawvereERKSim/` modules; no
  declarations of its own.

### Equivalence assembly and miscellaneous

- [`GebLean/LayeredEquivalence.lean`](../../GebLean/LayeredEquivalence.lean)
  — a layered copresheaf/dependent-type equivalence (objects,
  then morphisms) over a small judgment category; adjacent
  infrastructure rather than ER/K^sim content (see Pointers).
- [`GebLean/NatElegantPair.lean`](../../GebLean/NatElegantPair.lean)
  — Szudzik's elegant pairing `elegantPair` and `natSquare`, the
  packing primitive reused for multi-output recursion and tree
  Gödel numbering.

### ER and K_sim utility libraries (`GebLean/Utilities/`)

- ER-side arithmetic and bounds:
  [`GebLean/Utilities/ERArith.lean`](../../GebLean/Utilities/ERArith.lean)
  (ER-term arithmetic helpers),
  [`GebLean/Utilities/ERTreeArith.lean`](../../GebLean/Utilities/ERTreeArith.lean)
  (tree-encoded arithmetic),
  [`GebLean/Utilities/ERAMajorants.lean`](../../GebLean/Utilities/ERAMajorants.lean)
  (Tourlakis A-majorant functions),
  [`GebLean/Utilities/ERPackedBound.lean`](../../GebLean/Utilities/ERPackedBound.lean)
  (bounds on Szudzik-packed values),
  [`GebLean/Utilities/ERSimultaneousBoundedRec.lean`](../../GebLean/Utilities/ERSimultaneousBoundedRec.lean)
  (simultaneous bounded recursion in ER) and
  [`GebLean/Utilities/ERTupling.lean`](../../GebLean/Utilities/ERTupling.lean)
  (ER-level tupling).
- K-side arithmetic and simulation:
  [`GebLean/Utilities/KArith.lean`](../../GebLean/Utilities/KArith.lean)
  (the K^sim arithmetic library, e.g. `KMor1.natK`),
  [`GebLean/Utilities/KSimSzudzikSimrec.lean`](../../GebLean/Utilities/KSimSzudzikSimrec.lean)
  (Szudzik-packed K^sim simultaneous recursion) and
  [`GebLean/Utilities/KSimURMSimulator.lean`](../../GebLean/Utilities/KSimURMSimulator.lean)
  (`KMor1.simulate`, the K^sim_2 simulation of the URM).
- URM and register-machine machinery:
  [`GebLean/Utilities/RegisterMachine.lean`](../../GebLean/Utilities/RegisterMachine.lean)
  and
  [`GebLean/Utilities/ZeroTestURM.lean`](../../GebLean/Utilities/ZeroTestURM.lean)
  (the unlimited-register-machine model and its zero-test kernel).
- Generic packing, recursion, and growth helpers:
  [`GebLean/Utilities/SzudzikSeq.lean`](../../GebLean/Utilities/SzudzikSeq.lean)
  (Szudzik sequence packing),
  [`GebLean/Utilities/Tupling.lean`](../../GebLean/Utilities/Tupling.lean)
  (generic tupling),
  [`GebLean/Utilities/SimRec.lean`](../../GebLean/Utilities/SimRec.lean)
  (`Nat.simRecVec`, the reference simultaneous recursor),
  [`GebLean/Utilities/Tower.lean`](../../GebLean/Utilities/Tower.lean)
  (the iterated-exponential `tower`) and
  [`GebLean/Utilities/ComputationalComplexity.lean`](../../GebLean/Utilities/ComputationalComplexity.lean)
  (shared complexity/bound lemmas).

## Alternative formulations

### The Lawvere category of binary-tree naturals: V1 vs. V2

There is a single concept here — a two-sort Lawvere theory whose
sorts are the naturals `ℕ` and labeled binary trees, with the
`m = 0` subcategory intended to recover the elementary-recursive
naturals. The repository contains two formulations of it,
artifacts of searching for a preferred specific construction.

- The V1 formulation
  ([`GebLean/LawvereNatBT.lean`](../../GebLean/LawvereNatBT.lean)
  and siblings) defines the morphism inductive `NatBTMor1`
  top-down, with its own tree-fold generators, and back-translates
  to ER via
  [`GebLean/LawvereNatBTBackTrans.lean`](../../GebLean/LawvereNatBTBackTrans.lean).
- The V2 formulation
  ([`GebLean/LawvereNatBTV2.lean`](../../GebLean/LawvereNatBTV2.lean)
  and siblings) defines `NatBTMor1V2` bottom-up directly over ER
  terms, so the equivalence with ER (proved on the `m = 0`
  subcategory in
  [`GebLean/LawvereERNatBTV2Equiv.lean`](../../GebLean/LawvereERNatBTV2Equiv.lean))
  is immediate from the construction.

Both formulations carry the same quotient/interpretation/`m = 0`
scaffolding; they differ only in whether the tree morphisms are
primitive (V1) or defined over ER (V2).

### K_sim_2 included in ER: majorization vs. direct Szudzik route

There is a single inclusion — every K^sim_2 morphism is
elementary-recursive — formulated by two routes.

- The structural route
  ([`GebLean/LawvereKSimER.lean`](../../GebLean/LawvereKSimER.lean),
  `kToER`) discharges the `sim` constructor by majorization: a
  tower/polynomial bound on the simultaneous recursion lets it be
  re-expressed with ER's bounded recursion, with the bound proved
  separately (`kToER_simrec_dominates`).
- The direct route
  ([`GebLean/LawvereKSimERDirect.lean`](../../GebLean/LawvereKSimERDirect.lean),
  `kToERDirect`) packs the multi-output simultaneous recursion
  into a single channel by Szudzik pairing and simulates it
  directly, using the packed-bound utilities.

The two translators agree on interpretation; the route taken
affects only how the `sim` constructor's bound is obtained.

## Dependencies

- The polynomial / W- / M-types and polynomial-functors layer
  supplies the Lawvere-categorical setting (finite-product
  categories of term-functions); see the
  [polynomial / W- / M-types and PFunctors](polynomial-functors.md)
  section of the documentation index.
- The tree-calculus phase-2 layer supplies the primitive-recursive
  substrate used by
  [`GebLean/LawvereTreeER.lean`](../../GebLean/LawvereTreeER.lean)
  and the tree-Gödel modules; see the
  [tree calculus phase 2](tree-calculus.md)
  section of the documentation index.
- CSLib is a cross-cutting dependency: the URM machinery behind
  `erToKFunctor` consumes CSLib's computability formalisations; see
  the [CSLib integration](../index.md#cslib) section of
  the documentation index.

## Pointers

Research notes (relocated under `docs/research/`):

- [`docs/research/lawvere-elementary-recursive.md`](../research/lawvere-elementary-recursive.md)
  — the elementary-recursive Lawvere category.
- [`docs/research/lawvere-k-sim-hierarchy.md`](../research/lawvere-k-sim-hierarchy.md)
  — Tourlakis's K^sim hierarchy as a Lawvere category.
- [`docs/research/2026-04-30-ksim-polynomial-bound-references.md`](../research/2026-04-30-ksim-polynomial-bound-references.md)
  — the polynomial-bound literature references (Tourlakis 2012,
  elementary-recursive growth bounds).
- [`docs/research/2026-05-02-er-ksim2-equiv-via-urm-master-design.md`](../research/2026-05-02-er-ksim2-equiv-via-urm-master-design.md)
  — the master design for the ER ≌ K^sim_2 equivalence via URM
  simulation, with the Tourlakis and Wagner-Wong citations.
- [`docs/research/tree-calculus.md`](../research/tree-calculus.md)
  — the tree-calculus substrate underlying `LawvereTreeER`.

Design specs (under `docs/superpowers/specs/`):

- [`docs/superpowers/specs/2026-05-02-step-1-er-tupling-design.md`](../superpowers/specs/2026-05-02-step-1-er-tupling-design.md),
  [`docs/superpowers/specs/2026-05-03-step-2-er-simultaneous-bounded-rec-design.md`](../superpowers/specs/2026-05-03-step-2-er-simultaneous-bounded-rec-design.md),
  [`docs/superpowers/specs/2026-05-03-step-3-er-tourlakis-A-majorants-design.md`](../superpowers/specs/2026-05-03-step-3-er-tourlakis-A-majorants-design.md)
  — the ER-side bound infrastructure (tupling, simultaneous
  bounded recursion, A-majorants).
- [`docs/superpowers/specs/2026-05-03-step-4-ksim-majorization-design.md`](../superpowers/specs/2026-05-03-step-4-ksim-majorization-design.md),
  [`docs/superpowers/specs/2026-05-03-step-5-ksim-to-er-functor-design.md`](../superpowers/specs/2026-05-03-step-5-ksim-to-er-functor-design.md)
  — K^sim majorization and the `kToERFunctor` (K^sim_2 ⊆ ER).
- [`docs/superpowers/specs/2026-05-05-karith-design.md`](../superpowers/specs/2026-05-05-karith-design.md)
  — the KArith library.
- [`docs/superpowers/specs/2026-05-16-er-to-k-via-cslib-urm-design.md`](../superpowers/specs/2026-05-16-er-to-k-via-cslib-urm-design.md)
  — the master ER → K spec (tasks T1-T4) via CSLib URM
  simulation.
- [`docs/superpowers/specs/2026-05-21-step-t3-urm-to-ksim-simulator-design.md`](../superpowers/specs/2026-05-21-step-t3-urm-to-ksim-simulator-design.md),
  [`docs/superpowers/specs/2026-05-22-step-t4-runtime-bound-design.md`](../superpowers/specs/2026-05-22-step-t4-runtime-bound-design.md),
  [`docs/superpowers/specs/2026-05-25-step-t5-equivalence-design.md`](../superpowers/specs/2026-05-25-step-t5-equivalence-design.md)
  — the URM-to-K^sim simulator (T3), runtime bound (T4), and
  packaged equivalence (T5).

The
[K_sim hierarchy and ER <-> K_sim_2 equivalence](../index.md)
section of the documentation index records the established
narrative, including the axiom envelope and the assembly of
`erKSimEquiv`.

## Provenance

Time-boxed novelty search, 2026-05-31, scope: mathlib (leansearch
/ loogle), then the cited literature; conservative — "no prior
formalization found" where the search was inconclusive.

- ER Lawvere category (`LawvereER*`, `LawvereERKSim/`'s ER side):
  the elementary-recursive functions are standard
  (Kalmár; Tourlakis, *Theory of Computation*, Wiley 2012). The
  function class and its tower bound are known mathematics;
  presenting them as a Lawvere category and proving the
  ER-specific results (`erInterpFunctor_not_full`,
  `tetration_not_ER`) in Lean is, to the search, a first machine
  checked formalization — category 2 for the mathematics, with the
  Lawvere packaging plausibly novel (category 1, `unverified`).
- K^sim hierarchy (`LawvereKSim*`): the K^sim hierarchy and the
  level-2 coincidence with ER are Tourlakis 2012 (Corollary
  0.1.0.44 at `n = 2`). Known mathematics; no prior Lean
  formalization of the hierarchy or its Lawvere packaging found —
  category 2 for the theorem, the categorical packaging category 1
  (`unverified`).
- ER ≌ K^sim_2 categorical equivalence (`erKSimEquiv`,
  `kToERFunctor`/`erToKFunctor`): the set-level equality of the two
  function classes is Tourlakis 2012. Casting it as a categorical
  equivalence of Lawvere categories is plausibly novel — category
  1 (`unverified`); the underlying URM-simulation argument
  (Wagner-Wong; Cutland, *Computability*, CUP 1980) is known
  mathematics, first Lean formalization in this packaging
  (category 2).
- Gödel System T (`LawvereGodelT*`): System T is standard (Gödel
  1958; the level/tower analysis follows Beckmann-Weiermann).
  Known mathematics; the typed-term formalization with reduction
  here found no prior Lean equivalent at the searched scope —
  category 2.
- Tree-native ER and tree-Gödel (`LawvereTreeER*`, `TreeGoedel`,
  `TreeEqGoedel`, `TreeLogic`, `NatElegantPair`): elementary
  recursion realised over binary trees via the tree-calculus
  primitive recursor and a Gödel numbering built from Szudzik's
  pairing (Szudzik, *An Elegant Pairing Function*, 2006). The
  pairing function and ER are known mathematics; the tree-native
  ER category and tree Gödel numbering are plausibly novel —
  category 1 (`unverified`), built on category-2 components.
- NatBT theories (`LawvereNatBT*`, `LawvereNatBTV2*`): the
  two-sort Lawvere theory of naturals and binary trees is a
  bespoke construction of this development — category 1
  (`unverified`); the `m = 0` equivalence with ER is proved
  internally.
- Utility libraries (`GebLean/Utilities/`): standard arithmetic,
  recursion, packing, and register-machine machinery (Szudzik
  pairing, simultaneous recursion, the URM model). Known
  mathematics, supporting infrastructure for the above; category 2
  where any single declaration is of independent interest,
  otherwise plumbing.
