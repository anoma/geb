# Adversarial review 1: Phase C inter-definability sub-plan

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Blockers](#blockers)
- [Majors](#majors)
- [Minors](#minors)
- [Nits](#nits)
- [Verified without defect](#verified-without-defect)
- [Disposition](#disposition)
- [Overall](#overall)

<!-- END doctoc generated TOC -->

Round 1, 2026-07-20. One fresh-context reviewer (declaration
existence, internal consistency, constraint compliance, mathlib
upstream guides re-fetched, mathematical soundness, placeholder scan)
against source at branch `feat/ramified-poly-er`, covering both the
design (`../specs/2026-07-20-ramified-poly-er-design.md`) and the
sub-plan (`2026-07-19-ramified-poly-er-subplan.md`).

## Blockers

None.

## Majors

- M1 (design s6; plan C.8, C.9, C.13, C.19). `List.get_map`, cited as
  a consumed lemma for the reindexing transports, does not exist in
  this toolchain (core has only `List.getElem_map`; the repo already
  works around this with the bespoke `barTy_get_map` in
  `GebLean/Ramified/Soundness/Represents.lean`). Fix: state a shared
  `get`-of-`map` helper in Task C.8 (via `List.get_eq_getElem` and
  `List.getElem_map`) and cite it everywhere the transports need it.
- M2 (design s3; plan C.12). `freeAlgSliceEquiv_recurse` is assigned
  to `GebLean/Ramified/Polynomial/FreeAlg.lean` with proof by
  `FreeAlg'.induction`, but `FreeAlg'.induction` is declared
  downstream in `GebLean/Ramified/Polynomial/RType.lean`, which
  imports `FreeAlg.lean` — the assigned host cannot use the stated
  proof device. Fix: host the new agreement lemmas in
  `Polynomial/RType.lean`.
- M3 (plan, coverage of design s12). No plan task touches `TODO.md`,
  which the design lists as a deliverable. Reviewer could not see
  that the porting record is already committed on this branch (the
  `doc(todo)` commit preceding the sub-plan). Fix: annotate design
  s12 with the delivery status; no plan task needed.
- M4 (both, systematic). The documents disagree on the
  signature-translation names: design `tmMapSigEquiv` /
  `tmMapSig_eval` / `presentationSynCatEquiv` / (in two residual
  spots) `SortedSig.Equiv` versus plan `SortedSigEquiv.tmMap` /
  `.tmEquiv` / `PresentationEquiv.tmMap_eval` /
  `PresentationEquiv.synCatEquiv`; the plan's own Global constraints
  and C.1 Step 3 use the design's names, which no task produces.
  Fix: align on the plan's namespaced names in both documents.

## Minors

- m1 (plan C.16 Step 3). `rTypeInterpCongr` is produced nowhere; the
  congruence is Task C.12's `RType.interpCongr`. Fix: reference
  C.12's output.
- m2 (design s7 versus plan C.2). W-equivalence orientation
  disagrees: design `(reindex e F).W ≃ F.W`, plan
  `F.W ≃ (reindex e F).W`. Fix: align on the plan's orientation
  (the fiber form C.13 consumes).
- m3 (design s10 versus plan C.18). The design claims the mathlib
  full-subcategory route "is pinned in the sub-plan"; the sub-plan
  defers it to the executor with a recording step. Fix: correct the
  design's claim to match.
- m4 (plan C.18). `ObjectProperty.FullSubcategory.lift` is
  misqualified; the mathlib declaration is `ObjectProperty.lift`.
  Fix the name.
- m5 (plan C.2 Step 1). `Equiv.not` does not exist; the declaration
  is `Equiv.boolNot` (C.1 and C.8 already use it). Fix the spelling.
- m6 (plan, commit blocks). Nine of eighteen commit messages exceed
  72 characters measured as whole first lines. Fix: trim to at most
  72 and state the whole-line measure in the Global constraints.
- m7 (design s11; plan Global constraints versus C.12).
  `RType.interpCongr` is a Type-valued legacy-side `PolyFix.ind`
  elimination, but the `PolyFix.ind` whitelist enumerations in both
  documents omit it. Fix: add it to both enumerations.

## Nits

- n1 (design s9; plan C.17). `Tm'.towerSorts` and `RIdent'.shapeFO`
  are `Prop`-valued definitions in `lowerCamelCase`; mathlib names
  `Prop`-valued definitions in `UpperCamelCase` (compare
  `RIdent'.FirstOrder` in the same module). The legacy precedent is
  deleted with the module, so nothing forces the old case. Fix:
  rename to `Tm'.TowerSorts` / `RIdent'.ShapeFO`.
- n2 (plan C.8, C.10, C.12, C.18, C.19 Consumes). File attributions
  wrong though every name exists: `Ctx` is in `Term.lean`;
  `ccrObjMk` in `Utilities/Families.lean`; `natFreeAlgEquiv` in
  `Algebras.lean`; `objToNat` in `Examples.lean`;
  `FreeAlg'.induction` in `Polynomial/RType.lean`; `erToKFunctor` in
  `LawvereERKSim/ErToKFunctor.lean`; `kToERFunctor` /
  `kToERFunctor_map_interp` in `LawvereKSimER.lean`;
  `LawvereKSimDCat` in `LawvereKSimQuot.lean`; C.19 uses
  `kToERFunctor` without listing it. Fix the attributions.
- n3 (plan C.8 Files). "alphabetical position" conflicts with
  `GebLean/Ramified.lean`'s dependency-ordered import list. Fix the
  wording.

## Verified without defect

- Declaration existence: about eighty consumed names verified present
  with the claimed shapes across the legacy `Ramified` modules, the
  Phase A/B modules, the vendored `Slice/{Basic,W}.lean`,
  `PolyAlg.lean`, and mathlib (including `Equiv.listEquivOfEquiv`
  with forward map `List.map e`, `Equiv.sigmaCongr` / `prodCongr` /
  `sumCongr` / `subtypeEquiv` / `boolNot` / `sigmaSumDistrib`,
  `piSetoid`, `ObjectProperty.FullSubcategory`,
  `NatIso.ofComponents`, `eqToIso`, `IsTerminal.ofUniqueHom`,
  `BinaryFan.IsLimit.mk`, `ofChosenFiniteProducts`,
  `Equivalence.faithful_functor`, `List.map_ofFn`). Conditional
  branches resolved: `RType'.interp_isObj` is absent from Phase A,
  so the C.12-before-C.10 order is operative; `natFreeAlgEquiv'` is
  defined as `(freeAlgSliceEquiv natAlgSig).trans natFreeAlgEquiv`,
  so the C.12 agreement lemma holds by `rfl`; `FreeAlg'.induction`
  exists (in `Polynomial/RType.lean`).
- Constraint compliance: every construction names a permitted
  elimination device; `PolyFix.ind` verified `Sort`-polymorphic, so
  the Type-valued legacy-side translations are realizable; the
  Quotient API is `mk` / `lift` / `ind` / `sound` only; `@[simp]`
  assignments fall under the constructor/field policy; no
  `noncomputable` in any route; universes conform.
- Mathematical soundness: `reindex` is sound against the vendored
  admissibility structure (`WValid` / `NodeValid` / `OverInput`
  constrain only index equalities, and the underlying `PFunctor` is
  untouched); the `identSliceEquiv` assembly type-checks end to end
  with `reindex identCtxEquiv.symm` the correct direction; the
  two-step composite meets at
  `SynCat (higherOrder' A) (interpQuotRel (higherOrder' A))`; the
  C.19 transfer route closes against the actual
  `ramified_definability` statement; no statement found false as
  stated.
- Placeholder scan: deferred spellings carry executor decision
  procedures with recording steps; aggregator wiring and test
  registration complete.

## Disposition

Applied in the follow-up commit on this branch: M1 (shared `get_map`
helper produced by C.8 and cited at every transport), M2 (agreement
lemmas re-hosted in `Polynomial/RType.lean`), M4 (both documents
aligned on `SortedSigEquiv.tmMap` / `.tmEquiv` /
`PresentationEquiv.tmMap_eval` / `PresentationEquiv.synCatEquiv`),
m1–m7, n1 (renamed `Tm'.TowerSorts` / `RIdent'.ShapeFO`), n2, n3.
M3 resolved by annotating design s12 with the existing `doc(todo)`
commit; no plan task added. The conditional-branch resolutions are
folded into C.10/C.12 (unconditional C.12-first order; the
`natFreeAlgEquiv'_slice` lemma recorded as `rfl`-provable). One
knock-on fix beyond the findings: with C.12 ordered first,
`rTypeSliceEquiv_curried` (which consumes C.10's `RType'.curried`)
moved from C.12 to C.10.

## Overall

Zero blockers; four majors, seven minors, three nits, all mechanical
to repair; the architecture, constraint compliance, and the
consumed-declaration surface verified sound. Round 2 verifies the
dispositions and scans for regressions.
