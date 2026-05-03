# Workstream: ER ↔ K^sim_2 categorical equivalence

## Status

Active.

## Context

Formalizing the categorical equivalence
`LawvereKSimDCat 2 ≌ LawvereERCat`.  Master design at
`docs/research/2026-05-02-er-ksim2-equiv-via-urm-master-design.md`.

## Progress

- Step 0 (master design): complete (3 rounds adversarial
  review, signed off).
- Step 1 (foundational ER-side tupling): complete.  Lands
  `Nat.tuplePack`, `Nat.tupleAt`, `Nat.tuplePackCoef`,
  bijection theorems, polynomial value bound, ER-side
  named composites, PolyBound builders, ERMorN-quotient
  round-trip lemmas, and decorative
  `LawvereERCat.tupleIso (k + 1) ≅ 1`.  Plan at
  `docs/superpowers/plans/2026-05-02-step-1-er-tupling.md`.
  Spec at
  `docs/superpowers/specs/2026-05-02-step-1-er-tupling-design.md`.
  3 rounds adversarial review on spec; clean bill of
  health round 3.
- Step 2 (ER-side simultaneous bounded recursion):
  complete.  Lands `Nat.simRecVec` / `Nat.simRec`
  semantic functions, `ERMor1.tuplePackedBound`
  packed-state bound + PolyBound builder + dominance
  helper, `ERMor1.simultaneousBoundedRec` with
  conditional correctness theorem
  `simultaneousBoundedRec_interp_correct` and
  per-component PolyBound builder
  `ofSimultaneousBoundedRec`.  Plan at
  `docs/superpowers/plans/2026-05-03-step-2-er-simultaneous-bounded-rec.md`.
  Spec at
  `docs/superpowers/specs/2026-05-03-step-2-er-simultaneous-bounded-rec-design.md`.
- Step 3 (Tourlakis A_n^r majorant family in ER):
  complete.  Lands `ERMor1.A_one`, `ERMor1.A_one_iter`,
  `ERMor1.A_two_iter` named composites; closed-form
  `@[simp]` interp lemmas; `ERMor1.PolyBound.ofA_one` and
  `ERMor1.PolyBound.ofA_one_iter` builders.  No PolyBound
  for `A_two_iter` (tower-fast; level-2 chain consumes
  Nat-level dominance via
  `simultaneousBoundedRec_interp_correct` at step 5).
  Plan at
  `docs/superpowers/plans/2026-05-03-step-3-er-tourlakis-A-majorants.md`.
  Spec at
  `docs/superpowers/specs/2026-05-03-step-3-er-tourlakis-A-majorants-design.md`.
  4 rounds adversarial review on the spec, 2 on the plan;
  round 4 of the spec review empirically Lean-verified all
  five proofs.

## Next steps

- Step 4: `LawvereKSimMajorization.lean` (master design
  §3.4).
