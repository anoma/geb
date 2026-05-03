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

## Next steps

- Step 3: `A_n^r` Tourlakis named composites in ER
  (`ERMor1.A_one`, `ERMor1.A_one_iter`,
  `ERMor1.A_two_iter`).  See master design §3.3.
