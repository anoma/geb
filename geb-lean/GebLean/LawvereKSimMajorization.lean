import GebLean.LawvereKSim
import GebLean.LawvereKSimPolynomialBound
import GebLean.Utilities.ERAMajorants
import GebLean.Utilities.ERArith
import GebLean.Utilities.Tower
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Nat.Log

/-!
# K^sim majorization theorems (Tourlakis 2018 §0.1.0.10)

For every `f : KMor1 a` with `f.level ≤ n` (where `n ≤ 2`),
this module produces a Lean-computable `(r, offset) : ℕ × ℕ`
such that
`∀ v : Fin a → ℕ,
  f.interp v ≤ (ERMor1.A_n_iter r).interp ![vMax v + offset]`.

Three deliverables:

- `KMor1.majorize_one : KMor1 a → f.level ≤ 1 → ℕ × ℕ`
  plus `majorize_by_A_one_iter` (level-≤1 case in A_1).
- `KMor1.majorize : KMor1 a → f.level ≤ 2 → ℕ × ℕ` plus
  `majorize_by_A_two_iter` (level-≤2 case in A_2).
- `KMor1.majorize_by_componentBound` step-5 bridge lemma
  feeding `simultaneousBoundedRec_interp_correct`.

ER-side helpers `sumCtxER`, `sumCtxERPlusOffset` named
composites support the bridge.

See
`docs/superpowers/specs/2026-05-03-step-4-ksim-majorization-design.md`
and master design §3.4 / §3.5 in
`docs/research/2026-05-02-er-ksim2-equiv-via-urm-master-design.md`.
Cross-reference network:
`docs/research/2026-04-30-ksim-polynomial-bound-references.md`.
-/

namespace GebLean

/-- Maximum of a `Fin a → ℕ` family.  Matches the
`Finset.sup` form returned by
`KMor1.linearBound_dominates`.  Private to this file. -/
private abbrev vMax {a : ℕ} (v : Fin a → ℕ) : ℕ :=
  (Finset.univ : Finset (Fin a)).sup v

end GebLean
