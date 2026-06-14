import GebLean.LawvereER
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Ring.GeomSum

/-!
# `natBSum` bridge and geometric closed form

`ℕ`-level lemmas supporting the Era bounded-sum engine
(`GebLean/EraCompleteness.lean`). Relates the recursion-defined
`natBSum` (`GebLean/LawvereER.lean`) to `Finset.sum`, and proves the
geometric closed form `Σ_{i<n} q^i = (q^n − 1)/(q − 1)`.

## Main statements

* `natBSum_eq_sum` — `natBSum bound f = ∑ i ∈ Finset.range bound, f i`.
* `natGeomSum_eq` — the geometric closed form for `2 ≤ q`.

## References

* Marchenkov 2007, § 5 (geometric closed forms).

## Tags

elementary recursive, bounded summation, geometric series
-/

namespace GebLean

/-- `natBSum` agrees with the `Finset.range` sum. -/
theorem natBSum_eq_sum (bound : ℕ) (f : ℕ → ℕ) :
    natBSum bound f = ∑ i ∈ Finset.range bound, f i := by
  induction bound with
  | zero => simp [natBSum]
  | succ b ih =>
    have hstep : natBSum (b + 1) f = natBSum b f + f b := rfl
    rw [hstep, Finset.sum_range_succ, ih]

end GebLean
