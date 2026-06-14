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

/-- `(Σ_{i<n} q^i) * (q - 1) = q ^ n - 1` over `ℕ`, for `1 ≤ q`. -/
theorem natGeomSum_mul (q n : ℕ) (hq : 1 ≤ q) :
    (∑ i ∈ Finset.range n, q ^ i) * (q - 1) = q ^ n - 1 := by
  induction n with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, Nat.add_mul, pow_succ, ih]
    have h1 : 1 ≤ q ^ m := Nat.one_le_pow _ _ (by omega)
    have h2 : q ^ m ≤ q ^ m * q := Nat.le_mul_of_pos_right _ (by omega)
    have h3 : q ^ m * (q - 1) = q ^ m * q - q ^ m := Nat.mul_sub_one (q ^ m) q
    omega

/-- Geometric closed form: `Σ_{i<n} q^i = (q^n - 1)/(q - 1)` for
`2 ≤ q`. -/
theorem natGeomSum_eq (q n : ℕ) (hq : 2 ≤ q) :
    ∑ i ∈ Finset.range n, q ^ i = (q ^ n - 1) / (q - 1) := by
  have hpos : 0 < q - 1 := by omega
  rw [← natGeomSum_mul q n (by omega), Nat.mul_div_cancel _ hpos]

/-- The geometric closed form in `natBSum` shape, for `2 ≤ q`. -/
theorem natBSum_geom (q bound : ℕ) (hq : 2 ≤ q) :
    natBSum bound (fun i => q ^ i) = (q ^ bound - 1) / (q - 1) := by
  rw [natBSum_eq_sum]; exact natGeomSum_eq q bound hq

end GebLean
