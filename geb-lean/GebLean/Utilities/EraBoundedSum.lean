import GebLean.LawvereER
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# `natBSum` bridge and geometric closed form

`ℕ`-level lemmas supporting the Era bounded-sum engine
(`GebLean/EraCompleteness.lean`). Relates the recursion-defined
`natBSum` (`GebLean/LawvereER.lean`) to `Finset.sum`, and proves the
geometric closed form `Σ_{i<n} q^i = (q^n − 1)/(q − 1)`.

## Main statements

* `natBSum_eq_sum` — `natBSum bound f = ∑ i ∈ Finset.range bound, f i`.
* `natGeomSum_eq` — the geometric closed form for `2 ≤ q`.
* `natLinGeomSum_mul` — the linear-weighted geometric progression
  identity, cleared of division.
* `natLinGeomSum_eq` — the linear-weighted geometric closed form for
  `2 ≤ q` and `2 ≤ n`.

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

/-- Linear-weighted geometric sum `Σ_{i<n} i·qⁱ`, cleared of division
and stated additively (no `ℕ` truncation, valid for all `n`), for
`2 ≤ q`. `G₁` re-indexed to `Finset.range n`. -/
theorem natLinGeomSum_mul (q n : ℕ) (hq : 2 ≤ q) :
    (∑ i ∈ Finset.range n, i * q ^ i) * (q - 1) ^ 2 + q ^ (n + 1)
        + n * q ^ n =
      n * q ^ (n + 1) + q := by
  induction n with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, Nat.add_mul, pow_succ]
    -- normalize pow expansions so q^{m+k} appears as iterated *q
    simp only [pow_succ, pow_zero, one_mul] at *
    have hqm : 1 ≤ q ^ m := Nat.one_le_pow _ _ (by omega)
    -- q^m*(q-1) = q^m*q - q^m
    have ha : q ^ m * (q - 1) = q ^ m * q - q ^ m := Nat.mul_sub_one _ _
    -- q^m ≤ q^m*q
    have hle : q ^ m ≤ q ^ m * q := Nat.le_mul_of_pos_right _ (by omega)
    -- q^m*q ≤ q^m*q*q
    have hle2 : q ^ m * q ≤ q ^ m * q * q := Nat.le_mul_of_pos_right _ (by omega)
    -- (q^m*q - q^m)*q = q^m*q*q - q^m*q
    have hd : (q ^ m * q - q ^ m) * q = q ^ m * q * q - q ^ m * q :=
      Nat.sub_mul _ _ _
    -- additive expansion: q^m*(q-1)*(q-1) + 2*(q^m*q) = q^m*q*q + q^m
    have hexp : q ^ m * (q - 1) * (q - 1) + 2 * (q ^ m * q) = q ^ m * q * q + q ^ m := by
      -- key: q^m*q*(q-1) = q^m*q*q - q^m*q (Nat.mul_sub_one)
      have hpqd : q ^ m * q * (q - 1) = q ^ m * q * q - q ^ m * q := Nat.mul_sub_one _ _
      -- additive: q^m*q*(q-1) + q^m*q = q^m*q*q  (with hle2 for the subtraction)
      have hpqd2 : q ^ m * q * (q - 1) + q ^ m * q = q ^ m * q * q := by omega
      -- q^m*(q-1)*(q-1) + q^m*(q-1) = q^m*(q-1)*q  (dist law, additive)
      have hpd2 : q ^ m * (q - 1) * (q - 1) + q ^ m * (q - 1) = q ^ m * (q - 1) * q := by
        have hle3 : q ^ m * (q - 1) ≤ q ^ m * (q - 1) * q :=
          Nat.le_mul_of_pos_right _ (by omega)
        have := Nat.mul_sub_one (q ^ m * (q - 1)) q
        omega
      -- q^m*(q-1)*q = q^m*q*(q-1)  (mul_comm in the middle)
      have hcomm : q ^ m * (q - 1) * q = q ^ m * q * (q - 1) := by ring
      omega
    -- key atoms omega needs: (m+1)*R = m*R + R for R = q^m*q*q and R = q^m*q
    have hm1R : (m + 1) * (q ^ m * q * q) = m * (q ^ m * q * q) + q ^ m * q * q :=
      Nat.succ_mul m (q ^ m * q * q)
    have hm1Q : (m + 1) * (q ^ m * q) = m * (q ^ m * q) + q ^ m * q :=
      Nat.succ_mul m (q ^ m * q)
    -- m-scaled version: m*q^m*((q-1)*(q-1)) + 2*m*(q^m*q) = m*(q^m*q*q) + m*q^m
    -- derived by multiplying hexp by m and reassociating
    have hmexp : m * q ^ m * ((q - 1) * (q - 1)) + 2 * m * (q ^ m * q) =
        m * (q ^ m * q * q) + m * q ^ m := by
      -- m * (hexp) using Nat.mul_add on both sides
      have hscale : m * (q ^ m * (q - 1) * (q - 1) + 2 * (q ^ m * q)) =
          m * (q ^ m * q * q + q ^ m) := congrArg (m * ·) hexp
      -- left: m * (A + B) = m*A + m*B
      rw [Nat.mul_add, Nat.mul_add] at hscale
      -- reassociate: m * (q^m*(q-1)*(q-1)) = m*q^m*((q-1)*(q-1))
      have hl1 : m * (q ^ m * (q - 1) * (q - 1)) = m * q ^ m * ((q - 1) * (q - 1)) := by
        rw [Nat.mul_assoc, Nat.mul_assoc]
      -- m*(2*(q^m*q)) = 2*m*(q^m*q)
      have hl2 : m * (2 * (q ^ m * q)) = 2 * m * (q ^ m * q) := by
        rw [← Nat.mul_assoc, Nat.mul_comm m 2, Nat.mul_assoc]
      linarith [hl1, hl2, hscale]
    linarith

/-- Linear-weighted geometric closed form:
`Σ_{i<n} i·qⁱ = ((n−1)·q^{n+1} − n·qⁿ + q)/(q−1)²` for `2 ≤ q` and `2 ≤ n`.
The hypothesis `2 ≤ n` ensures `n·qⁿ ≤ (n−1)·q^{n+1}` so the ℕ subtraction is exact;
the formula reduces to a division of `S·(q−1)²` by `(q−1)²`.
Derived from `natLinGeomSum_mul` by clearing denominators. -/
theorem natLinGeomSum_eq (q n : ℕ) (hq : 2 ≤ q) (hn : 2 ≤ n) :
    ∑ i ∈ Finset.range n, i * q ^ i =
      ((n - 1) * q ^ (n + 1) - n * q ^ n + q) / (q - 1) ^ 2 := by
  have hpos : 0 < (q - 1) ^ 2 := Nat.pow_pos (by omega)
  have hmul := natLinGeomSum_mul q n hq
  -- (n-1)*q^{n+1} + q^{n+1} = n*q^{n+1}
  have hn1_eq : (n - 1) * q ^ (n + 1) + q ^ (n + 1) = n * q ^ (n + 1) := by
    have hpred : n - 1 + 1 = n := by omega
    calc (n - 1) * q ^ (n + 1) + q ^ (n + 1)
        = (n - 1 + 1) * q ^ (n + 1) := by rw [Nat.add_mul, one_mul]
      _ = n * q ^ (n + 1) := by rw [hpred]
  -- n*q^n ≤ (n-1)*q^{n+1}: needed for exact ℕ subtraction
  -- equivalent to n ≤ (n-1)*q, which holds for n ≥ 2, q ≥ 2
  have hle_sub : n * q ^ n ≤ (n - 1) * q ^ (n + 1) := by
    -- rewrite as (n-1)*q*q^n ≥ n*q^n, i.e., (n-1)*q ≥ n (for n≥2, q≥2)
    have hpow : (n - 1) * q ^ (n + 1) = (n - 1) * q * q ^ n := by
      rw [pow_succ]; ring
    rw [hpow]
    apply Nat.mul_le_mul_right
    -- n ≤ (n-1)*q: use 2*(n-1) ≥ n (from n≥2) and q*(n-1) ≥ 2*(n-1)
    calc n ≤ 2 * (n - 1) := by omega
      _ ≤ q * (n - 1) := Nat.mul_le_mul_right _ hq
      _ = (n - 1) * q := by ring
  -- from hmul and hn1_eq: (Σ i·qⁱ)*(q-1)² + n·qⁿ = (n-1)·q^{n+1} + q
  have hadd : (∑ i ∈ Finset.range n, i * q ^ i) * (q - 1) ^ 2 + n * q ^ n =
      (n - 1) * q ^ (n + 1) + q := by linarith
  -- exact ℕ subtraction: (n-1)*q^{n+1} - n*q^n + q = (Σ i·qⁱ)*(q-1)²
  have hclear : (n - 1) * q ^ (n + 1) - n * q ^ n + q =
      (∑ i ∈ Finset.range n, i * q ^ i) * (q - 1) ^ 2 := by omega
  rw [hclear, Nat.mul_div_cancel _ hpos]

end GebLean
