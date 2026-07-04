import Mathlib.Algebra.Order.BigOperators.Group.Finset
import GebLean.Utilities.Tower
import GebLean.LawvereKSim

/-!
# Clock-format tower arithmetic

Pure natural-number inequalities converting the elementary-recurrence runtime
tower bound into Leivant's clock format `c · 2_q(sz)` (Lemma 6 hypothesis
shape, section 3.2). The runtime bound produced elsewhere in the definability
development has the shape `tower μ (m + k)`, an additive offset `k` inside a
fixed-height tower applied to a size `m`; Leivant's clock format instead
multiplies a fixed-height ladder `2_q` by a constant `c`. `add_le_tower`
absorbs the offset into the tower's argument, `tower_add_le_tower` then absorbs
it into the tower's height via `tower_comp`, and `tower_clock_format` packages
the result in the existential `c · 2_q` shape (with `c = 1`, `q = μ + k`).
`maxOfNat_le_sum_succ` and `clock_mono` supply the componentwise
max-over-inputs handling that the arity remark of section 3.2 needs: the
maximum of an input-indexed size family is bounded by the staggered sum, and
the clock composite `c · 2_q` is monotone in its argument.

## Main statements

* `add_le_tower` — `x + k ≤ tower k x`, the offset bounded by the height.
* `tower_add_le_tower` — `tower μ (x + k) ≤ tower (μ + k) x`, the offset
  absorbed into the height.
* `tower_clock_format` — the existential `c · 2_q` clock format.
* `maxOfNat_le_sum_succ` — the max over inputs bounded by the staggered sum.
* `clock_mono` — monotonicity of the clock composite `c · tower q`.

## Implementation notes

These are pure `ℕ` inequalities (novel packaging), supporting the transcription
of Leivant's Lemma 6 clock format. `tower_clock_format` keeps an explicit
constant `c` (specialized to `1`) so that downstream statements match Lemma 6's
`c · 2_q` shape at the paper's generality rather than a normalized special
case.

## References

D. Leivant, "Ramified recurrence and computational complexity III: Higher type
recurrence and elementary complexity", Annals of Pure and Applied Logic 96
(1999) 209-229, section 3.2, DOI `10.1016/S0168-0072(98)00040-2`.

## Tags

tower, elementary recurrence, clock format, elementary complexity
-/

namespace GebLean.Ramified.Definability

open Finset

/-- `x + k ≤ tower k x`: each of the `k` height increments has room for one
additive unit, since `n + 1 ≤ 2 ^ n` for every `n`. -/
theorem add_le_tower (k x : ℕ) : x + k ≤ tower k x := by
  induction k with
  | zero => simp
  | succ k ih =>
    calc x + (k + 1) = (x + k) + 1 := by omega
      _ ≤ tower k x + 1 := by omega
      _ ≤ 2 ^ tower k x := Nat.lt_two_pow_self
      _ = tower (k + 1) x := (tower_succ k x).symm

/-- The additive offset absorbed into the height: `tower μ (x + k)` is bounded
by `tower (μ + k) x`, via `add_le_tower`, `tower_mono_right`, and
`tower_comp`. -/
theorem tower_add_le_tower (μ k x : ℕ) :
    tower μ (x + k) ≤ tower (μ + k) x :=
  le_trans (tower_mono_right μ (add_le_tower k x)) (le_of_eq (tower_comp μ k x))

/-- The clock format: for every height `μ` and offset `k` there are a constant
`c` and a height `q` with `tower μ (x + k) ≤ c * tower q x` for all `x` —
Leivant's `c · 2_q` shape (Lemma 6 hypothesis format), realized with `c = 1`
and `q = μ + k`. The explicit `c` keeps the statement at the paper's
generality. -/
theorem tower_clock_format (μ k : ℕ) :
    ∃ c q, ∀ x, tower μ (x + k) ≤ c * tower q x :=
  ⟨1, μ + k, fun x => by rw [Nat.one_mul]; exact tower_add_le_tower μ k x⟩

/-- The max over inputs bounded by the staggered in-system size sum:
`Fin.maxOfNat n v ≤ ∑ i, (v i + 1)`. The componentwise input handling of the
arity remark (section 3.2). -/
theorem maxOfNat_le_sum_succ (n : ℕ) (v : Fin n → ℕ) :
    Fin.maxOfNat n v ≤ ∑ i, (v i + 1) :=
  Fin.maxOfNat_le fun j =>
    le_trans (Nat.le_add_right (v j) 1)
      (Finset.single_le_sum (f := fun i => v i + 1)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ j))

/-- The clock composite `c · tower q` is monotone in its argument: `x ≤ y`
gives `c * tower q x ≤ c * tower q y`. Transports an input bound through the
clock format (the arity remark, section 3.2). -/
theorem clock_mono (c q : ℕ) {x y : ℕ} (h : x ≤ y) :
    c * tower q x ≤ c * tower q y :=
  Nat.mul_le_mul (Nat.le_refl c) (tower_mono_right q h)

end GebLean.Ramified.Definability
