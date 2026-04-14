import Mathlib.Algebra.Order.Monoid.Unbundled.Pow

/-!
# Tower of Twos

Iterated exponential `tower k x` applies `fun n => 2 ^ n` to `x` a
total of `k` times.  Used as a bounding function for the elementary
recursive functions: every ER term's interpretation is dominated by a
fixed-height tower applied to the context's maximum (plus a padding
constant).
-/

namespace GebLean

/-- `tower k x` is a tower of `k` twos applied to `x`:
`tower 0 x = x` and `tower (k+1) x = 2 ^ tower k x`. -/
def tower : ℕ → ℕ → ℕ
  | 0, x => x
  | k + 1, x => 2 ^ tower k x

@[simp] theorem tower_zero (x : ℕ) : tower 0 x = x := rfl

@[simp] theorem tower_succ (k x : ℕ) :
    tower (k + 1) x = 2 ^ tower k x := rfl

/-- `x ≤ tower k x` for all `k`, `x`. -/
theorem self_le_tower (k x : ℕ) : x ≤ tower k x := by
  induction k with
  | zero => exact Nat.le_refl _
  | succ k ih =>
    calc x ≤ tower k x := ih
      _ ≤ 2 ^ tower k x := by
        have h : tower k x < 2 ^ tower k x :=
          Nat.lt_two_pow_self
        exact le_of_lt h

/-- `1 ≤ tower k x` whenever `1 ≤ x`. -/
theorem one_le_tower_of_one_le (k x : ℕ) (hx : 1 ≤ x) :
    1 ≤ tower k x := le_trans hx (self_le_tower k x)

/-- `tower k` is monotone in its second argument. -/
theorem tower_mono_right (k : ℕ) {x y : ℕ} (h : x ≤ y) :
    tower k x ≤ tower k y := by
  induction k with
  | zero => exact h
  | succ k ih =>
    exact Nat.pow_le_pow_right (by omega) ih

/-- Composition of towers: applying a height-`j` tower to a
height-`k` tower of `x` equals applying a height-`j+k` tower to `x`. -/
theorem tower_comp (j k x : ℕ) :
    tower j (tower k x) = tower (j + k) x := by
  induction j with
  | zero => rw [Nat.zero_add]; rfl
  | succ j ih =>
    rw [Nat.succ_add]
    change 2 ^ tower j (tower k x) = 2 ^ tower (j + k) x
    rw [ih]

end GebLean
