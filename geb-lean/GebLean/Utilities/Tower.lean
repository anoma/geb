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

end GebLean
