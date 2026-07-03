import GebLean
import GebLean.Ramified.Definability.Bounds

/-!
# Tests for clock-format tower arithmetic

Executable checks for `GebLean.Ramified.Definability.Bounds`: numeric `#guard`
instances of the offset bounds `add_le_tower` and `tower_add_le_tower` at small
heights (tower values grow doubly exponentially, so the arguments are kept
tiny), and `example` instances exercising the existential clock format
`tower_clock_format`, the max-over-inputs bound `maxOfNat_le_sum_succ`, and the
clock monotonicity `clock_mono`.
-/

namespace GebLeanTests.Ramified.Definability.BoundsTest

open GebLean GebLean.Ramified.Definability

-- `add_le_tower` at small values: `tower 2 1 = 4`, `tower 3 0 = 4`.
#guard 1 + 2 ≤ tower 2 1
#guard 0 + 3 ≤ tower 3 0

-- `tower_add_le_tower` at `μ = 1, k = 2, x = 1`: `tower 1 3 = 8 ≤ tower 3 1 = 16`.
#guard tower 1 (1 + 2) ≤ tower (1 + 2) 1

-- `Fin.maxOfNat` on a small family: the max of `1, 2, 3` is `3`.
#guard Fin.maxOfNat 3 (fun i => i.val + 1) = 3

-- The existential clock format at `μ = 1, k = 2`.
example : ∃ c q, ∀ x, tower 1 (x + 2) ≤ c * tower q x :=
  tower_clock_format 1 2

-- The max-over-inputs bound over a three-input size family.
example (v : Fin 3 → ℕ) : Fin.maxOfNat 3 v ≤ ∑ i, (v i + 1) :=
  maxOfNat_le_sum_succ 3 v

-- The clock composite is monotone in its argument.
example {x y : ℕ} (h : x ≤ y) : 5 * tower 2 x ≤ 5 * tower 2 y :=
  clock_mono 5 2 h

end GebLeanTests.Ramified.Definability.BoundsTest
