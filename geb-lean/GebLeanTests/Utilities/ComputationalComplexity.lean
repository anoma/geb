import GebLean.Utilities.ComputationalComplexity

/-!
# Tests for `Utilities/ComputationalComplexity`

`#guard` checks for `Nat.pair_le_sq` and `Nat.seqPackBound`
on small concrete inputs.  The `Nat.tower_succ_pow_bound`,
`Nat.tower_succ_pow_bound_strong`, and
`Nat.polynomial_iter_tower_bound` lemmas are verified by
Lean's typechecker; numerical spot-checks at very small
inputs are not informative for tower-of-exponentials bounds.
-/

open Nat

#guard Nat.pair 0 0 ≤ (0 + 0 + 1)^2
#guard Nat.pair 3 5 ≤ (3 + 5 + 1)^2
#guard Nat.pair 7 7 ≤ (7 + 7 + 1)^2

#guard Nat.seqPack [3] ≤ seqPackBound 0 1 3
#guard Nat.seqPack [3, 5] ≤ seqPackBound 1 1 5
#guard Nat.seqPack [1, 2, 3] ≤ seqPackBound 2 1 3
