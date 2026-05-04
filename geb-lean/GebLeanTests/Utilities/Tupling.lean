import GebLean.Utilities.Tupling

/-!
# Tests for `Nat.tuplePack`, `Nat.tupleAt`, `Nat.tuplePackCoef`,
# `Nat.tupleAt_le`, `Nat.tuplePack_le`.

Foundational fixed-length k-tuple Szudzik pairing
infrastructure for the ER ↔ K^sim_2 categorical equivalence.
See `GebLean.Utilities.Tupling` and master design §3.1
in `docs/research/2026-05-02-er-ksim2-equiv-via-urm-master-design.md`.
-/

open Nat

-- Head/tail orientation locks: the prefix-pack is on the
-- LEFT of `pair`; the new last element is on the RIGHT,
-- matching Tourlakis 2018 §0.1.0.34, p. 14's left-fold
-- recurrence.
#guard tuplePack 1 ![3, 5] = pair 3 5
#guard tupleAt 1 (pair 3 5) 0 = 3
#guard tupleAt 1 (pair 3 5) 1 = 5

-- Identity case (k = 0).
#guard tuplePack 0 ![7] = 7
#guard tupleAt 0 17 0 = 17

-- Round-trip on a small concrete 3-tuple.
#guard tupleAt 2 (tuplePack 2 ![3, 5, 7]) 0 = 3
#guard tupleAt 2 (tuplePack 2 ![3, 5, 7]) 1 = 5
#guard tupleAt 2 (tuplePack 2 ![3, 5, 7]) 2 = 7

-- Boundary `example` lemmas (recurrence + bound corner cases).

example (v : Fin 1 → ℕ) : tuplePack 0 v ≤ v 0 := by
  simp [tuplePack]

example : tuplePackCoef 0 = 1 := rfl

example : tuplePackCoef 1 = 9 := rfl

example : tuplePackCoef 2 = 121 := rfl

example :
    tuplePack 1 ![0, 0]
      ≤ tuplePackCoef 1 * 1 ^ (2 ^ 1) := by
  decide

example :
    tuplePack 1 ![3, 5]
      ≤ tuplePackCoef 1 * (5 + 1) ^ (2 ^ 1) := by
  decide
