import GebLean.Utilities.Tupling

namespace GebLeanTests.Tupling

-- Head/tail orientation locks: the prefix-pack is on the
-- LEFT of `pair`; the new last element is on the RIGHT,
-- matching Tourlakis 2018 §0.1.0.34, p. 14's left-fold
-- recurrence.
#guard Nat.tuplePack 1 ![3, 5] = Nat.pair 3 5
#guard Nat.tupleAt 1 (Nat.pair 3 5) 0 = 3
#guard Nat.tupleAt 1 (Nat.pair 3 5) 1 = 5

-- Identity case (k = 0).
#guard Nat.tuplePack 0 ![7] = 7
#guard Nat.tupleAt 0 17 0 = 17

-- Round-trip on a small concrete 3-tuple.
#guard Nat.tupleAt 2 (Nat.tuplePack 2 ![3, 5, 7]) 0 = 3
#guard Nat.tupleAt 2 (Nat.tuplePack 2 ![3, 5, 7]) 1 = 5
#guard Nat.tupleAt 2 (Nat.tuplePack 2 ![3, 5, 7]) 2 = 7

-- Boundary `example` lemmas (recurrence + bound corner cases).

example (v : Fin 1 → ℕ) : Nat.tuplePack 0 v ≤ v 0 := by
  simp [Nat.tuplePack]

example : Nat.tuplePackCoef 0 = 1 := rfl

example : Nat.tuplePackCoef 1 = 9 := rfl

example : Nat.tuplePackCoef 2 = 121 := rfl

example :
    Nat.tuplePack 1 ![0, 0]
      ≤ Nat.tuplePackCoef 1 * 1 ^ (2 ^ 1) := by
  decide

example :
    Nat.tuplePack 1 ![3, 5]
      ≤ Nat.tuplePackCoef 1 * (5 + 1) ^ (2 ^ 1) := by
  decide

end GebLeanTests.Tupling
