import GebLean.Utilities.ERTreeArith

/-!
# Tests for `GebLean.Utilities.ERTreeArith`.
-/

open GebLean

#guard ERMor1.btlEncodeLeaf.interp ![0] = 0
#guard ERMor1.btlEncodeLeaf.interp ![3] = 6
#guard ERMor1.btlEncodeLeaf.interp ![7] = 14

#guard ERMor1.btlEncodeNode.interp ![0, 0] = 1
#guard ERMor1.btlEncodeNode.interp ![2, 4] =
    2 * Nat.pair 2 4 + 1

/-- `btlEncodeLeaf` agrees with `BTL.encode` on a leaf. -/
example (lbl : ℕ) :
    ERMor1.btlEncodeLeaf.interp ![lbl] =
      BTL.encode (BTL.leaf lbl) := by simp

/-- `btlEncodeNode` reconstructs a parent code from child codes
that are themselves already encoded. -/
example (l r : BTL) :
    ERMor1.btlEncodeNode.interp
        ![BTL.encode l, BTL.encode r] =
      BTL.encode (BTL.node l r) := by
  simp [BTL.encode]
