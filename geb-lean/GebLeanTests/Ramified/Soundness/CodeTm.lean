import GebLean.Ramified.Soundness.CodeTm

/-!
# Tests for the sort codes

Acceptance examples for the Gödel coding of the ramified types (task 6.4.5): the
node equations of `codeRType` on small literal sorts, the shape-tag reads of
`shapeCode`, and the child-code reads of `argCode`, `domCode`, and `codCode`.
-/

namespace GebLean.Ramified

open GebLean.Ramified.OneLambda

/-- The base sort `o` codes to `Nat.pair 0 0`, through the node equation. -/
example : codeRType RType.o = Nat.pair 0 0 := by simp

/-- The arrow sort `o → o` codes to its shape-tagged nested pair, through the
node equations. -/
example :
    codeRType (RType.arrow RType.o RType.o)
      = Nat.pair 1 (Nat.pair (Nat.pair 0 0) (Nat.pair 0 0)) := by simp

/-- The `Ω o` sort codes to its shape-tagged pair, through the node equations. -/
example : codeRType (RType.omega RType.o) = Nat.pair 2 (Nat.pair 0 0) := by simp

/-- The shape tag of a base-sort code is `0`. -/
example : shapeCode (codeRType RType.o) = 0 := by
  simp [shapeCode, Nat.unpair_pair]

/-- The shape tag of an arrow code is `1`. -/
example : shapeCode (codeRType (RType.arrow RType.o RType.o)) = 1 := by
  simp [shapeCode, Nat.unpair_pair]

/-- The shape tag of an `Ω` code is `2`. -/
example : shapeCode (codeRType (RType.omega RType.o)) = 2 := by
  simp [shapeCode, Nat.unpair_pair]

/-- The child-code read of an `Ω` code recovers the child code. -/
example : argCode (codeRType (RType.omega RType.o)) = codeRType RType.o := by
  simp [argCode, Nat.unpair_pair]

/-- The domain and codomain reads of an arrow code recover the two child
codes. -/
example :
    domCode (codeRType (RType.arrow RType.o (RType.omega RType.o)))
      = codeRType RType.o
    ∧ codCode (codeRType (RType.arrow RType.o (RType.omega RType.o)))
      = codeRType (RType.omega RType.o) := by
  constructor <;> simp [domCode, codCode, argCode, Nat.unpair_pair]

end GebLean.Ramified
