import GebLean.Ramified.Soundness.CodeTm

/-!
# Tests for the sort codes

Acceptance examples for the Gödel coding of the ramified types (task 6.4.5): the
node equations of `codeRType` on small literal sorts, the shape-tag reads of
`shapeCode`, and the child-code reads of `argCode`, `domCode`, and `codCode`;
and the mirror theorem `ordCode_codeRType` on small sorts, asserting that
reading the type order off a code agrees with computing it on the type.
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

/-- Reading the order off the code of the arrow sort `o → o` agrees with
`RType.ord`, the acceptance instance of the mirror theorem. -/
example :
    ordCode (codeRType (RType.arrow RType.o RType.o))
      = RType.ord (RType.arrow RType.o RType.o) := ordCode_codeRType _

/-- The mirror theorem holds on the order-`2` sort `(o → o) → o`, exercising a
nested arrow recursion. -/
example :
    ordCode (codeRType (RType.arrow (RType.arrow RType.o RType.o) RType.o))
      = 2 := by
  rw [ordCode_codeRType]
  simp [RType.ord_arrow, RType.ord_o]

/-- The mirror theorem holds through an `Ω` node, which contributes no order
shift. -/
example :
    ordCode (codeRType (RType.omega (RType.arrow RType.o RType.o)))
      = RType.ord (RType.arrow RType.o RType.o) := by
  rw [ordCode_codeRType, RType.ord_omega]

end GebLean.Ramified
