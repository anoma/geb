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

/-- The operation code of an application `app o o`: kind bit `0` with the domain
and codomain sort codes, through `codeOp` and the `codeRType` node equation. -/
example :
    codeOp (OneLambdaOp.app RType.o RType.o)
      = Nat.pair 0 (Nat.pair (Nat.pair 0 0) (Nat.pair 0 0)) := by simp [codeOp]

/-- The operation codes of the two constructor constants of `natAlgSig`: kind bit
`2` with the `Bool` label read `cond b 1 0`. -/
example :
    codeOp (OneLambdaOp.con true) = Nat.pair 2 1
    ∧ codeOp (OneLambdaOp.con false) = Nat.pair 2 0 := ⟨rfl, rfl⟩

/-- The operation codes of a destructor and the case combinator: kind bits `3`
and `4` with the position index and `0`. -/
example :
    codeOp (OneLambdaOp.dstr ⟨0, by decide⟩) = Nat.pair 3 0
    ∧ codeOp OneLambdaOp.case = Nat.pair 4 0 := ⟨rfl, rfl⟩

/-- A bound variable codes to kind bit `0` with its de Bruijn index `0`, through
`codeTm_var` (task 6.4.6). -/
example : codeTm (Binding.Tm.var (boundVar (Γ := []) (σ := RType.o))) = Nat.pair 0 0 := by
  rw [codeTm_var]; rfl

/-- The identity abstraction `λx:o. x` codes through `codeTm_lam'` and
`codeTm_var` to its kind-`1` node with the `lam` operation code and the unary
body pack. -/
example :
    codeTm (OneLambda.lam' (Binding.Tm.var (boundVar (Γ := []) (σ := RType.o))))
      = Nat.pair 1 (Nat.pair (codeOp (OneLambdaOp.lam RType.o RType.o))
          (Nat.pair (Nat.pair 0 0) 0)) := by
  rw [codeTm_lam', codeTm_var]; rfl

/-- The identity β-redex `(λx:o. x) c₀` (the task 6.4.1 acceptance term) codes
through `codeTm_app'` to its kind-`1` node with the `app` operation code and the
binary child pack of the function and argument codes. -/
example :
    codeTm (OneLambda.app'
        (OneLambda.lam' (Binding.Tm.var (boundVar (Γ := []) (σ := RType.o))))
        (conc (natToFreeAlg 0)))
      = Nat.pair 1 (Nat.pair (codeOp (OneLambdaOp.app RType.o RType.o))
          (Nat.pair
            (codeTm (OneLambda.lam' (Binding.Tm.var (boundVar (Γ := []) (σ := RType.o)))))
            (Nat.pair (codeTm (conc (natToFreeAlg 0))) 0))) := by
  rw [codeTm_app']

/-- A constructor constant `con true` codes through `codeTm_con` to its kind-`1`
node with the nullary children pack `0`. -/
example :
    codeTm (Binding.Tm.op (S := oneLambdaSig natAlgSig) (Γ := [])
        (OneLambdaOp.con true) (fun k => k.elim0))
      = Nat.pair 1 (Nat.pair (codeOp (OneLambdaOp.con true)) 0) := by
  rw [codeTm_con]

end GebLean.Ramified
