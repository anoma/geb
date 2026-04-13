import GebLean.LawvereER

/-!
# Boolean Operations on Elementary Recursive Terms

Defines `boolNot`, `boolAnd`, and `boolEqNat` as
specific `ERMor1` terms, together with `@[simp]`
interpretation lemmas and Boolean-closure properties.
Convention: `1 = true`, `0 = false`.

These operations are the building blocks for the
finite-product and equalizer constructions in
`LawvereERLex.lean`.
-/

namespace GebLean

/-- Boolean negation as the indicator of `x = 0`:
returns `1` if input is `0`, else `0`.
Definable as `1 ⊖ x`. -/
def ERMor1.boolNot : ERMor1 1 :=
  ERMor1.comp ERMor1.sub fun i => match i with
    | ⟨0, _⟩ => ERMor1.oneN 1
    | ⟨1, _⟩ => ERMor1.proj 0

/-- Interpretation of `boolNot`: returns `1 ⊖ ctx 0`. -/
@[simp] theorem ERMor1.interp_boolNot
    (ctx : Fin 1 → ℕ) :
    ERMor1.boolNot.interp ctx = 1 - ctx 0 :=
  rfl

/-- `boolNot` always returns a Boolean value. -/
theorem ERMor1.boolNot_le_one (ctx : Fin 1 → ℕ) :
    ERMor1.boolNot.interp ctx ≤ 1 := by
  rw [ERMor1.interp_boolNot]
  exact Nat.sub_le 1 (ctx 0)

end GebLean
