import Mathlib.Logic.Equiv.Defs

/-!
# Sigma Utilities

Lemmas and equivalences for working with sigma types when encoding
dependent categorical data.
-/

universe u v

namespace GebLean

/-- A subtype of a sigma where both indices are constrained to specific
values is equivalent to the underlying fiber. -/
def sigmaTrivialSubtype {α : Type*} {β : α → α → Type*} (a b : α) :
    {m : Σ (a' b' : α), β a' b' // m.1 = a ∧ m.2.1 = b} ≃ β a b where
  toFun m := by
    rcases m with ⟨⟨a', b', x⟩, ha, hb⟩
    cases ha
    cases hb
    exact x
  invFun x := ⟨⟨a, b, x⟩, rfl, rfl⟩
  left_inv := by
    intro m
    rcases m with ⟨⟨a', b', x⟩, ha, hb⟩
    cases ha
    cases hb
    rfl
  right_inv := by
    intro x
    rfl

end GebLean
