import Mathlib.Logic.Equiv.Defs

/-!
# Utilities

General-purpose utility functions and lemmas that may be useful across
different modules.
-/

/-- A subtype of sigma where both indices are constrained to equal specific
    values is equivalent to the base type at those indices.

    This is useful when extracting dependent types from functors, where the
    functor encoding uses sigma types with equality constraints. -/
def sigmaTrivialSubtype {α : Type*} {β : α → α → Type*} (a b : α) :
    {m : Σ (a' b' : α), β a' b' // m.1 = a ∧ m.2.1 = b} ≃ β a b where
  toFun m := by
    obtain ⟨⟨a', b', x⟩, ha, hb⟩ := m
    subst ha hb
    exact x
  invFun x := ⟨⟨a, b, x⟩, rfl, rfl⟩
  left_inv := by
    intro ⟨⟨a', b', x⟩, ha, hb⟩
    subst ha hb
    rfl
  right_inv := by intro x; rfl
