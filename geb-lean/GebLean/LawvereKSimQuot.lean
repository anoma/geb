import GebLean.LawvereKSimInterp
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Terminal
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts

/-!
# Extensional-equality quotient and Lawvere structure

This module will define the extensional-equality setoid
`kMorNSetoid` on K^sim morphisms, the quotient category
`KMorNQuo`, the Lawvere finite-product structure, and the
depth-restricted full subcategory `KSimMor d` per design
principle P4.
-/

namespace GebLean

/-- Extensional equality on multi-output K^sim
morphisms.  Two `f, g : KMorN n m` are equivalent iff
their interpretations agree at every context (and so
agree component-wise). -/
def kMorNSetoid (n m : ℕ) : Setoid (KMorN n m) where
  r f g := ∀ ctx : Fin n → ℕ, f.interp ctx = g.interp ctx
  iseqv := {
    refl := fun _ _ => rfl
    symm := fun h ctx => (h ctx).symm
    trans := fun h1 h2 ctx =>
      (h1 ctx).trans (h2 ctx)
  }

end GebLean
