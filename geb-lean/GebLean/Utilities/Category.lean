import Mathlib.CategoryTheory.Category.Cat
import Mathlib.CategoryTheory.Equivalence

namespace CategoryTheory

universe u v

variable {C D : Type u} [Category.{v} C] [Category.{v} D]

/-- Notation for isomorphism between categories without explicit `Cat.of`. -/
notation C " ≅Cat " D => Cat.of C ≅ Cat.of D

/-- Convenience alias for the equivalence associated to an isomorphism of
    categories. -/
@[inline] def catIsoToEquivalence (iso : C ≅Cat D) : C ≌ D :=
  Cat.equivOfIso iso

end CategoryTheory
