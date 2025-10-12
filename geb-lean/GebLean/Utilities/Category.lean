import Mathlib.CategoryTheory.Category.Cat
import Mathlib.CategoryTheory.Equivalence

namespace CategoryTheory

/-- Notation for isomorphism between categories without explicit `Cat.of`. -/
notation C " ≅Cat " D => Cat.of C ≅ Cat.of D

end CategoryTheory
