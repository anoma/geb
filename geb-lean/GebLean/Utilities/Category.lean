import Mathlib.CategoryTheory.Category.Cat
import Mathlib.CategoryTheory.Equivalence

/-!
# Category Theory Utilities

Convenience notation and helpers for working with categories.

## Main definitions

* `≅Cat`: Notation for isomorphisms between categories without explicit
  `Cat.of`
-/

namespace CategoryTheory

/-- Notation for isomorphism between categories without explicit `Cat.of`. -/
notation C " ≅Cat " D => Cat.of C ≅ Cat.of D

end CategoryTheory
