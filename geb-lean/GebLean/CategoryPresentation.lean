import Mathlib.CategoryTheory.Category.Cat
import Mathlib.CategoryTheory.Category.Quiv
import Mathlib.CategoryTheory.Quotient

/-!
# Presentation of Categories by Generators and Relations

This module implements the presentation of a category by generators and
relations, following the standard construction:

1. Start with a quiver (generators)
2. Form the free category on that quiver (using `Quiv.free`)
3. Quotient by a congruence relation (using `CategoryTheory.Quotient`)

The result is a category where morphisms are equivalence classes of paths
in the quiver, with specified paths identified according to the relations.

## Main definitions

- `CategoryPresentation`: A structure packaging a quiver and relations on
  its free category
- `toCategory`: The presented category, formed as the quotient

## References

- https://ncatlab.org/nlab/show/presentation+of+a+category+by+generators+and+relations
- [Mathlib.CategoryTheory.Quotient](https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/Quotient.html)
- [Mathlib.CategoryTheory.Category.Quiv](https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/Category/Quiv.html)

-/

namespace GebLean

open CategoryTheory Quiver

universe v u

/-- A presentation of a category consists of:
    - A quiver `V` (the generators)
    - A relation `rels` on morphisms in the free category on `V`
-/
structure CategoryPresentation where
  /-- The quiver of generators -/
  generators : Type u
  /-- The quiver structure on generators -/
  [generatorQuiver : Quiver.{v + 1} generators]
  /-- Relations on paths in the free category -/
  relations : @HomRel (Paths generators) _

namespace CategoryPresentation

variable (P : CategoryPresentation.{v, u})

/-- Make the quiver instance available -/
instance : Quiver.{v + 1} P.generators := P.generatorQuiver

/-- The free category on the generators has Paths as morphisms -/
abbrev FreeCategory := Paths P.generators

/-- The presented category, formed by quotienting the free category by the
    relations -/
def toCategory : Type u := Quotient P.relations

/-- The presented category has a natural category structure -/
instance categoryToCategory : Category.{max u v} P.toCategory :=
  Quotient.category P.relations

end CategoryPresentation

end GebLean
