import Mathlib.CategoryTheory.Category.Cat
import Mathlib.CategoryTheory.Equivalence

/-!
# Category Theory Utilities

Convenience notation and helpers for working with categories.

## Main definitions

* `HomSet`: Structure containing the data of a quiver (the Hom type family)
* `≅Cat`: Notation for isomorphisms between categories without explicit
  `Cat.of`
-/

namespace GebLean

open CategoryTheory

universe v u

/-- The data of a quiver: a family of types indexed by pairs of vertices. -/
structure HomSet (V : Type u) where
  /-- The type of edges/arrows/morphisms between a given source and target. -/
  Hom : V → V → Sort v

/-- Extract a `Quiver` typeclass instance from a `HomSet`. -/
instance {V : Type u} (hs : HomSet.{v, u} V) : Quiver.{v} V where
  Hom := hs.Hom

/-- Extract the `HomSet` from a `Quiver` typeclass instance. -/
def homSetOfQuiver (V : Type u) [Quiver.{v} V] : HomSet.{v, u} V where
  Hom := Quiver.Hom

end GebLean

namespace CategoryTheory

/-- Notation for isomorphism between categories without explicit `Cat.of`. -/
notation C " ≅Cat " D => Cat.of C ≅ Cat.of D

end CategoryTheory
