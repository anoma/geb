import Mathlib.Combinatorics.Quiver.Basic
import Mathlib.CategoryTheory.Category.Quiv
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.Data.Fintype.Basic
import GebLean.Utilities.Category
import GebLean.Utilities.Fintype

/-!
# Finite Quivers

This file defines finite quivers and related structures.

## Main definitions

* `FinQuiverWitness`: A proof that a quiver has finitely many vertices
  and edges
* `FiniteQuiver`: A quiver with finitely many vertices and edges
* `IsFiniteQuiver`: The property that a quiver (in Quiv) is finite
* `FiniteQuiverCat`: The full subcategory of finite quivers
-/

universe u v

namespace GebLean

/-- A finite quiver has finitely many vertices and finitely many edges
    between each pair of vertices. This requires morphisms to be in
    Type (not Prop). -/
structure FinQuiverWitness (V : Type u) (hs : HomSet.{v + 1, u} V) where
  /-- The vertex set is finite -/
  fintypeVertex : FintypeData V
  /-- Each edge set is finite -/
  fintypeEdge : ∀ a b : V, FintypeData (hs a b)

attribute [instance] FinQuiverWitness.fintypeVertex
  FinQuiverWitness.fintypeEdge

/-- Build a `Quiver` typeclass instance from a `FinQuiverWitness`. -/
instance {V : Type u} (hs : HomSet.{v + 1, u} V)
    (_wit : FinQuiverWitness V hs) : Quiver.{v + 1, u} V where
  Hom := hs

open CategoryTheory

/-- The property that a quiver (in Quiv) is finite (has finitely many
    vertices and edges). -/
def IsFiniteQuiver : ObjectProperty (Quiv.{v, u}) :=
  fun V => Nonempty (FinQuiverWitness V (homSetOfQuiver V))

/-- The full subcategory of finite quivers. -/
abbrev FiniteQuiverCat :=
  IsFiniteQuiver.FullSubcategory

namespace FiniteQuiverCat

/-- The inclusion functor from finite quivers to all quivers. -/
abbrev ι : FiniteQuiverCat.{v, u} ⥤ Quiv.{v, u} :=
  IsFiniteQuiver.ι

end FiniteQuiverCat

end GebLean
