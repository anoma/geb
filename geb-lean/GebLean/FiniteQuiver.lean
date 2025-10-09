import Mathlib.Combinatorics.Quiver.Basic
import Mathlib.CategoryTheory.Category.Quiv
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.Data.Fintype.Basic

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

/-- A proof of finiteness of a quiver. -/
structure FinQuiverWitness (V : Type u) [Quiver.{v + 1} V] where
  /-- The vertex set is finite -/
  fintypeVertex : Fintype V
  /-- Each edge set is finite -/
  fintypeEdge : ∀ a b : V, Fintype (a ⟶ b)

attribute [instance] FinQuiverWitness.fintypeVertex
  FinQuiverWitness.fintypeEdge

/-- A finite quiver has finitely many vertices and finitely many edges
    between each pair of vertices. This requires morphisms to be in
    Type (not Prop). -/
class FiniteQuiver (V : Type u) [Quiver.{v + 1} V] where
  toFiniteness : FinQuiverWitness V := by infer_instance

instance {V : Type u} [Quiver.{v + 1} V] [h : FiniteQuiver V] :
    FinQuiverWitness V := h.toFiniteness

open CategoryTheory

/-- The property that a quiver (in Quiv) is finite (has finitely many
    vertices and edges). -/
def IsFiniteQuiver : ObjectProperty (Quiv.{v, u}) :=
  fun V => Nonempty (FinQuiverWitness V)

/-- The full subcategory of finite quivers. -/
abbrev FiniteQuiverCat :=
  IsFiniteQuiver.FullSubcategory

namespace FiniteQuiverCat

/-- The inclusion functor from finite quivers to all quivers. -/
abbrev ι : FiniteQuiverCat.{v, u} ⥤ Quiv.{v, u} :=
  IsFiniteQuiver.ι

end FiniteQuiverCat
