import Mathlib.Combinatorics.Quiver.Basic
import Mathlib.Combinatorics.Quiver.Path
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Order.Basic

/-!
# Acyclic Categories

This file defines acyclic quivers and acyclic categories using topological
sorting as the acyclicity criterion.

## Main definitions

* `AcyclicQuiver`: A quiver with a strict total order on vertices such
  that every edge goes from a smaller vertex to a larger vertex
  (topological sort)
* `FiniteAcyclicQuiver`: An acyclic quiver with finitely many vertices
  and finitely many edges
* `AcyclicCategory`: An acyclic quiver with associative composition
  (semicategory structure). Note: The strict ordering forbids identity
  morphisms, so the structure does not specify them explicitly, but we
  can generate a category structure by adjoining identities.
* `FiniteAcyclicCategory`: A finite acyclic category
-/

universe u v w

/-- An acyclic quiver is a quiver equipped with a strict total order
    on vertices such that every edge goes from a smaller to a larger
    vertex. This provides a topological sort, which proves the quiver
    is acyclic. -/
class AcyclicQuiver (V : Type u) extends Quiver.{v} V, LinearOrder V where
  /-- Every edge goes from a smaller vertex to a larger vertex -/
  edge_increases : ∀ {a b : V}, (a ⟶ b) → a < b

/-- A finite acyclic quiver has finitely many vertices and finitely
    many edges between each pair of vertices. -/
class FiniteAcyclicQuiver (V : Type u) [AcyclicQuiver V] where
  /-- The vertex set is finite -/
  fintypeObj : Fintype V := by infer_instance
  /-- Each hom-set is finite -/
  fintypeHom (a b : V) : Fintype (a ⟶ b) := by infer_instance

attribute [instance] FiniteAcyclicQuiver.fintypeObj
  FiniteAcyclicQuiver.fintypeHom

/-- An acyclic category is an acyclic quiver with a composition
    operation. The strict ordering ensures there are no identity
    morphisms, so this is a semicategory structure rather than a full
    category. Identities can be added later to form a complete
    category. -/
class AcyclicCategory (V : Type u) [AcyclicQuiver V] where
  /-- Composition of morphisms -/
  comp : ∀ {a b c : V}, (a ⟶ b) → (b ⟶ c) → (a ⟶ c)
  /-- Associativity of composition -/
  assoc : ∀ {a b c d : V} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d),
    comp (comp f g) h = comp f (comp g h)

/-- A finite acyclic category combines finiteness with the acyclic
    composition structure. -/
class FiniteAcyclicCategory (V : Type u) [AcyclicQuiver V]
    [AcyclicCategory V] extends FiniteAcyclicQuiver V

namespace AcyclicQuiver

variable {V : Type u} [AcyclicQuiver V]

/-- In an acyclic quiver, the edge relation is irreflexive. -/
theorem edge_irrefl (a : V) : IsEmpty (a ⟶ a) := by
  constructor
  intro f
  have : a < a := edge_increases f
  exact lt_irrefl a this

/-- In an acyclic quiver, edges are antisymmetric: if there's an edge
    from a to b, there cannot be an edge from b to a. -/
theorem edge_antisymm {a b : V} (f : a ⟶ b) : IsEmpty (b ⟶ a) := by
  constructor
  intro g
  have hab : a < b := edge_increases f
  have hba : b < a := edge_increases g
  exact lt_asymm hab hba

/-- Any path built from edges goes from a smaller to a larger
    vertex. -/
theorem path_increases {a b c : V} (p : Quiver.Path a b)
    (f : b ⟶ c) :
    a < c := by
  cases p with
  | nil => exact edge_increases f
  | cons p' g =>
    have hab : a < b := path_increases p' g
    have hbc : b < c := edge_increases f
    exact lt_trans hab hbc

/-- There are no non-trivial cycles in an acyclic quiver. -/
theorem no_cycles {a : V} (p : Quiver.Path a a) :
    p = Quiver.Path.nil := by
  cases p with
  | nil => rfl
  | cons p' f =>
    exfalso
    have : a < a := path_increases p' f
    exact lt_irrefl a this

end AcyclicQuiver

namespace AcyclicCategory

open CategoryTheory

variable {V : Type u} [AcyclicQuiver V]

end AcyclicCategory
