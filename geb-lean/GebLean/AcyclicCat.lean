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
* `FiniteQuiver`: A quiver with finitely many vertices and edges
* `FiniteAcyclicQuiver`: An acyclic quiver with finitely many vertices
  and edges
* `Semicategory`: A quiver with associative composition but no identity
  morphisms
* `FiniteSemicategory`: A semicategory with finitely many vertices and
  morphisms
* `AcyclicCategory`: An acyclic quiver with a semicategory structure
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

/-- A finite acyclic quiver has finitely many vertices and finitely
    many edges between each pair of vertices. -/
class FiniteAcyclicQuiver (V : Type u) [AcyclicQuiver V] where
  toFiniteness : FinQuiverWitness V := by infer_instance

instance {V : Type u} [AcyclicQuiver V] [h : FiniteAcyclicQuiver V] :
    FinQuiverWitness V := h.toFiniteness

/-- A semicategory is a quiver with associative composition but no
    identity morphisms. -/
class Semicategory (V : Type u) extends Quiver.{v} V where
  /-- Composition of morphisms -/
  comp : ∀ {a b c : V}, (a ⟶ b) → (b ⟶ c) → (a ⟶ c)
  /-- Associativity of composition -/
  assoc : ∀ {a b c d : V} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d),
    comp (comp f g) h = comp f (comp g h)

/-- A finite semicategory has finitely many vertices and morphisms. -/
class FiniteSemicategory (V : Type u) [Semicategory V] where
  toFiniteness : FinQuiverWitness V := by infer_instance

instance {V : Type u} [Semicategory V] [h : FiniteSemicategory V] :
    FinQuiverWitness V := h.toFiniteness

/-- An acyclic category is an acyclic quiver with a semicategory
    structure. The strict ordering ensures there are no identity
    morphisms. Identities can be added later to form a complete
    category. -/
class AcyclicCategory (V : Type u) [AcyclicQuiver V]
    extends Semicategory V

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
