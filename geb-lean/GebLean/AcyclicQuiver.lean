import Mathlib.Combinatorics.Quiver.Basic
import Mathlib.Combinatorics.Quiver.Path
import Mathlib.Combinatorics.Quiver.Prefunctor
import Mathlib.CategoryTheory.Category.Basic
import GebLean.FiniteQuiver

/-!
# Acyclic Quivers

This file defines acyclic quivers using topological sorting as the
acyclicity criterion.

## Main definitions

* `AcyclicQuiver`: A quiver with a partial order on vertices such that
  every edge goes from a smaller vertex to a larger vertex (topological
  sort)
* `FiniteAcyclicQuiver`: An acyclic quiver with finitely many vertices
  and edges
* `AcyclicQuiverHom`: Morphisms of acyclic quivers
* `AcyclicQuiverCat`: The category of acyclic quivers
-/

universe u u' u'' v v' v''

/-- A topological order is a partial order used to witness acyclicity
    via topological sort. We use a partial order rather than a total
    order because vertices in different connected components don't need
    to be comparable. This allows forming coproducts of acyclic
    categories. -/
abbrev TopologicalOrder := PartialOrder

/-- The property that every edge in a quiver goes from a smaller vertex
    to a larger vertex with respect to a topological order. -/
abbrev QuiverEdgesIncrease (V : Type u) [Quiver.{v} V]
    [TopologicalOrder V] :=
  ∀ {a b : V}, (a ⟶ b) → a < b

/-- An acyclic quiver is a quiver equipped with a partial order on
    vertices such that every edge goes from a smaller to a larger
    vertex. This provides a topological sort, which proves the quiver
    is acyclic. -/
class AcyclicQuiver (V : Type u) extends Quiver.{v} V,
    TopologicalOrder V where
  edgesIncrease : QuiverEdgesIncrease V := by infer_instance

instance {V : Type u} [h : AcyclicQuiver V] : QuiverEdgesIncrease V :=
  h.edgesIncrease

/-- Every edge in an acyclic quiver goes from a smaller vertex to a
    larger vertex. -/
abbrev edge_increases := @AcyclicQuiver.edgesIncrease

/-- Morphisms of acyclic quivers preserve the strict ordering on
    vertices via their object maps. -/
abbrev PrefunctorPreservesOrder {V : Type u} {W : Type u'} [Quiver V]
    [Quiver W] [TopologicalOrder V] [TopologicalOrder W]
    (F : Prefunctor V W) :=
  StrictMono F.obj

/-- A finite acyclic quiver has finitely many vertices and finitely
    many edges between each pair of vertices. -/
class FiniteAcyclicQuiver (V : Type u) [AcyclicQuiver V] where
  toFiniteness : FinQuiverWitness V := by infer_instance

instance {V : Type u} [AcyclicQuiver V] [h : FiniteAcyclicQuiver V] :
    FinQuiverWitness V := h.toFiniteness

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

/-- A morphism of acyclic quivers is a prefunctor that preserves the
    order on vertices. -/
structure AcyclicQuiverHom (V : Type u) (W : Type u') [AcyclicQuiver V]
    [AcyclicQuiver W] extends Prefunctor V W where
  /-- The vertex map preserves the order -/
  obj_mono : PrefunctorPreservesOrder toPrefunctor

namespace AcyclicQuiverHom

variable {U : Type u} {V : Type u'} {W : Type u''}
  [AcyclicQuiver U] [AcyclicQuiver V] [AcyclicQuiver W]

/-- The identity morphism of acyclic quivers. -/
def id (V : Type u) [AcyclicQuiver V] : AcyclicQuiverHom V V where
  toPrefunctor := Prefunctor.id V
  obj_mono := fun _ _ h => h

/-- Composition of morphisms of acyclic quivers. -/
def comp (F : AcyclicQuiverHom U V) (G : AcyclicQuiverHom V W) :
    AcyclicQuiverHom U W where
  toPrefunctor := Prefunctor.comp F.toPrefunctor G.toPrefunctor
  obj_mono := fun _ _ h => G.obj_mono (F.obj_mono h)

/-- Morphisms of acyclic quivers preserve the edge_increases
    property. -/
theorem map_edge_increases (F : AcyclicQuiverHom V W) {a b : V}
    (f : a ⟶ b) : F.obj a < F.obj b := by
  have hab : a < b := edge_increases f
  exact F.obj_mono hab

@[ext]
theorem ext {F G : AcyclicQuiverHom V W}
    (h : F.toPrefunctor = G.toPrefunctor) : F = G := by
  cases F
  cases G
  congr

theorem id_comp (F : AcyclicQuiverHom V W) : comp (id V) F = F := by
  apply ext
  rfl

theorem comp_id (F : AcyclicQuiverHom V W) : comp F (id W) = F := by
  apply ext
  rfl

theorem comp_assoc {X : Type u} [AcyclicQuiver X]
    (F : AcyclicQuiverHom U V) (G : AcyclicQuiverHom V W)
    (H : AcyclicQuiverHom W X) :
    comp (comp F G) H = comp F (comp G H) := by
  apply ext
  rfl

end AcyclicQuiverHom

/-- The category of acyclic quivers (as a small category where vertices
    and edges are in the same universe). -/
structure AcyclicQuiverCat : Type (u + 1) where
  /-- The type of vertices. -/
  carrier : Type u
  /-- The quiver structure -/
  quiver : Quiver.{u} carrier
  /-- The topological order on vertices -/
  order : TopologicalOrder carrier
  /-- Proof that edges increase -/
  edgesIncrease : @QuiverEdgesIncrease carrier quiver order

instance instAcyclicQuiverCatQuiver (V : AcyclicQuiverCat) :
    Quiver V.carrier := V.quiver
instance instAcyclicQuiverCatOrder (V : AcyclicQuiverCat) :
    TopologicalOrder V.carrier := V.order
instance instAcyclicQuiverCatEdgesIncrease (V : AcyclicQuiverCat) :
    QuiverEdgesIncrease V.carrier :=
  V.edgesIncrease

instance instAcyclicQuiverCatAcyclicQuiver (V : AcyclicQuiverCat) :
    AcyclicQuiver V.carrier where
  edgesIncrease := V.edgesIncrease

namespace AcyclicQuiverCat

open CategoryTheory

instance : CoeSort AcyclicQuiverCat (Type u) where
  coe V := V.carrier

/-- Construct a bundled acyclic quiver from a type with an acyclic
    quiver instance. -/
def of (V : Type u) [q : Quiver.{u} V] [o : TopologicalOrder V]
    (ei : QuiverEdgesIncrease V) : AcyclicQuiverCat := ⟨V, q, o, ei⟩

instance : Category.{u} AcyclicQuiverCat where
  Hom V W := AcyclicQuiverHom.{u, u} V W
  id V := AcyclicQuiverHom.id V
  comp {_ _ _} F G := AcyclicQuiverHom.comp F G
  id_comp {_ _} := AcyclicQuiverHom.id_comp
  comp_id {_ _} := AcyclicQuiverHom.comp_id
  assoc {_ _ _ _} := AcyclicQuiverHom.comp_assoc

end AcyclicQuiverCat
