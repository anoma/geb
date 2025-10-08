import Mathlib.Combinatorics.Quiver.Basic
import Mathlib.Combinatorics.Quiver.Prefunctor
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.Data.Fintype.Basic

/-!
# Semicategories

This file defines semicategories and their morphisms.

## Main definitions

* `Semicategory`: A quiver with associative composition but no identity
  morphisms
* `Semifunctor`: A morphism between semicategories that preserves
  composition
* `SemicategoryCat`: The category of semicategories (as a small category
  where objects and morphisms are in the same universe)
* `FiniteSemicategory`: A semicategory with finitely many objects and
  morphisms
-/

universe u v w

/-- A proof of finiteness of a quiver. -/
structure FinQuiverWitness (V : Type u) [Quiver.{v + 1} V] where
  /-- The vertex set is finite -/
  fintypeVertex : Fintype V
  /-- Each edge set is finite -/
  fintypeEdge : ∀ a b : V, Fintype (a ⟶ b)

attribute [instance] FinQuiverWitness.fintypeVertex
  FinQuiverWitness.fintypeEdge

/-- A semicategory is a quiver with associative composition but no
    identity morphisms. -/
class Semicategory (V : Type u) extends Quiver.{v} V where
  /-- Composition of morphisms -/
  comp : ∀ {a b c : V}, (a ⟶ b) → (b ⟶ c) → (a ⟶ c)
  /-- Associativity of composition -/
  assoc : ∀ {a b c d : V} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d),
    comp (comp f g) h = comp f (comp g h)

/-- A finite semicategory has finitely many objects and morphisms. -/
class FiniteSemicategory (V : Type u) [Semicategory V] where
  toFiniteness : FinQuiverWitness V := by infer_instance

instance {V : Type u} [Semicategory V] [h : FiniteSemicategory V] :
    FinQuiverWitness V := h.toFiniteness

/-- A semifunctor is a morphism between semicategories that preserves
    composition but not necessarily identities (since semicategories
    may not have identities). -/
structure Semifunctor (U V : Type u) [Semicategory U]
    [Semicategory V] extends Prefunctor U V where
  /-- A semifunctor preserves composition -/
  map_comp : ∀ {a b c : U} (f : a ⟶ b) (g : b ⟶ c),
    map (Semicategory.comp f g) = Semicategory.comp (map f) (map g)

namespace Semifunctor

variable {U V W : Type u} [Semicategory U] [Semicategory V]
  [Semicategory W]

@[ext]
theorem ext {F G : Semifunctor U V} (h : F.toPrefunctor = G.toPrefunctor) :
    F = G := by
  cases F
  cases G
  congr

/-- The identity semifunctor. -/
def id (V : Type u) [Semicategory V] : Semifunctor V V where
  toPrefunctor := Prefunctor.id V
  map_comp _ _ := rfl

/-- Composition of semifunctors. -/
def comp (F : Semifunctor U V) (G : Semifunctor V W) :
    Semifunctor U W where
  toPrefunctor := F.toPrefunctor.comp G.toPrefunctor
  map_comp f g := by
    simp [Prefunctor.comp]
    rw [F.map_comp, G.map_comp]

theorem id_comp (F : Semifunctor V W) : (id V).comp F = F := by
  apply Semifunctor.ext
  rfl

theorem comp_id (F : Semifunctor V W) : F.comp (id W) = F := by
  apply Semifunctor.ext
  rfl

theorem comp_assoc {X : Type u} [Semicategory X]
    (F : Semifunctor U V) (G : Semifunctor V W)
    (H : Semifunctor W X) :
    (F.comp G).comp H = F.comp (G.comp H) := by
  apply Semifunctor.ext
  rfl

end Semifunctor

/-- The category of semicategories (as a small category where objects
    and morphisms are in the same universe). -/
structure SemicategoryCat : Type (u + 1) where
  /-- The underlying type of objects. -/
  carrier : Type u
  [quiver : Quiver.{u} carrier]
  [semicat : Semicategory.{u, u} carrier]

attribute [instance] SemicategoryCat.quiver SemicategoryCat.semicat

namespace SemicategoryCat

open CategoryTheory

instance : CoeSort SemicategoryCat (Type u) where
  coe V := V.carrier

/-- Construct a bundled semicategory from a type with a semicategory
    instance. -/
def of (V : Type u) [Quiver.{u} V] [Semicategory.{u, u} V] :
    SemicategoryCat := ⟨V⟩

instance : Category.{u} SemicategoryCat where
  Hom V W := Semifunctor.{u} V W
  id V := Semifunctor.id V
  comp {_ _ _} F G := F.comp G
  id_comp {_ _} := Semifunctor.id_comp
  comp_id {_ _} := Semifunctor.comp_id
  assoc {_ _ _ _} := Semifunctor.comp_assoc

end SemicategoryCat
