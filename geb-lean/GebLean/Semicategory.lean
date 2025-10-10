import Mathlib.Combinatorics.Quiver.Basic
import Mathlib.Combinatorics.Quiver.Prefunctor
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.ConcreteCategory.Bundled
import GebLean.FiniteQuiver

/-!
# Semicategories

This file defines semicategories and their morphisms.

## Main definitions

* `CompositionalStruct`: A structure providing composition of morphisms
* `AssociativityLaw`: An associativity law for a compositional structure
* `SemicategoryStruct`: The structure of a semicategory (composition and
  associativity)
* `Semicategory`: A quiver with associative composition but no identity
  morphisms
* `FiniteSemicategory`: A semicategory with finitely many objects and
  morphisms
* `Semifunctor`: A morphism between semicategories that preserves
  composition
* `SemicategoryCat`: The category of semicategories (as a small category
  where objects and morphisms are in the same universe)
-/

universe u u' u'' v

/-- A compositional structure provides a way to compose morphisms in a
    quiver. -/
abbrev CompositionalStruct (V : Type u) [Quiver.{v + 1} V] :=
  ∀ {a b c : V}, (a ⟶ b) → (b ⟶ c) → (a ⟶ c)

/-- An associativity law states that composition is associative. This is
    a property dependent upon having a compositional structure. -/
abbrev AssociativityLaw (V : Type u) [Quiver.{v + 1} V]
    (comp : CompositionalStruct V) :=
  ∀ {a b c d : V} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d),
    comp (comp f g) h = comp f (comp g h)

/-- The structure of a semicategory: composition and associativity,
    without requiring identity morphisms. -/
structure SemicategoryStruct (V : Type u) [Quiver.{v + 1} V] where
  /-- Composition of morphisms -/
  comp : CompositionalStruct V
  /-- Associativity of composition -/
  assoc : AssociativityLaw V comp

/-- A semicategory is a quiver with associative composition but no
    identity morphisms. -/
class Semicategory (V : Type u) extends Quiver.{v + 1} V where
  toSemicategoryStruct : SemicategoryStruct V := by infer_instance

instance {V : Type u} [h : Semicategory V] :
    SemicategoryStruct V := h.toSemicategoryStruct

namespace Semicategory

/-- Composition of morphisms in a semicategory. -/
abbrev comp {V : Type u} [Semicategory V] {a b c : V}
    (f : a ⟶ b) (g : b ⟶ c) : (a ⟶ c) :=
  (toSemicategoryStruct (V := V)).comp f g

/-- Associativity of composition in a semicategory. -/
abbrev assoc {V : Type u} [Semicategory V] {a b c d : V}
    (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) :
    comp (comp f g) h = comp f (comp g h) :=
  (toSemicategoryStruct (V := V)).assoc f g h

end Semicategory

/-- A finite semicategory has finitely many objects and morphisms. -/
class FiniteSemicategory (V : Type u) [Semicategory V] where
  toFiniteness : FinQuiverWitness V := by infer_instance

instance {V : Type u} [Semicategory V] [h : FiniteSemicategory V] :
    FinQuiverWitness V := h.toFiniteness

/-- A semifunctor is a morphism between semicategories that preserves
    composition but not necessarily identities (since semicategories
    may not have identities). -/
structure Semifunctor (U : Type u) (V : Type u') [Semicategory U]
    [Semicategory V] extends Prefunctor U V where
  /-- A semifunctor preserves composition -/
  map_comp : ∀ {a b c : U} (f : a ⟶ b) (g : b ⟶ c),
    map (Semicategory.comp f g) = Semicategory.comp (map f) (map g)

namespace Semifunctor

variable {U : Type u} {V : Type u'} {W : Type u''}
  [Semicategory U] [Semicategory V] [Semicategory W]

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
  toPrefunctor := Prefunctor.comp F.toPrefunctor G.toPrefunctor
  map_comp f g := by
    simp [Prefunctor.comp]
    rw [F.map_comp, G.map_comp]

theorem id_comp (F : Semifunctor V W) : comp (id V) F = F := by
  apply Semifunctor.ext
  rfl

theorem comp_id (F : Semifunctor V W) : comp F (id W) = F := by
  apply Semifunctor.ext
  rfl

theorem comp_assoc {X : Type u} [Semicategory X]
    (F : Semifunctor U V) (G : Semifunctor V W)
    (H : Semifunctor W X) :
    comp (comp F G) H = comp F (comp G H) := by
  apply Semifunctor.ext
  rfl

end Semifunctor

/-- The large category of semicategories, allowing objects and
    morphisms to be in different universes. Uses the Bundled pattern
    from mathlib. -/
def SemicategoryCat.Large : Type (max (u + 1) (v + 1)) :=
  CategoryTheory.Bundled (Semicategory.{u, v})

namespace SemicategoryCat.Large

open CategoryTheory

instance : CoeSort (SemicategoryCat.Large.{u, v}) (Type u) where
  coe V := V.α

/-- Extract the Semicategory instance from a bundled semicategory. -/
def str' (V : SemicategoryCat.Large.{u, v}) : Semicategory.{u, v} V.α :=
  V.str

-- Make the instance available automatically
instance (V : SemicategoryCat.Large.{u, v}) : Semicategory.{u, v} V.α :=
  V.str

/-- Construct a large bundled semicategory from a type with a
    semicategory instance. -/
def of (V : Type u) [Semicategory.{u, v} V] : SemicategoryCat.Large.{u, v} :=
  Bundled.of V

instance : Category.{max u v} (SemicategoryCat.Large.{u, v}) where
  Hom V W := Semifunctor V.α W.α
  id V := Semifunctor.id V.α
  comp {_ _ _} F G := Semifunctor.comp F G
  id_comp {_ _} := Semifunctor.id_comp
  comp_id {_ _} := Semifunctor.comp_id
  assoc {_ _ _ _} := Semifunctor.comp_assoc

end SemicategoryCat.Large

/-- The small category of semicategories, where objects and morphisms
    are in the same universe. -/
abbrev SemicategoryCat.Small := SemicategoryCat.Large.{u, u}

/-- The default is the small category of semicategories. -/
abbrev SemicategoryCat := SemicategoryCat.Small
