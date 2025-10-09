import Mathlib.Combinatorics.Quiver.Basic
import Mathlib.Combinatorics.Quiver.Prefunctor
import Mathlib.CategoryTheory.Category.Basic
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

universe u u' u'' v v' v''

/-- A compositional structure provides a way to compose morphisms in a
    quiver. -/
abbrev CompositionalStruct (V : Type u) [Quiver.{v} V] :=
  ∀ {a b c : V}, (a ⟶ b) → (b ⟶ c) → (a ⟶ c)

/-- An associativity law states that composition is associative. This is
    a property dependent upon having a compositional structure. -/
abbrev AssociativityLaw (V : Type u) [Quiver.{v} V]
    (comp : CompositionalStruct V) :=
  ∀ {a b c d : V} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d),
    comp (comp f g) h = comp f (comp g h)

/-- The structure of a semicategory: composition and associativity,
    without requiring identity morphisms. -/
structure SemicategoryStruct (V : Type u) [Quiver.{v} V] where
  /-- Composition of morphisms -/
  comp : CompositionalStruct V
  /-- Associativity of composition -/
  assoc : AssociativityLaw V comp

/-- A semicategory is a quiver with associative composition but no
    identity morphisms. -/
class Semicategory (V : Type u) extends Quiver.{v} V where
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

/-- The category of semicategories as a small category where objects
    and morphisms are in the same universe. For unbundled
    semicategories, objects and morphisms may be in different
    universes. -/
structure SemicategoryCat : Type (u + 1) where
  /-- The underlying type of objects. -/
  carrier : Type u
  /-- The quiver structure -/
  quiver : Quiver.{u} carrier
  /-- The semicategory structure -/
  semicat : @SemicategoryStruct carrier quiver

instance instSemicategoryCatQuiver (V : SemicategoryCat) :
    Quiver V.carrier := V.quiver
instance instSemicategoryCatSemicategoryStruct (V : SemicategoryCat) :
    SemicategoryStruct V.carrier := V.semicat

instance instSemicategoryCatSemicategory (V : SemicategoryCat) :
    Semicategory V.carrier where
  toSemicategoryStruct := V.semicat

namespace SemicategoryCat

open CategoryTheory

instance : CoeSort SemicategoryCat.{u} (Type u) where
  coe V := V.carrier

/-- Construct a bundled semicategory from a type with a semicategory
    instance. -/
def of (V : Type u) [q : Quiver.{u} V] (sc : SemicategoryStruct V) :
    SemicategoryCat.{u} := ⟨V, q, sc⟩

instance : Category.{u} SemicategoryCat.{u} where
  Hom V W := Semifunctor V.carrier W.carrier
  id V := Semifunctor.id V.carrier
  comp {_ _ _} F G := Semifunctor.comp F G
  id_comp {_ _} := Semifunctor.id_comp
  comp_id {_ _} := Semifunctor.comp_id
  assoc {_ _ _ _} := Semifunctor.comp_assoc

end SemicategoryCat
