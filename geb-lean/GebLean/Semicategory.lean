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

namespace GebLean

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

namespace Semicategory

open CategoryTheory

/-- Morphisms in the category obtained by adjoining identities to a
    semicategory. A morphism is either an identity or a morphism
    from the underlying semicategory. -/
inductive AdjoinedIdHom {V : Type u} [Semicategory.{u, u} V] :
    V → V → Type u where
  | id (a : V) : AdjoinedIdHom a a
  | hom {a b : V} (f : a ⟶ b) : AdjoinedIdHom a b

namespace AdjoinedIdHom

variable {V : Type u} [Semicategory.{u, u} V]

/-- Compose two morphisms with adjoined identities. -/
def comp {a b c : V} : AdjoinedIdHom a b → AdjoinedIdHom b c →
    AdjoinedIdHom a c
  | id _, id _ => id a
  | id _, hom g => hom g
  | hom f, id _ => hom f
  | hom f, hom g => hom (Semicategory.comp f g)

theorem comp_id {a b : V} (f : AdjoinedIdHom a b) :
    comp f (id b) = f := by
  cases f <;> rfl

theorem id_comp {a b : V} (f : AdjoinedIdHom a b) :
    comp (id a) f = f := by
  cases f <;> rfl

theorem comp_assoc {a b c d : V}
    (f : AdjoinedIdHom a b) (g : AdjoinedIdHom b c)
    (h : AdjoinedIdHom c d) :
    comp (comp f g) h = comp f (comp g h) := by
  cases f with
  | id =>
    cases g with
    | id =>
      cases h with
      | id => rfl
      | hom => rfl
    | hom =>
      cases h with
      | id => rfl
      | hom => rfl
  | hom =>
    cases g with
    | id =>
      cases h with
      | id => rfl
      | hom => rfl
    | hom =>
      cases h with
      | id => rfl
      | hom => simp only [comp]; rw [Semicategory.assoc]

/-- Given decidable equality on semicategory morphisms, provide decidable
    equality on morphisms with adjoined identities. -/
def decidableEq (decEqSemi : ∀ (X Y : V), DecidableEq (X ⟶ Y))
    (X Y : V) : DecidableEq (AdjoinedIdHom X Y) :=
  fun f g => by
    cases f with
    | id =>
      cases g with
      | id => exact isTrue rfl
      | hom _ => exact isFalse (fun h => nomatch h)
    | hom f' =>
      cases g with
      | id => exact isFalse (fun h => nomatch h)
      | hom g' =>
        have : DecidableEq (X ⟶ Y) := decEqSemi X Y
        cases this f' g' with
        | isTrue h => exact isTrue (congrArg AdjoinedIdHom.hom h)
        | isFalse h => exact isFalse (fun heq => h (by cases heq; rfl))

/-- Instance version of decidableEq for automatic inference -/
instance instDecidableEq [decEqSemi : ∀ (X Y : V), DecidableEq (X ⟶ Y)]
    (X Y : V) : DecidableEq (AdjoinedIdHom X Y) :=
  decidableEq decEqSemi X Y

end AdjoinedIdHom

/-- The category structure obtained by adjoining identities to a
    semicategory. -/
instance adjoinedIdCategory {V : Type u} [Semicategory.{u, u} V] :
    Category V where
  Hom := AdjoinedIdHom
  id a := AdjoinedIdHom.id a
  comp := AdjoinedIdHom.comp
  id_comp := AdjoinedIdHom.id_comp
  comp_id := AdjoinedIdHom.comp_id
  assoc := AdjoinedIdHom.comp_assoc

/-- Lift a semifunctor to a functor between the categories with
    adjoined identities. -/
def liftToFunctor {U : Type u} {V : Type u}
    [Semicategory.{u, u} U] [Semicategory.{u, u} V]
    (F : Semifunctor U V) : U ⥤ V where
  obj := F.obj
  map := fun {a b} f =>
    match f with
    | AdjoinedIdHom.id _ => AdjoinedIdHom.id (F.obj a)
    | AdjoinedIdHom.hom g => AdjoinedIdHom.hom (F.map g)
  map_id a := rfl
  map_comp {a b c} f g := by
    cases f with
    | id =>
      cases g with
      | id => rfl
      | hom => rfl
    | hom f' =>
      cases g with
      | id => rfl
      | hom g' =>
        change AdjoinedIdHom.hom (F.map (Semicategory.comp f' g')) =
          AdjoinedIdHom.comp (AdjoinedIdHom.hom (F.map f'))
            (AdjoinedIdHom.hom (F.map g'))
        simp only [AdjoinedIdHom.comp, F.map_comp]

/-- The inclusion functor from semicategories to categories. -/
def toCat : SemicategoryCat ⥤ Cat where
  obj V := ⟨V.α, adjoinedIdCategory⟩
  map {V W} F := liftToFunctor F
  map_id V := by
    refine CategoryTheory.Functor.ext ?_ ?_
    · intro x
      rfl
    · intro x y f
      simp only [CategoryStruct.id, CategoryTheory.Functor.id_obj, eqToHom_refl]
      cases f <;> rfl
  map_comp {U V W} F G := by
    refine CategoryTheory.Functor.ext ?_ ?_
    · intro x
      rfl
    · intro x y f
      simp only [CategoryStruct.comp, CategoryTheory.Functor.comp_obj,
        eqToHom_refl]
      cases f <;> rfl

end Semicategory

end GebLean
