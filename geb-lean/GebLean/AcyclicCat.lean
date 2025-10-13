import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import GebLean.AcyclicQuiver
import GebLean.Semicategory

/-!
# Acyclic Categories

This file defines acyclic categories (acyclic quivers with semicategory
structure) and the category of acyclic categories.

## Main definitions

* `AcyclicCategory`: An acyclic quiver with a semicategory structure
* `FiniteAcyclicCategory`: A finite acyclic category
* `AcyclicCategoryHom`: Morphisms of acyclic categories
* `AcyclicCategoryCat`: The category of acyclic categories
* `FiniteAcyclicCategoryCat`: The full subcategory of finite acyclic
  categories
-/

namespace GebLean

universe u u' u'' v

/-- An acyclic category is an acyclic quiver with a semicategory
    structure. The strict ordering ensures there are no identity
    morphisms. Identities can be adjoined to form a category. -/
class AcyclicCategory (V : Type u) [AcyclicQuiver V] where
  toSemicategoryStruct : SemicategoryStruct V := by infer_instance

instance {V : Type u} [AcyclicQuiver V] [h : AcyclicCategory V] :
    SemicategoryStruct V := h.toSemicategoryStruct

instance {V : Type u} [inst : AcyclicQuiver V] [h : AcyclicCategory V] :
    Semicategory V where
  toQuiver := inst.toQuiver
  toSemicategoryStruct := h.toSemicategoryStruct

/-- A finite acyclic category combines finiteness with the acyclic
    composition structure. -/
class FiniteAcyclicCategory (V : Type u) [AcyclicQuiver V]
    [AcyclicCategory V] extends FiniteAcyclicQuiver V

/-- A morphism of acyclic categories is a semifunctor that also
    preserves the strict order on objects. -/
structure AcyclicCategoryHom (U : Type u) (V : Type u') [AcyclicQuiver U]
    [AcyclicCategory U] [AcyclicQuiver V] [AcyclicCategory V] where
  /-- The underlying semifunctor -/
  toSemifunctor : Semifunctor U V
  /-- The object map preserves the order -/
  obj_mono : PrefunctorPreservesOrder toSemifunctor.toPrefunctor

namespace AcyclicCategoryHom

variable {U : Type u} {V : Type u'} {W : Type u''}
  [AcyclicQuiver U] [AcyclicCategory U]
  [AcyclicQuiver V] [AcyclicCategory V] [AcyclicQuiver W]
  [AcyclicCategory W]

/-- The identity morphism of acyclic categories. -/
def id (V : Type u) [AcyclicQuiver V] [AcyclicCategory V] :
    AcyclicCategoryHom V V where
  toSemifunctor := Semifunctor.id V
  obj_mono := fun _ _ h => h

/-- Composition of morphisms of acyclic categories. -/
def comp (F : AcyclicCategoryHom U V) (G : AcyclicCategoryHom V W) :
    AcyclicCategoryHom U W where
  toSemifunctor := Semifunctor.comp F.toSemifunctor G.toSemifunctor
  obj_mono := fun _ _ h => G.obj_mono (F.obj_mono h)

@[ext]
theorem ext {F G : AcyclicCategoryHom U V}
    (h : F.toSemifunctor = G.toSemifunctor) : F = G := by
  cases F
  cases G
  congr

theorem id_comp (F : AcyclicCategoryHom V W) : comp (id V) F = F := by
  apply ext
  apply Semifunctor.ext
  rfl

theorem comp_id (F : AcyclicCategoryHom V W) : comp F (id W) = F := by
  apply ext
  apply Semifunctor.ext
  rfl

theorem comp_assoc {X : Type u} [AcyclicQuiver X] [AcyclicCategory X]
    (F : AcyclicCategoryHom U V) (G : AcyclicCategoryHom V W)
    (H : AcyclicCategoryHom W X) :
    comp (comp F G) H = comp F (comp G H) := by
  apply ext
  apply Semifunctor.ext
  rfl

end AcyclicCategoryHom

/-- Witness data for an acyclic category: combines quiver, order,
    acyclicity, and composition structure. -/
structure AcyclicCategoryWitness (V : Type u) where
  quiver : Quiver.{v + 1} V
  order : TopologicalOrder V
  edgesIncrease : @QuiverEdgesIncrease V quiver order
  semicat : @SemicategoryStruct V quiver

/-- The large category of acyclic categories. Since AcyclicCategory
    depends on AcyclicQuiver, we store witness data directly rather
    than typeclass instances to avoid diamond problems. -/
structure AcyclicCategoryCat.Large : Type (max (u + 1) (v + 1)) where
  /-- The carrier type -/
  carrier : Type u
  /-- The witness data for the acyclic category structure -/
  wit : AcyclicCategoryWitness.{u, v} carrier

namespace AcyclicCategoryCat.Large

open CategoryTheory

instance : CoeSort (AcyclicCategoryCat.Large.{u, v}) (Type u) where
  coe V := V.carrier

instance (V : AcyclicCategoryCat.Large.{u, v}) : Quiver.{v + 1} V.carrier :=
  V.wit.quiver

instance (V : AcyclicCategoryCat.Large.{u, v}) : TopologicalOrder V.carrier :=
  V.wit.order

instance (V : AcyclicCategoryCat.Large.{u, v}) :
    QuiverEdgesIncrease V.carrier :=
  V.wit.edgesIncrease

instance (V : AcyclicCategoryCat.Large.{u, v}) :
    SemicategoryStruct V.carrier :=
  V.wit.semicat

instance (V : AcyclicCategoryCat.Large.{u, v}) :
    AcyclicQuiver.{u, v} V.carrier where
  toQuiver := V.wit.quiver
  toPartialOrder := V.wit.order
  edgesIncrease := V.wit.edgesIncrease

instance (V : AcyclicCategoryCat.Large.{u, v}) : AcyclicCategory V.carrier where
  toSemicategoryStruct := V.wit.semicat

/-- Construct a large bundled acyclic category from a type with
    acyclic category structure. -/
def of (V : Type u) [q : AcyclicQuiver.{u, v} V] [c : AcyclicCategory V] :
    AcyclicCategoryCat.Large.{u, v} :=
  ⟨V, {
    quiver := q.toQuiver
    order := q.toPartialOrder
    edgesIncrease := q.edgesIncrease
    semicat := c.toSemicategoryStruct
  }⟩

instance : Category.{max u v} (AcyclicCategoryCat.Large.{u, v}) where
  Hom V W := AcyclicCategoryHom V.carrier W.carrier
  id V := AcyclicCategoryHom.id V.carrier
  comp {_ _ _} F G := AcyclicCategoryHom.comp F G
  id_comp {_ _} := AcyclicCategoryHom.id_comp
  comp_id {_ _} := AcyclicCategoryHom.comp_id
  assoc {_ _ _ _} := AcyclicCategoryHom.comp_assoc

end AcyclicCategoryCat.Large

/-- The small category of acyclic categories, where objects and
    morphisms are in the same universe. -/
abbrev AcyclicCategoryCat.Small := AcyclicCategoryCat.Large.{u, u}

/-- The default is the small category of acyclic categories. -/
abbrev AcyclicCategoryCat := AcyclicCategoryCat.Small

open CategoryTheory

/-- The property that an acyclic category is finite (has finitely
    many vertices and edges). -/
def IsFiniteAcyclicCategory : ObjectProperty AcyclicCategoryCat :=
  fun V => Nonempty (FinQuiverWitness V.carrier)

/-- The full subcategory of finite acyclic categories. -/
abbrev FiniteAcyclicCategoryCat :=
  IsFiniteAcyclicCategory.FullSubcategory

namespace FiniteAcyclicCategoryCat

/-- The inclusion functor from finite acyclic categories to all acyclic
    categories. -/
abbrev ι : FiniteAcyclicCategoryCat ⥤ AcyclicCategoryCat :=
  IsFiniteAcyclicCategory.ι

end FiniteAcyclicCategoryCat

namespace AcyclicCategory

open CategoryTheory

section CategoryTheory

variable {V : Type u} [AcyclicQuiver.{u, u} V] [AcyclicCategory V]

/-- Morphisms in the category obtained by adjoining identities to an
    acyclic category. A morphism is either an identity or a morphism
    from the underlying acyclic category. -/
inductive AdjoinedIdHom : V → V → Type u where
  | id (a : V) : AdjoinedIdHom a a
  | hom {a b : V} (f : a ⟶ b) : AdjoinedIdHom a b

namespace AdjoinedIdHom

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

end AdjoinedIdHom

/-- The category structure obtained by adjoining identities to an
    acyclic category. -/
instance adjoinedIdCategory : Category V where
  Hom := AdjoinedIdHom
  id a := AdjoinedIdHom.id a
  comp := AdjoinedIdHom.comp
  id_comp := AdjoinedIdHom.id_comp
  comp_id := AdjoinedIdHom.comp_id
  assoc := AdjoinedIdHom.comp_assoc

/-- Lift an acyclic category homomorphism to a functor between the
    categories with adjoined identities. -/
def liftToFunctor {U : Type u} {V : Type u}
    [AcyclicQuiver.{u, u} U] [AcyclicCategory U]
    [AcyclicQuiver.{u, u} V] [AcyclicCategory V]
    (F : AcyclicCategoryHom U V) : U ⥤ V where
  obj := F.toSemifunctor.obj
  map := fun {a b} f =>
    match f with
    | AdjoinedIdHom.id _ => AdjoinedIdHom.id (F.toSemifunctor.obj a)
    | AdjoinedIdHom.hom g => AdjoinedIdHom.hom (F.toSemifunctor.map g)
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
        change AdjoinedIdHom.hom (F.toSemifunctor.map (Semicategory.comp f' g')) =
          AdjoinedIdHom.comp (AdjoinedIdHom.hom (F.toSemifunctor.map f'))
            (AdjoinedIdHom.hom (F.toSemifunctor.map g'))
        simp only [AdjoinedIdHom.comp, F.toSemifunctor.map_comp]

/-- The inclusion functor from acyclic categories to categories. -/
def toCat : AcyclicCategoryCat ⥤ Cat where
  obj V := ⟨V.carrier, adjoinedIdCategory⟩
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
      simp only [CategoryStruct.comp, CategoryTheory.Functor.comp_obj, eqToHom_refl]
      cases f <;> rfl

/-- The composed inclusion functor from finite acyclic categories to
    categories. -/
def finiteAcyclicCatToCat : FiniteAcyclicCategoryCat ⥤ Cat :=
  FiniteAcyclicCategoryCat.ι ⋙ toCat

end CategoryTheory

end AcyclicCategory

end GebLean
