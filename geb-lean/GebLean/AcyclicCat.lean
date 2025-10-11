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
    morphisms. Identities can be added later to form a category.

    Note: We store the semicategory structure directly rather than
    extending Semicategory, to avoid diamond problems with the Quiver
    instance. -/
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

instance (V : AcyclicCategoryCat.Large.{u, v}) : QuiverEdgesIncrease V.carrier :=
  V.wit.edgesIncrease

instance (V : AcyclicCategoryCat.Large.{u, v}) : SemicategoryStruct V.carrier :=
  V.wit.semicat

instance (V : AcyclicCategoryCat.Large.{u, v}) : AcyclicQuiver.{u, v} V.carrier where
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

variable {V : Type u} [AcyclicQuiver V]

end AcyclicCategory

end GebLean
