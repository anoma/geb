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

universe u v

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
structure AcyclicCategoryHom (U V : Type u) [AcyclicQuiver U]
    [AcyclicCategory U] [AcyclicQuiver V] [AcyclicCategory V] where
  /-- The underlying semifunctor -/
  toSemifunctor : Semifunctor U V
  /-- The object map preserves the order -/
  obj_mono : PrefunctorPreservesOrder toSemifunctor.toPrefunctor

namespace AcyclicCategoryHom

variable {U V W : Type u} [AcyclicQuiver U] [AcyclicCategory U]
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

/-- The category of acyclic categories (as a small category where
    objects and morphisms are in the same universe). We bundle an
    acyclic quiver with a semicategory structure. -/
structure AcyclicCategoryCat : Type (u + 1) where
  /-- The underlying acyclic quiver -/
  toAcyclicQuiverCat : AcyclicQuiverCat
  /-- The semicategory structure -/
  semicat : @SemicategoryStruct toAcyclicQuiverCat.carrier
    toAcyclicQuiverCat.quiver

instance instAcyclicCategoryCatQuiver (V : AcyclicCategoryCat) :
    Quiver V.toAcyclicQuiverCat.carrier :=
  V.toAcyclicQuiverCat.quiver
instance instAcyclicCategoryCatOrder (V : AcyclicCategoryCat) :
    TopologicalOrder V.toAcyclicQuiverCat.carrier :=
  V.toAcyclicQuiverCat.order
instance instAcyclicCategoryCatEdgesIncrease (V : AcyclicCategoryCat) :
    QuiverEdgesIncrease V.toAcyclicQuiverCat.carrier :=
  V.toAcyclicQuiverCat.edgesIncrease
instance instAcyclicCategoryCatSemicategoryStruct
    (V : AcyclicCategoryCat) :
    SemicategoryStruct V.toAcyclicQuiverCat.carrier :=
  V.semicat

instance instAcyclicCategoryCatAcyclicQuiver (V : AcyclicCategoryCat) :
    AcyclicQuiver V.toAcyclicQuiverCat.carrier where
  edgesIncrease := V.toAcyclicQuiverCat.edgesIncrease

instance instAcyclicCategoryCatAcyclicCategory (V : AcyclicCategoryCat) :
    AcyclicCategory V.toAcyclicQuiverCat.carrier where
  toSemicategoryStruct := V.semicat

namespace AcyclicCategoryCat

open CategoryTheory

instance : CoeSort AcyclicCategoryCat (Type u) where
  coe V := V.toAcyclicQuiverCat.carrier

/-- Construct a bundled acyclic category from a type with an acyclic
    category instance. -/
def of (V : Type u) [q : Quiver.{u} V] [o : TopologicalOrder V]
    (ei : QuiverEdgesIncrease V) (sc : SemicategoryStruct V) :
    AcyclicCategoryCat :=
  ⟨⟨V, q, o, ei⟩, sc⟩

instance : Category.{u} AcyclicCategoryCat where
  Hom V W := AcyclicCategoryHom.{u} V W
  id V := AcyclicCategoryHom.id V
  comp {_ _ _} F G := AcyclicCategoryHom.comp F G
  id_comp {_ _} := AcyclicCategoryHom.id_comp
  comp_id {_ _} := AcyclicCategoryHom.comp_id
  assoc {_ _ _ _} := AcyclicCategoryHom.comp_assoc

end AcyclicCategoryCat

open CategoryTheory

/-- The property that an acyclic category is finite (has finitely many
    vertices and edges). -/
def IsFiniteAcyclicCategory : ObjectProperty AcyclicCategoryCat :=
  fun V => Nonempty (FinQuiverWitness V.toAcyclicQuiverCat.carrier)

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
