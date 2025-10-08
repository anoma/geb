import Mathlib.Combinatorics.Quiver.Basic
import Mathlib.Combinatorics.Quiver.Path
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.Data.Fintype.Basic
import Mathlib.Order.Basic
import GebLean.FiniteQuiver
import GebLean.Semicategory

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
* `AcyclicCategory`: An acyclic quiver with a semicategory structure
* `FiniteAcyclicCategory`: A finite acyclic category
-/

universe u v

/-- An acyclic quiver is a quiver equipped with a strict total order
    on vertices such that every edge goes from a smaller to a larger
    vertex. This provides a topological sort, which proves the quiver
    is acyclic. -/
class AcyclicQuiver (V : Type u) extends Quiver.{v} V, LinearOrder V where
  /-- Every edge goes from a smaller vertex to a larger vertex -/
  edge_increases : ∀ {a b : V}, (a ⟶ b) → a < b

/-- Morphisms of acyclic quivers and categories preserve the strict
    ordering on vertices via their object maps. -/
abbrev PrefunctorPreservesOrder {V W : Type u} [Quiver V] [Quiver W]
    [LinearOrder V] [LinearOrder W] (F : Prefunctor V W) :=
  StrictMono F.obj

/-- A finite acyclic quiver has finitely many vertices and finitely
    many edges between each pair of vertices. -/
class FiniteAcyclicQuiver (V : Type u) [AcyclicQuiver V] where
  toFiniteness : FinQuiverWitness V := by infer_instance

instance {V : Type u} [AcyclicQuiver V] [h : FiniteAcyclicQuiver V] :
    FinQuiverWitness V := h.toFiniteness

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
structure AcyclicQuiverHom (V W : Type u) [AcyclicQuiver V]
    [AcyclicQuiver W] extends Prefunctor V W where
  /-- The vertex map preserves the order -/
  obj_mono : PrefunctorPreservesOrder toPrefunctor

namespace AcyclicQuiverHom

variable {U V W : Type u} [AcyclicQuiver U] [AcyclicQuiver V]
  [AcyclicQuiver W]

/-- The identity morphism of acyclic quivers. -/
def id (V : Type u) [AcyclicQuiver V] : AcyclicQuiverHom V V where
  toPrefunctor := Prefunctor.id V
  obj_mono := fun _ _ h => h

/-- Composition of morphisms of acyclic quivers. -/
def comp (F : AcyclicQuiverHom U V) (G : AcyclicQuiverHom V W) :
    AcyclicQuiverHom U W where
  toPrefunctor := F.toPrefunctor.comp G.toPrefunctor
  obj_mono := fun _ _ h => G.obj_mono (F.obj_mono h)

/-- Morphisms of acyclic quivers preserve the edge_increases
    property. -/
theorem map_edge_increases (F : AcyclicQuiverHom V W) {a b : V}
    (f : a ⟶ b) : F.obj a < F.obj b := by
  have hab : a < b := AcyclicQuiver.edge_increases f
  exact F.obj_mono hab

@[ext]
theorem ext {F G : AcyclicQuiverHom V W} (h : F.toPrefunctor = G.toPrefunctor) :
    F = G := by
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
  [quiver : Quiver.{u} carrier]
  [acyclic : AcyclicQuiver.{u, u} carrier]

attribute [instance] AcyclicQuiverCat.quiver AcyclicQuiverCat.acyclic

namespace AcyclicQuiverCat

open CategoryTheory

instance : CoeSort AcyclicQuiverCat (Type u) where
  coe V := V.carrier

/-- Construct a bundled acyclic quiver from a type with an acyclic
    quiver instance. -/
def of (V : Type u) [Quiver.{u} V] [AcyclicQuiver.{u, u} V] :
    AcyclicQuiverCat := ⟨V⟩

instance : Category.{u} AcyclicQuiverCat where
  Hom V W := AcyclicQuiverHom.{u, u} V W
  id V := AcyclicQuiverHom.id V
  comp {_ _ _} F G := AcyclicQuiverHom.comp F G
  id_comp {_ _} := AcyclicQuiverHom.id_comp
  comp_id {_ _} := AcyclicQuiverHom.comp_id
  assoc {_ _ _ _} := AcyclicQuiverHom.comp_assoc

end AcyclicQuiverCat

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
  toSemifunctor := F.toSemifunctor.comp G.toSemifunctor
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

/-- The category of acyclic categories (as a small category where objects
    and morphisms are in the same universe). We bundle the carrier,
    acyclic quiver, and acyclic category structure. -/
structure AcyclicCategoryCat : Type (u + 1) where
  /-- The type of objects. -/
  carrier : Type u
  [acyclic : AcyclicQuiver.{u, u} carrier]
  [acat : AcyclicCategory carrier]

attribute [instance] AcyclicCategoryCat.acyclic AcyclicCategoryCat.acat

namespace AcyclicCategoryCat

open CategoryTheory

instance : CoeSort AcyclicCategoryCat (Type u) where
  coe V := V.carrier

/-- Construct a bundled acyclic category from a type with an acyclic
    category instance. -/
def of (V : Type u) [Quiver.{u} V] [AcyclicQuiver.{u, u} V]
    [AcyclicCategory V] : AcyclicCategoryCat := ⟨V⟩

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
