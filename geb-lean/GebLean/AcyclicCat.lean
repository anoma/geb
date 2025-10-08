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

/-- Morphisms of acyclic quivers and categories preserve the strict
    ordering on vertices via their object maps. -/
abbrev PrefunctorPreservesOrder {V W : Type u} [Quiver V] [Quiver W]
    [LinearOrder V] [LinearOrder W] (F : Prefunctor V W) :=
  StrictMono F.obj

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

/-- A finite semicategory has finitely many objects and morphisms. -/
class FiniteSemicategory (V : Type u) [Semicategory V] where
  toFiniteness : FinQuiverWitness V := by infer_instance

instance {V : Type u} [Semicategory V] [h : FiniteSemicategory V] :
    FinQuiverWitness V := h.toFiniteness

/-- An acyclic category is an acyclic quiver with a semicategory
    structure. The strict ordering ensures there are no identity
    morphisms. Identities can be added later to form a category. -/
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

theorem id_comp (F : AcyclicQuiverHom V W) : (id V).comp F = F := by
  apply ext
  rfl

theorem comp_id (F : AcyclicQuiverHom V W) : F.comp (id W) = F := by
  apply ext
  rfl

theorem comp_assoc {X : Type u} [AcyclicQuiver X]
    (F : AcyclicQuiverHom U V) (G : AcyclicQuiverHom V W)
    (H : AcyclicQuiverHom W X) :
    (F.comp G).comp H = F.comp (G.comp H) := by
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
  comp {_ _ _} F G := F.comp G
  id_comp {_ _} := AcyclicQuiverHom.id_comp
  comp_id {_ _} := AcyclicQuiverHom.comp_id
  assoc {_ _ _ _} := AcyclicQuiverHom.comp_assoc

end AcyclicQuiverCat

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

/-- A morphism of acyclic categories is a semifunctor that also
    preserves the strict order on objects. -/
structure AcyclicCategoryHom (U V : Type u) [AcyclicQuiver U]
    [AcyclicCategory U] [AcyclicQuiver V] [AcyclicCategory V]
    extends Semifunctor U V where
  /-- The object map preserves the order -/
  obj_mono : PrefunctorPreservesOrder toPrefunctor

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

theorem id_comp (F : AcyclicCategoryHom V W) : (id V).comp F = F := by
  apply ext
  apply Semifunctor.ext
  rfl

theorem comp_id (F : AcyclicCategoryHom V W) : F.comp (id W) = F := by
  apply ext
  apply Semifunctor.ext
  rfl

theorem comp_assoc {X : Type u} [AcyclicQuiver X] [AcyclicCategory X]
    (F : AcyclicCategoryHom U V) (G : AcyclicCategoryHom V W)
    (H : AcyclicCategoryHom W X) :
    (F.comp G).comp H = F.comp (G.comp H) := by
  apply ext
  apply Semifunctor.ext
  rfl

end AcyclicCategoryHom

/-- The category of acyclic categories (as a small category where objects
    and morphisms are in the same universe). We bundle the carrier,
    quiver, acyclic quiver, and semicategory structure. The
    `AcyclicCategory` instance is derived from these. -/
structure AcyclicCategoryCat : Type (u + 1) where
  /-- The type of objects. -/
  carrier : Type u
  [quiver : Quiver.{u} carrier]
  [acyclic : AcyclicQuiver.{u, u} carrier]
  [semicat : Semicategory.{u, u} carrier]

attribute [instance] AcyclicCategoryCat.quiver
  AcyclicCategoryCat.acyclic AcyclicCategoryCat.semicat

namespace AcyclicCategoryCat

open CategoryTheory

instance : CoeSort AcyclicCategoryCat (Type u) where
  coe V := V.carrier

/-- Since `AcyclicCategory` just extends `Semicategory`, we can derive
    it from the bundled fields. -/
instance (V : AcyclicCategoryCat) : AcyclicCategory V where
  toSemicategory := V.semicat

/-- Construct a bundled acyclic category from a type with an acyclic
    category instance. -/
def of (V : Type u) [Quiver.{u} V] [AcyclicQuiver.{u, u} V]
    [Semicategory.{u, u} V] [AcyclicCategory V] :
    AcyclicCategoryCat := ⟨V⟩

instance : Category.{u} AcyclicCategoryCat where
  Hom V W := AcyclicCategoryHom.{u} V W
  id V := AcyclicCategoryHom.id V
  comp {_ _ _} F G := F.comp G
  id_comp {_ _} := AcyclicCategoryHom.id_comp
  comp_id {_ _} := AcyclicCategoryHom.comp_id
  assoc {_ _ _ _} := AcyclicCategoryHom.comp_assoc

end AcyclicCategoryCat

namespace AcyclicCategory

open CategoryTheory

variable {V : Type u} [AcyclicQuiver V]

end AcyclicCategory
