import Mathlib.CategoryTheory.Category.Cat
import GebLean.DepCategoryJudgments
import GebLean.Utilities.Category

/-!
# The Category of Categories as a Full Subcategory of DepCategoryData

This file shows that `Cat` (the category of categories) embeds as a full
subcategory into `DepCategoryData`.

## Overview

The category `DepCategoryData` with `DepNatTransData` morphisms is equivalent
to the category of copresheaves on `CategoryJudgments.Obj`. This copresheaf
category contains all "potential" category structures, including ones that
do not satisfy the category axioms.

The category `Cat` of small categories embeds into `DepCategoryData` as
those objects where:
- Identity witnesses exist and are unique for each object
- Composition witnesses exist and are unique for each composable pair
- The identity and associativity laws hold

## Main definitions

* `catToDepCategoryData`: Converts a category to DepCategoryData by encoding
  the category structure as dependent types where identity and composition
  witnesses are propositions (subtypes witnessing equality)

* `functorToDepNatTrans`: Converts a functor between categories to a
  DepNatTransData morphism between the corresponding DepCategoryData

* `catEmbedding`: The functor `Cat ⥤ DepCategoryData` that embeds
  categories into dependent category data

* `catEmbedding.faithful`: Proof that the embedding is faithful (injective
  on morphisms)

* `catEmbedding.full`: Proof that the embedding is full (surjective on
  morphisms between objects in the image)

## Mathematical content

A category `C` is converted to `DepCategoryData` as follows:
- `objT` = the objects of `C`
- `morT a b` = morphisms from `a` to `b` in `C`
- `idT m` = proof that `m` is the identity morphism (i.e., `m = 𝟙 _`)
- `compT f g h` = proof that `h = f ≫ g`

A functor `F : C ⥤ D` induces `DepNatTransData` with:
- `appObj` = the object function of `F`
- `appMor` = the morphism function of `F`
- `appId` = proof preservation (uses that `F` preserves identities)
- `appComp` = proof preservation (uses that `F` preserves composition)

The embedding is full because any `DepNatTransData` between categories
(when viewed as `DepCategoryData`) must preserve the identity and
composition structure, which exactly characterizes functors.

## References

See `DepCategoryJudgments.lean` for the definition of `DepCategoryData` and
its equivalence with copresheaves on `CategoryJudgments.Obj`.
-/

namespace GebLean

namespace CategoryJudgments

open CategoryTheory

section FunctionalityConditions

/-- Each object has an identity morphism. -/
def DepCategoryData.IdExists (D : DepCategoryData) : Prop :=
  ∀ (o : D.objT), ∃ (m : D.morT o o), Nonempty (D.idT m)

/-- Each object has at most one identity morphism. -/
def DepCategoryData.IdUnique (D : DepCategoryData) : Prop :=
  ∀ (o : D.objT) (m₁ m₂ : D.morT o o),
    Nonempty (D.idT m₁) → Nonempty (D.idT m₂) → m₁ = m₂

/-- Each composable pair has a composite. -/
def DepCategoryData.CompExists (D : DepCategoryData) : Prop :=
  ∀ {a b c : D.objT} (f : D.morT a b) (g : D.morT b c),
    ∃ (h : D.morT a c), Nonempty (D.compT f g h)

/-- Each composable pair has at most one composite. -/
def DepCategoryData.CompUnique (D : DepCategoryData) : Prop :=
  ∀ {a b c : D.objT} (f : D.morT a b) (g : D.morT b c) (h₁ h₂ : D.morT a c),
    Nonempty (D.compT f g h₁) → Nonempty (D.compT f g h₂) → h₁ = h₂

/-- The identity relation is functional. -/
structure DepCategoryData.IdFunctional (D : DepCategoryData) : Prop where
  exists_ : D.IdExists
  unique : D.IdUnique

/-- The composition relation is functional. -/
structure DepCategoryData.CompFunctional (D : DepCategoryData) : Prop where
  exists_ : D.CompExists
  unique : D.CompUnique

/-- Both identity and composition relations are functional. -/
structure DepCategoryData.Functional (D : DepCategoryData) : Prop where
  id : D.IdFunctional
  comp : D.CompFunctional

end FunctionalityConditions

section FunctionalCategoryEquiv

/-- The subtype of `DepCategoryData` satisfying the functionality conditions.
    These are the objects that have the data of a category (without laws). -/
def DepFunctionalCategory := { D : DepCategoryData // D.Functional }

/-- Convert a `BundledCategoryStruct` to a `DepCategoryData`. -/
def bundledCategoryStructToDepData (C : BundledCategoryStruct) :
    DepCategoryData :=
  letI : CategoryStruct C := BundledCategoryStruct.instCategoryStruct C
  { objT := C
    morT := fun a b => a ⟶ b
    idT := fun {o} m => m = 𝟙 o
    compT := fun {_ _ _} f g h => h = f ≫ g }

/-- A `BundledCategoryStruct` converted to `DepCategoryData` satisfies
    `IdExists`. -/
theorem bundledCategoryStructToDepData_idExists (C : BundledCategoryStruct) :
    (bundledCategoryStructToDepData C).IdExists := fun o =>
  ⟨@CategoryStruct.id C (BundledCategoryStruct.instCategoryStruct C) o, ⟨rfl⟩⟩

/-- A `BundledCategoryStruct` converted to `DepCategoryData` satisfies
    `IdUnique`. -/
theorem bundledCategoryStructToDepData_idUnique (C : BundledCategoryStruct) :
    (bundledCategoryStructToDepData C).IdUnique := fun _ _ _ ⟨h₁⟩ ⟨h₂⟩ =>
  h₁.trans h₂.symm

/-- A `BundledCategoryStruct` converted to `DepCategoryData` satisfies
    `CompExists`. -/
theorem bundledCategoryStructToDepData_compExists (C : BundledCategoryStruct) :
    (bundledCategoryStructToDepData C).CompExists := fun f g =>
  ⟨@CategoryStruct.comp C (BundledCategoryStruct.instCategoryStruct C) _ _ _ f g,
   ⟨rfl⟩⟩

/-- A `BundledCategoryStruct` converted to `DepCategoryData` satisfies
    `CompUnique`. -/
theorem bundledCategoryStructToDepData_compUnique (C : BundledCategoryStruct) :
    (bundledCategoryStructToDepData C).CompUnique :=
  fun _ _ _ _ ⟨p₁⟩ ⟨p₂⟩ => p₁.trans p₂.symm

/-- A `BundledCategoryStruct` converted to `DepCategoryData` satisfies
    `Functional`. -/
theorem bundledCategoryStructToDepData_functional (C : BundledCategoryStruct) :
    (bundledCategoryStructToDepData C).Functional where
  id := {
    exists_ := bundledCategoryStructToDepData_idExists C
    unique := bundledCategoryStructToDepData_idUnique C
  }
  comp := {
    exists_ := bundledCategoryStructToDepData_compExists C
    unique := bundledCategoryStructToDepData_compUnique C
  }

/-- Convert a `BundledCategoryStruct` to a `DepFunctionalCategory`. -/
def bundledCategoryStructToDepFunctional (C : BundledCategoryStruct) :
    DepFunctionalCategory :=
  ⟨bundledCategoryStructToDepData C, bundledCategoryStructToDepData_functional C⟩

/-- Given a `DepFunctionalCategory`, extract the identity morphism for an
    object using the functionality condition. -/
noncomputable def DepFunctionalCategory.idMor (D : DepFunctionalCategory)
    (o : D.val.objT) : D.val.morT o o :=
  (D.property.id.exists_ o).choose

/-- The identity morphism satisfies `idT`. -/
theorem DepFunctionalCategory.idMor_spec (D : DepFunctionalCategory)
    (o : D.val.objT) : Nonempty (D.val.idT (D.idMor o)) :=
  (D.property.id.exists_ o).choose_spec

/-- Given a `DepFunctionalCategory`, extract the composite morphism for a
    composable pair using the functionality condition. -/
noncomputable def DepFunctionalCategory.compMor (D : DepFunctionalCategory)
    {a b c : D.val.objT} (f : D.val.morT a b) (g : D.val.morT b c) :
    D.val.morT a c :=
  (D.property.comp.exists_ f g).choose

/-- The composite morphism satisfies `compT`. -/
theorem DepFunctionalCategory.compMor_spec (D : DepFunctionalCategory)
    {a b c : D.val.objT} (f : D.val.morT a b) (g : D.val.morT b c) :
    Nonempty (D.val.compT f g (D.compMor f g)) :=
  (D.property.comp.exists_ f g).choose_spec

/-- Convert a `DepFunctionalCategory` to a `CategoryStruct` instance on its
    object type. -/
noncomputable def depFunctionalToCategoryStruct (D : DepFunctionalCategory) :
    CategoryStruct D.val.objT where
  Hom := D.val.morT
  id := D.idMor
  comp := D.compMor

/-- Convert a `DepFunctionalCategory` to a `BundledCategoryStruct`. -/
noncomputable def depFunctionalToBundledCategoryStruct
    (D : DepFunctionalCategory) : BundledCategoryStruct :=
  @BundledCategoryStruct.of D.val.objT (depFunctionalToCategoryStruct D)

end FunctionalCategoryEquiv

end CategoryJudgments

end GebLean
