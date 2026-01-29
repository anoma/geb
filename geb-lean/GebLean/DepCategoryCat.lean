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

/-- Each object has an identity morphism (with witness). Uses `PSigma` to
    handle the case where `idT` is `Prop`-valued. -/
def DepCategoryData.IdExists.{u₁, u₂, u₃, u₄}
    (D : DepCategoryData.{u₁, u₂, u₃, u₄}) : Sort (max 1 u₁ u₂ u₃) :=
  ∀ (o : D.objT), PSigma (D.idT (o := o))

/-- Each object has at most one identity morphism. -/
def DepCategoryData.IdUnique.{u₁, u₂, u₃, u₄}
    (D : DepCategoryData.{u₁, u₂, u₃, u₄}) : Prop :=
  ∀ (o : D.objT) (m₁ m₂ : D.morT o o), D.idT m₁ → D.idT m₂ → m₁ = m₂

/-- Each composable pair has a composite (with witness). Uses `PSigma` to
    handle the case where `compT` is `Prop`-valued. -/
def DepCategoryData.CompExists.{u₁, u₂, u₃, u₄}
    (D : DepCategoryData.{u₁, u₂, u₃, u₄}) : Sort (max 1 u₁ u₂ u₄) :=
  ∀ {a b c : D.objT} (f : D.morT a b) (g : D.morT b c),
    PSigma (D.compT f g)

/-- Each composable pair has at most one composite. -/
def DepCategoryData.CompUnique.{u₁, u₂, u₃, u₄}
    (D : DepCategoryData.{u₁, u₂, u₃, u₄}) : Prop :=
  ∀ {a b c : D.objT} (f : D.morT a b) (g : D.morT b c) (h₁ h₂ : D.morT a c),
    D.compT f g h₁ → D.compT f g h₂ → h₁ = h₂

/-- The identity relation is functional (with witnesses). -/
structure DepCategoryData.IdFunctional.{u₁, u₂, u₃, u₄}
    (D : DepCategoryData.{u₁, u₂, u₃, u₄}) : Sort (max 1 u₁ u₂ u₃) where
  exists_ : D.IdExists
  unique : D.IdUnique

/-- The composition relation is functional (with witnesses). -/
structure DepCategoryData.CompFunctional.{u₁, u₂, u₃, u₄}
    (D : DepCategoryData.{u₁, u₂, u₃, u₄}) : Sort (max 1 u₁ u₂ u₄) where
  exists_ : D.CompExists
  unique : D.CompUnique

/-- Both identity and composition relations are functional (with witnesses). -/
structure DepCategoryData.Functional.{u₁, u₂, u₃, u₄}
    (D : DepCategoryData.{u₁, u₂, u₃, u₄}) : Sort (max 1 u₁ u₂ u₃ u₄) where
  id : D.IdFunctional
  comp : D.CompFunctional

end FunctionalityConditions

section FunctionalCategoryEquiv

/-- A `DepCategoryData` bundled with its functionality witnesses.
    These are the objects that have the data of a category (without laws). -/
structure DepFunctionalCategory.{u₁, u₂, u₃, u₄} : Type (max u₁ u₂ u₃ u₄) where
  /-- The underlying category data -/
  data : DepCategoryData.{u₁, u₂, u₃, u₄}
  /-- The functionality witnesses -/
  functional : data.Functional

/-- Convert a `BundledCategoryStruct` to a `DepCategoryData`. -/
def bundledCategoryStructToDepData.{v, u} (C : BundledCategoryStruct.{v, u}) :
    DepCategoryData :=
  letI : CategoryStruct C := BundledCategoryStruct.instCategoryStruct C
  { objT := C
    morT := fun a b => a ⟶ b
    idT := fun {o} m => m = 𝟙 o
    compT := fun {_ _ _} f g h => h = f ≫ g }

/-- A `BundledCategoryStruct` converted to `DepCategoryData` satisfies
    `IdExists`. -/
def bundledCategoryStructToDepData_idExists (C : BundledCategoryStruct) :
    (bundledCategoryStructToDepData C).IdExists := fun o =>
  ⟨@CategoryStruct.id C (BundledCategoryStruct.instCategoryStruct C) o, rfl⟩

/-- A `BundledCategoryStruct` converted to `DepCategoryData` satisfies
    `IdUnique`. -/
theorem bundledCategoryStructToDepData_idUnique (C : BundledCategoryStruct) :
    (bundledCategoryStructToDepData C).IdUnique := fun _ _ _ h₁ h₂ =>
  h₁.trans h₂.symm

/-- A `BundledCategoryStruct` converted to `DepCategoryData` satisfies
    `CompExists`. -/
def bundledCategoryStructToDepData_compExists (C : BundledCategoryStruct) :
    (bundledCategoryStructToDepData C).CompExists := fun f g =>
  ⟨@CategoryStruct.comp C (BundledCategoryStruct.instCategoryStruct C) _ _ _ f g,
   rfl⟩

/-- A `BundledCategoryStruct` converted to `DepCategoryData` satisfies
    `CompUnique`. -/
theorem bundledCategoryStructToDepData_compUnique (C : BundledCategoryStruct) :
    (bundledCategoryStructToDepData C).CompUnique := fun _ _ _ _ p₁ p₂ =>
  p₁.trans p₂.symm

/-- A `BundledCategoryStruct` converted to `DepCategoryData` satisfies
    `Functional`. -/
def bundledCategoryStructToDepData_functional (C : BundledCategoryStruct) :
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
    DepFunctionalCategory where
  data := bundledCategoryStructToDepData C
  functional := bundledCategoryStructToDepData_functional C

/-- Given a `DepFunctionalCategory`, extract the identity morphism for an
    object using the functionality condition. -/
def DepFunctionalCategory.idMor (D : DepFunctionalCategory)
    (o : D.data.objT) : D.data.morT o o :=
  (D.functional.id.exists_ o).fst

/-- The identity morphism satisfies `idT`. -/
def DepFunctionalCategory.idMor_spec.{u₁, u₂, u₃, u₄}
    (D : DepFunctionalCategory.{u₁, u₂, u₃, u₄})
    (o : D.data.objT) : D.data.idT (D.idMor o) :=
  (D.functional.id.exists_ o).snd

/-- Given a `DepFunctionalCategory`, extract the composite morphism for a
    composable pair using the functionality condition. -/
def DepFunctionalCategory.compMor (D : DepFunctionalCategory)
    {a b c : D.data.objT} (f : D.data.morT a b) (g : D.data.morT b c) :
    D.data.morT a c :=
  (D.functional.comp.exists_ f g).fst

/-- The composite morphism satisfies `compT`. -/
def DepFunctionalCategory.compMor_spec.{u₁, u₂, u₃, u₄}
    (D : DepFunctionalCategory.{u₁, u₂, u₃, u₄})
    {a b c : D.data.objT} (f : D.data.morT a b) (g : D.data.morT b c) :
    D.data.compT f g (D.compMor f g) :=
  (D.functional.comp.exists_ f g).snd

/-- Convert a `DepFunctionalCategory` to a `CategoryStruct` instance on its
    object type. -/
def depFunctionalToCategoryStruct (D : DepFunctionalCategory) :
    CategoryStruct D.data.objT where
  Hom := D.data.morT
  id := D.idMor
  comp := D.compMor

/-- Convert a `DepFunctionalCategory` to a `BundledCategoryStruct`. -/
def depFunctionalToBundledCategoryStruct
    (D : DepFunctionalCategory) : BundledCategoryStruct :=
  @BundledCategoryStruct.of D.data.objT (depFunctionalToCategoryStruct D)

end FunctionalCategoryEquiv

end CategoryJudgments

end GebLean
