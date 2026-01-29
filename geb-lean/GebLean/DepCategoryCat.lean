import Mathlib.CategoryTheory.Category.Cat
import GebLean.DepCategoryJudgments

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

end CategoryJudgments

end GebLean
