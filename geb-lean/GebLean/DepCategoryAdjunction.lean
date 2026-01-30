import GebLean.DepCategoryCat
import GebLean.Utilities.SetoidCat
import Mathlib.Data.Setoid.Basic

/-!
# Reflective Adjunction from Cat to DepCategoryData

This file constructs the reflective adjunction showing that `Cat` (the category
of categories) is a reflective subcategory of `DepCategoryData`.

## Overview

The file `DepCategoryCat.lean` establishes that `DepCategoryCat` (a full
subcategory of `DepCategoryData` satisfying existence, uniqueness, subsingleton,
and category law conditions) is equivalent to mathlib's `Cat`.

This file constructs the reflective adjunction by building composable reflective
inclusions for each property:

* `WitnessSubsingleton`: Reflective inclusion by truncating witness types
* `Unique`: Reflective inclusion by quotienting morphisms
* Existence + CategoryLaws: Handled together

These reflections are parameterized to work at any level of the subcategory
chain.

## References

See `DepCategoryCat.lean` for the definition of `DepCategoryCat` and its
equivalence with `Cat`.
-/

namespace GebLean

namespace CategoryJudgments

open CategoryTheory

/-! ## WitnessSubsingleton Reflection

This section constructs the reflective inclusion for adding the
`WitnessSubsingleton` property. The reflector truncates witness types to
propositions, making them subsingletons.

The construction is parameterized over any category with a fully faithful
functor to `DepCategoryData`, allowing it to be applied at any level of
the subcategory chain.
-/

section WitnessSubsingletonReflection

/-- Truncate the witness types of a `DepCategoryData` to subsingletons.
    This replaces `idT` and `compT` with their quotients by the total relation
    (all elements related), making them subsingletons while staying in the
    same universe and remaining constructive. -/
def DepCategoryData.truncateWitnesses.{u₁, u₂, u₃, u₄}
    (D : DepCategoryData.{u₁, u₂, u₃, u₄}) : DepCategoryData.{u₁, u₂, u₃, u₄} where
  objT := D.objT
  morT := D.morT
  idT := fun m => Quotient (@trueSetoid (D.idT m))
  compT := fun f g h => Quotient (@trueSetoid (D.compT f g h))

/-- Truncated witness types satisfy `IdSubsingleton`. -/
theorem DepCategoryData.truncateWitnesses_idSubsingleton
    (D : DepCategoryData) : D.truncateWitnesses.IdSubsingleton :=
  fun _ _ => Quotient.trueSetoid_subsingleton (D.idT _)

/-- Truncated witness types satisfy `CompSubsingleton`. -/
theorem DepCategoryData.truncateWitnesses_compSubsingleton
    (D : DepCategoryData) : D.truncateWitnesses.CompSubsingleton :=
  fun _ _ _ {f} {g} {h} => Quotient.trueSetoid_subsingleton (D.compT f g h)

/-- Truncated witness types satisfy `WitnessSubsingleton`. -/
def DepCategoryData.truncateWitnesses_witnessSubsingleton
    (D : DepCategoryData) : D.truncateWitnesses.WitnessSubsingleton where
  id := D.truncateWitnesses_idSubsingleton
  comp := D.truncateWitnesses_compSubsingleton

/-- The unit morphism from `D` to `truncateWitnesses D` in `DepCategoryData`.
    This maps witnesses into the quotient. -/
def DepCategoryData.truncateWitnessesUnit (D : DepCategoryData) :
    DepNatTransData D D.truncateWitnesses where
  appObj := _root_.id
  appMor := _root_.id
  appId := fun wit => Quotient.mk trueSetoid wit
  appComp := fun wit => Quotient.mk trueSetoid wit

/-- The truncation functor on `DepCategoryData`. Stays in the same universe. -/
def truncateWitnessesFunctor.{u₁, u₂, u₃, u₄} :
    DepCategoryData.{u₁, u₂, u₃, u₄} ⥤ DepCategoryData.{u₁, u₂, u₃, u₄} where
  obj := DepCategoryData.truncateWitnesses
  map := fun {D E} α => {
    appObj := α.appObj
    appMor := α.appMor
    appId := fun q => Quotient.map α.appId (fun _ _ _ => trivial) q
    appComp := fun q => Quotient.map α.appComp (fun _ _ _ => trivial) q
  }
  map_id := fun D => by
    apply DepNatTransData.ext
    · rfl
    · rfl
    · apply heq_of_eq
      funext _ m w
      exact @Subsingleton.elim _ (Quotient.trueSetoid_subsingleton (D.idT m)) _ _
    · apply heq_of_eq
      funext _ _ _ f g h w
      exact @Subsingleton.elim _ (Quotient.trueSetoid_subsingleton (D.compT f g h)) _ _
  map_comp := fun {X Y Z} α β => by
    apply DepNatTransData.ext
    · rfl
    · rfl
    · apply heq_of_eq
      funext _ m w
      exact @Subsingleton.elim _ (Quotient.trueSetoid_subsingleton (Z.idT _)) _ _
    · apply heq_of_eq
      funext _ _ _ f g h w
      exact @Subsingleton.elim _ (Quotient.trueSetoid_subsingleton (Z.compT _ _ _)) _ _

/-- For a `DepCategoryData` already satisfying `WitnessSubsingleton`, the counit
    maps from the truncated version back to the original. Since the witness types
    are already subsingletons, `Quotient.lift` with the identity recovers the
    original elements. -/
def DepCategoryData.truncateWitnessesCounit {D : DepCategoryData}
    (h : D.WitnessSubsingleton) : DepNatTransData D.truncateWitnesses D where
  appObj := _root_.id
  appMor := _root_.id
  appId := Quotient.lift _root_.id
    (fun a b _ => @Subsingleton.elim _ (h.id _ _) a b)
  appComp := Quotient.lift _root_.id
    (fun a b _ => @Subsingleton.elim _ (h.comp _ _ _) a b)

/-- `WitnessSubsingleton` as an `ObjectProperty` on `DepCategoryData`. -/
def witnessSubsingletonProperty.{u₁, u₂, u₃, u₄} :
    ObjectProperty DepCategoryData.{u₁, u₂, u₃, u₄} :=
  DepCategoryData.WitnessSubsingleton

/-- The full subcategory of `DepCategoryData` satisfying `WitnessSubsingleton`. -/
abbrev DepCategoryDataWS.{u₁, u₂, u₃, u₄} : Type _ :=
  ObjectProperty.FullSubcategory witnessSubsingletonProperty.{u₁, u₂, u₃, u₄}

/-- The inclusion functor from `DepCategoryDataWS` to `DepCategoryData`. -/
abbrev depCategoryDataWSIncl.{u₁, u₂, u₃, u₄} :
    DepCategoryDataWS.{u₁, u₂, u₃, u₄} ⥤ DepCategoryData.{u₁, u₂, u₃, u₄} :=
  witnessSubsingletonProperty.ι

/-- The truncation functor lifts to `DepCategoryDataWS`. -/
def truncateWitnessesFunctorToWS.{u₁, u₂, u₃, u₄} :
    DepCategoryData.{u₁, u₂, u₃, u₄} ⥤ DepCategoryDataWS.{u₁, u₂, u₃, u₄} where
  obj := fun D => ⟨D.truncateWitnesses, D.truncateWitnesses_witnessSubsingleton⟩
  map := fun {D E} α => ObjectProperty.homMk (truncateWitnessesFunctor.map α)
  map_id := fun D => by
    apply ObjectProperty.hom_ext
    exact truncateWitnessesFunctor.map_id D
  map_comp := fun α β => by
    apply ObjectProperty.hom_ext
    exact truncateWitnessesFunctor.map_comp α β

end WitnessSubsingletonReflection

end CategoryJudgments

end GebLean
