import GebLean.DepCategoryCat
import GebLean.Utilities.SetoidCat
import Mathlib.CategoryTheory.Adjunction.Reflective
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

/-! ### Parameterized WitnessSubsingleton Reflection

The following definitions parameterize the WitnessSubsingleton reflection over any
category `C` with a functor `ι : C ⥤ DepCategoryData`. This allows the reflection
to be applied at any level of the subcategory chain.
-/

variable {C : Type*} [Category C] (ι : C ⥤ DepCategoryData)

/-- The `WitnessSubsingleton` property pulled back along a functor to
    `DepCategoryData`. An object `X : C` satisfies this property when
    `ι.obj X` satisfies `WitnessSubsingleton`. -/
def witnessSubsingletonPullback : ObjectProperty C :=
  fun X => (ι.obj X).WitnessSubsingleton

/-- The full subcategory of `C` where `ι.obj X` satisfies `WitnessSubsingleton`. -/
abbrev FullSubcategoryWS : Type _ :=
  ObjectProperty.FullSubcategory (witnessSubsingletonPullback ι)

/-- The inclusion from the WitnessSubsingleton full subcategory of `C` into `C`. -/
abbrev fullSubcategoryWSIncl : FullSubcategoryWS ι ⥤ C :=
  (witnessSubsingletonPullback ι).ι

/-- The truncation functor from `C` to `DepCategoryDataWS`, composing
    the given functor with the truncation. -/
def truncateWitnessesFrom : C ⥤ DepCategoryDataWS :=
  ι ⋙ truncateWitnessesFunctorToWS

/-- The unit natural transformation for the parameterized reflection.
    For each `X : C`, this gives a morphism `ι.obj X → truncateWitnesses (ι.obj X)`
    in `DepCategoryData`. -/
def truncateWitnessesUnitNat : ι ⟶ truncateWitnessesFrom ι ⋙ depCategoryDataWSIncl where
  app := fun X => (ι.obj X).truncateWitnessesUnit
  naturality := fun {X Y} f => by
    simp only [truncateWitnessesFrom, Functor.comp_obj, Functor.comp_map,
               truncateWitnessesFunctorToWS, depCategoryDataWSIncl,
               witnessSubsingletonProperty, ObjectProperty.ι_obj,
               ObjectProperty.ι_map, ObjectProperty.homMk_hom]
    apply DepNatTransData.ext
    · rfl
    · rfl
    · apply heq_of_eq
      funext _ m w
      exact @Subsingleton.elim _
        (Quotient.trueSetoid_subsingleton ((ι.obj Y).idT _)) _ _
    · apply heq_of_eq
      funext _ _ _ f' g h w
      exact @Subsingleton.elim _
        (Quotient.trueSetoid_subsingleton ((ι.obj Y).compT _ _ _)) _ _

/-- The counit for objects in the full subcategory. For `X : FullSubcategoryWS ι`,
    this gives a morphism `truncateWitnesses(ι.obj X.obj) → ι.obj X.obj` in
    `DepCategoryData`, using the fact that `ι.obj X.obj` satisfies
    `WitnessSubsingleton`. -/
def truncateWitnessesCounitAt (X : FullSubcategoryWS ι) :
    (ι.obj X.obj).truncateWitnesses ⟶ ι.obj X.obj :=
  DepCategoryData.truncateWitnessesCounit X.property

/-- The counit is a natural isomorphism when restricted to the full subcategory.
    This is because for objects satisfying `WitnessSubsingleton`, the truncation
    is isomorphic to the original via the unit and counit. -/
def truncateWitnessesCounitIsoAt (X : FullSubcategoryWS ι) :
    (ι.obj X.obj).truncateWitnesses ≅ ι.obj X.obj where
  hom := truncateWitnessesCounitAt ι X
  inv := (ι.obj X.obj).truncateWitnessesUnit
  hom_inv_id := by
    simp only [truncateWitnessesCounitAt]
    apply DepNatTransData.ext
    · rfl
    · rfl
    · apply heq_of_eq
      funext _ m w
      exact @Subsingleton.elim _
        (Quotient.trueSetoid_subsingleton ((ι.obj X.obj).idT _)) _ _
    · apply heq_of_eq
      funext _ _ _ f g h w
      exact @Subsingleton.elim _
        (Quotient.trueSetoid_subsingleton ((ι.obj X.obj).compT _ _ _)) _ _
  inv_hom_id := by
    simp only [truncateWitnessesCounitAt, DepCategoryData.truncateWitnessesCounit,
               DepCategoryData.truncateWitnessesUnit]
    apply DepNatTransData.ext
    · rfl
    · rfl
    · apply heq_of_eq
      funext _ m w
      rfl
    · apply heq_of_eq
      funext _ _ _ f g h w
      rfl

/-! ### Reflective Instance for WitnessSubsingleton

We complete the WitnessSubsingleton reflection by constructing the adjunction
and proving `Reflective depCategoryDataWSIncl`. -/

/-- The unit of the truncation adjunction: D → truncate(D). -/
def truncateWitnessesAdjUnit.{u₁, u₂, u₃, u₄} :
    (𝟭 DepCategoryData.{u₁, u₂, u₃, u₄}) ⟶
    truncateWitnessesFunctorToWS.{u₁, u₂, u₃, u₄} ⋙
    depCategoryDataWSIncl.{u₁, u₂, u₃, u₄} where
  app := fun D => D.truncateWitnessesUnit
  naturality := fun {D E} α => by
    simp only [Functor.id_obj, Functor.comp_obj, truncateWitnessesFunctorToWS,
               depCategoryDataWSIncl, witnessSubsingletonProperty,
               ObjectProperty.ι_obj, Functor.id_map, Functor.comp_map,
               ObjectProperty.ι_map, ObjectProperty.homMk_hom]
    apply DepNatTransData.ext
    · rfl
    · rfl
    · apply heq_of_eq
      funext o m w
      exact @Subsingleton.elim _
        (Quotient.trueSetoid_subsingleton (E.idT _)) _ _
    · apply heq_of_eq
      funext a b c f g h w
      exact @Subsingleton.elim _
        (Quotient.trueSetoid_subsingleton (E.compT _ _ _)) _ _

/-- The counit of the truncation adjunction: truncate(E) → E for E satisfying WS. -/
def truncateWitnessesAdjCounit.{u₁, u₂, u₃, u₄} :
    depCategoryDataWSIncl.{u₁, u₂, u₃, u₄} ⋙
    truncateWitnessesFunctorToWS.{u₁, u₂, u₃, u₄} ⟶
    (𝟭 DepCategoryDataWS.{u₁, u₂, u₃, u₄}) where
  app := fun E => ObjectProperty.homMk
    (DepCategoryData.truncateWitnessesCounit E.property)
  naturality := fun {E F} α => by
    apply ObjectProperty.hom_ext
    apply DepNatTransData.ext
    · rfl
    · rfl
    · apply heq_of_eq
      funext o m w
      induction w using Quotient.ind
      exact @Subsingleton.elim _
        (F.property.id (α.hom.appObj o) (α.hom.appMor m)) _ _
    · apply heq_of_eq
      funext a b c f g h w
      induction w using Quotient.ind
      exact @Subsingleton.elim _
        (F.property.comp (α.hom.appMor f) (α.hom.appMor g) (α.hom.appMor h)) _ _

/-- The adjunction between `truncateWitnessesFunctorToWS` and `depCategoryDataWSIncl`.
    This shows that `DepCategoryDataWS` is a reflective subcategory of `DepCategoryData`. -/
def truncateWitnessesAdjunction.{u₁, u₂, u₃, u₄} :
    truncateWitnessesFunctorToWS.{u₁, u₂, u₃, u₄} ⊣
    depCategoryDataWSIncl.{u₁, u₂, u₃, u₄} :=
  Adjunction.mkOfUnitCounit {
    unit := truncateWitnessesAdjUnit
    counit := truncateWitnessesAdjCounit
    left_triangle := by
      ext D
      simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.comp_obj,
                 Functor.id_obj, Functor.associator_hom_app, Functor.whiskerLeft_app,
                 NatTrans.id_app', truncateWitnessesFunctorToWS, depCategoryDataWSIncl,
                 witnessSubsingletonProperty, ObjectProperty.ι_obj,
                 truncateWitnessesAdjUnit, truncateWitnessesAdjCounit]
      apply DepNatTransData.ext
      · rfl
      · rfl
      · apply heq_of_eq
        funext o qm w
        exact @Subsingleton.elim _
          (Quotient.trueSetoid_subsingleton (D.idT _)) _ _
      · apply heq_of_eq
        funext a b c qf qg qh w
        exact @Subsingleton.elim _
          (Quotient.trueSetoid_subsingleton (D.compT _ _ _)) _ _
    right_triangle := by
      ext E
      simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.comp_obj,
                 Functor.id_obj, Functor.associator_inv_app, Functor.whiskerRight_app,
                 NatTrans.id_app', truncateWitnessesFunctorToWS, depCategoryDataWSIncl,
                 witnessSubsingletonProperty, ObjectProperty.ι_obj, ObjectProperty.ι_map,
                 truncateWitnessesAdjUnit, truncateWitnessesAdjCounit,
                 ObjectProperty.homMk_hom]
      apply DepNatTransData.ext
      · rfl
      · rfl
      · apply heq_of_eq
        funext o m w
        rfl
      · apply heq_of_eq
        funext a b c f g h w
        rfl
  }

/-- The counit component at E is an isomorphism. -/
def truncateWitnessesCounitIso.{u₁, u₂, u₃, u₄}
    (E : DepCategoryDataWS.{u₁, u₂, u₃, u₄}) :
    (depCategoryDataWSIncl.{u₁, u₂, u₃, u₄} ⋙
     truncateWitnessesFunctorToWS.{u₁, u₂, u₃, u₄}).obj E ≅ E where
  hom := truncateWitnessesAdjCounit.app E
  inv := ObjectProperty.homMk E.obj.truncateWitnessesUnit
  hom_inv_id := by
    apply ObjectProperty.hom_ext
    simp only [Functor.comp_obj, depCategoryDataWSIncl, witnessSubsingletonProperty,
               ObjectProperty.ι_obj, truncateWitnessesFunctorToWS,
               truncateWitnessesAdjCounit]
    apply DepNatTransData.ext
    · rfl
    · rfl
    · apply heq_of_eq
      funext o qm w
      exact @Subsingleton.elim _
        (Quotient.trueSetoid_subsingleton (E.obj.idT _)) _ _
    · apply heq_of_eq
      funext a b c qf qg qh w
      exact @Subsingleton.elim _
        (Quotient.trueSetoid_subsingleton (E.obj.compT _ _ _)) _ _
  inv_hom_id := by
    apply ObjectProperty.hom_ext
    simp only [Functor.comp_obj, depCategoryDataWSIncl, witnessSubsingletonProperty,
               ObjectProperty.ι_obj, truncateWitnessesFunctorToWS,
               truncateWitnessesAdjCounit]
    apply DepNatTransData.ext
    · rfl
    · rfl
    · apply heq_of_eq
      funext o m w
      rfl
    · apply heq_of_eq
      funext a b c f g h w
      rfl

/-- Each counit component is an isomorphism. -/
instance truncateWitnessesCounit_app_isIso.{u₁, u₂, u₃, u₄}
    (E : DepCategoryDataWS.{u₁, u₂, u₃, u₄}) :
    IsIso (truncateWitnessesAdjunction.{u₁, u₂, u₃, u₄}.counit.app E) :=
  (truncateWitnessesCounitIso E).isIso_hom

/-- The counit of the WitnessSubsingleton adjunction is a natural isomorphism. -/
instance truncateWitnessesCounit_isIso.{u₁, u₂, u₃, u₄} :
    IsIso truncateWitnessesAdjunction.{u₁, u₂, u₃, u₄}.counit :=
  NatIso.isIso_of_isIso_app _

/-- The inclusion of `DepCategoryDataWS` into `DepCategoryData` is reflective.
    This means `DepCategoryDataWS` is a reflective subcategory. -/
instance depCategoryDataWSIncl_reflective.{u₁, u₂, u₃, u₄} :
    Reflective depCategoryDataWSIncl.{u₁, u₂, u₃, u₄} where
  L := truncateWitnessesFunctorToWS
  adj := truncateWitnessesAdjunction

end WitnessSubsingletonReflection

end CategoryJudgments

end GebLean
