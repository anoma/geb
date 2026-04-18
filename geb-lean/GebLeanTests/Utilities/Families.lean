import GebLean.Utilities.Families

/-!
# Tests for C-Natural Packaging of ccrNewIndex and ccrNewFamily

Type-signature sanity checks and small-example tests for the
`CCRNaturalPackaging` section of `GebLean.Utilities.Families`.
-/

open GebLean CategoryTheory

/-! ## Type-signature sanity -/

-- ccrNewIndexNat has the expected shape
example : coprodCovarRepFunctor.{0, 0, 0} ⟶
    (Functor.const Cat.{0, 0}).obj typeCatLift.{0, 0, 0} :=
  ccrNewIndexNat.{0, 0, 0}

-- ccrElementsFunctor has the expected shape
example : Cat.{0, 0} ⥤ Cat.{0, 1} :=
  ccrElementsFunctor.{0, 0, 0}

-- ccrNewFamilyNat has the expected shape
example :
    ccrElementsFunctor.{0, 0, 0} ⟶
      ccrNewFamilyNatTarget.{0, 0, 0} :=
  ccrNewFamilyNat.{0, 0, 0}

/-! ## Definitional collapse to existing utilities -/

section CollapseTests

attribute [local instance] CategoryTheory.uliftCategory

example :
    (ccrNewIndexNat.{0, 0, 0}.app (Cat.of PUnit)).toFunctor =
      ccrNewIndexNatFunctor.{0, 0, 0} PUnit := by
  rfl

example :
    (ccrNewFamilyNat.{0, 0, 0}.app (Cat.of PUnit)).toFunctor =
      ccrNewFamilyFunctor.{0, 0, 0} PUnit ⋙
        CategoryTheory.ULift.upFunctor ⋙
        CategoryTheory.ULiftHom.up :=
  ccrNewFamilyNat_app_eq_ccrNewFamilyFunctor.{0, 0, 0} PUnit

end CollapseTests

/-! ## Naturality and functoriality, small examples -/

section NatAndFunctoriality

-- A concrete functor between small base categories.
private def baseFunctor : Cat.of PUnit ⟶ Cat.of PUnit :=
  (CategoryTheory.Functor.id _).toCatHom

-- Naturality of ccrNewIndexNat at baseFunctor holds by rfl
-- because coprodCovarRepFunctor.map preserves the index type.
example :
    (coprodCovarRepFunctor.{0, 0, 0}.map baseFunctor).toFunctor ⋙
      (ccrNewIndexNat.{0, 0, 0}.app _).toFunctor =
    (ccrNewIndexNat.{0, 0, 0}.app _).toFunctor := by
  rfl

-- Functoriality of ccrElementsFunctor: map_id is rfl-style
example :
    ccrElementsFunctor.{0, 0, 0}.map (𝟙 (Cat.of PUnit)) =
      𝟙 (ccrElementsFunctor.{0, 0, 0}.obj (Cat.of PUnit)) := by
  rw [CategoryTheory.Functor.map_id]

-- Functoriality of ccrElementsFunctor: map_comp
example :
    ccrElementsFunctor.{0, 0, 0}.map
      (baseFunctor ≫ baseFunctor) =
    ccrElementsFunctor.{0, 0, 0}.map baseFunctor ≫
      ccrElementsFunctor.{0, 0, 0}.map baseFunctor := by
  rw [CategoryTheory.Functor.map_comp]

end NatAndFunctoriality

/-! ## Universe polymorphism -/

section UniversePoly

-- Exercise ccrNewIndexNat at u := 1, v := 0, w := 0
example : coprodCovarRepFunctor.{1, 0, 0} ⟶
    (Functor.const Cat.{0, 1}).obj typeCatLift.{1, 0, 0} :=
  ccrNewIndexNat.{1, 0, 0}

-- Exercise ccrNewFamilyNat at u := 1, v := 0, w := 0
example :
    ccrElementsFunctor.{1, 0, 0} ⟶
      ccrNewFamilyNatTarget.{1, 0, 0} :=
  ccrNewFamilyNat.{1, 0, 0}

end UniversePoly
