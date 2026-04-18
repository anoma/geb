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
