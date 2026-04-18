import GebLean.PresheafPRA

/-!
# Tests for (I, J)-Naturality of praPositionsFunctor

Type-signature sanity checks and small-example tests for
`praPositionsNat` and friends in `GebLean.PresheafPRA`.
-/

open GebLean CategoryTheory

attribute [local instance] CategoryTheory.uliftCategory

/-! ## Type-signature sanity -/

-- praPositionsNat has the expected shape.
example :
    presheafPRACatBifunctor.{0, 0, 0, 0, 0, 0} ⟶
      praPositionsNatTarget.{0, 0, 0, 0, 0, 0} :=
  praPositionsNat.{0, 0, 0, 0, 0, 0}

-- praPositionsNatTarget has the expected shape.
example :
    Cat.{0, 0}ᵒᵖ ⥤
      (Cat.{0, 0}ᵒᵖ ⥤ Cat.{0, 1}) :=
  praPositionsNatTarget.{0, 0, 0, 0, 0, 0}

/-! ## Definitional collapse via the bridge lemma -/

section CollapseTest

-- Bridge lemma applies at a concrete small base-pair.
example :
    ((praPositionsNat.{0, 0, 0, 0, 0, 0}.app
        (Opposite.op (Cat.of (PUnitᵒᵖ : Type 0)))).app
      (Opposite.op (Cat.of (PUnitᵒᵖ : Type 0)))).toFunctor =
      (Functor.whiskeringRight PUnitᵒᵖ _ _).obj
        (ccrNewIndexFunctor.{1, 0, 0}
          (↑(presheafCat.{0, 0, 0} PUnit))) ⋙
        CategoryTheory.ULift.upFunctor ⋙
        CategoryTheory.ULiftHom.up :=
  praPositionsNat_app_eq_presheafCatFunctor.{0, 0, 0, 0, 0, 0}
    PUnit PUnit

end CollapseTest
