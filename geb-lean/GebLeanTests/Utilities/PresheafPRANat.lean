import GebLean.PresheafPRA

/-!
# Tests for (I, J)-Naturality of praPositionsNat

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

/-! ## Naturality in I and J, small examples -/

section NaturalityTests

-- The identity functor PUnitᵒᵖ ⥤ PUnitᵒᵖ, packaged as a Cat morphism.
private def baseIdFunctor :
    Cat.of (PUnitᵒᵖ : Type 0) ⟶ Cat.of (PUnitᵒᵖ : Type 0) :=
  (CategoryTheory.Functor.id _).toCatHom

-- Naturality of the inner nat-trans at fixed J = PUnitᵒᵖ,
-- morphism baseIdFunctor.op in I.
example :
    (presheafPRACatBifunctor.{0, 0, 0, 0, 0, 0}.obj
      (Opposite.op (Cat.of (PUnitᵒᵖ : Type 0)))).map baseIdFunctor.op ≫
        (praPositionsNat.{0, 0, 0, 0, 0, 0}.app
          (Opposite.op (Cat.of (PUnitᵒᵖ : Type 0)))).app
          (Opposite.op (Cat.of (PUnitᵒᵖ : Type 0))) =
      (praPositionsNat.{0, 0, 0, 0, 0, 0}.app
        (Opposite.op (Cat.of (PUnitᵒᵖ : Type 0)))).app
        (Opposite.op (Cat.of (PUnitᵒᵖ : Type 0))) ≫
        (praPositionsNatTarget.{0, 0, 0, 0, 0, 0}.obj
          (Opposite.op (Cat.of (PUnitᵒᵖ : Type 0)))).map baseIdFunctor.op :=
  (praPositionsNat.{0, 0, 0, 0, 0, 0}.app
    (Opposite.op (Cat.of (PUnitᵒᵖ : Type 0)))).naturality baseIdFunctor.op

-- Naturality of the outer nat-trans in J at baseIdFunctor.op.
example :
    presheafPRACatBifunctor.{0, 0, 0, 0, 0, 0}.map baseIdFunctor.op ≫
      praPositionsNat.{0, 0, 0, 0, 0, 0}.app
        (Opposite.op (Cat.of (PUnitᵒᵖ : Type 0))) =
      praPositionsNat.{0, 0, 0, 0, 0, 0}.app
        (Opposite.op (Cat.of (PUnitᵒᵖ : Type 0))) ≫
        praPositionsNatTarget.{0, 0, 0, 0, 0, 0}.map
          baseIdFunctor.op :=
  praPositionsNat.{0, 0, 0, 0, 0, 0}.naturality baseIdFunctor.op

end NaturalityTests

/-! ## Universe polymorphism -/

section UniversePoly

-- Exercise praPositionsNat at mixed universes
-- (u_I := 1, v_I := 0, u_J := 0, v_J := 0, w_I := 0, w' := 0).
example :
    presheafPRACatBifunctor.{1, 0, 0, 0, 0, 0} ⟶
      praPositionsNatTarget.{1, 0, 0, 0, 0, 0} :=
  praPositionsNat.{1, 0, 0, 0, 0, 0}

end UniversePoly
