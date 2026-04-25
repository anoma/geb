import GebLean.PresheafPRA

/-!
# Tests for (I, J, P)-Naturality of praPolyDirectionsFunctor

Type-signature sanity checks and small-example tests for
`praPolyDirectionsFunctor` and friends in `GebLean.PresheafPRA`.
-/

open GebLean CategoryTheory

attribute [local instance] CategoryTheory.uliftCategory

/-! ## Type-signature sanity -/

example :
    praPolyDirectionsSource.{0, 0, 0, 0, 0, 0} ⥤
      praPolyDirectionsTarget.{0, 0, 0, 0, 0, 0} :=
  praPolyDirectionsFunctor.{0, 0, 0, 0, 0, 0}

example : Cat.{0, 1} := praPolyDirectionsSource.{0, 0, 0, 0, 0, 0}
example : Cat.{0, 1} := praPolyDirectionsTarget.{0, 0, 0, 0, 0, 0}
example : Cat.{0, 0}ᵒᵖ ⥤ Cat.{0, 1} :=
  praDirectionsTargetFibre.{0, 0, 0, 0, 0, 0}

/-! ## Bridge-lemma collapse at a small concrete base -/

section CollapseTest

example (X : praPolyDirectionsSource.{0, 0, 0, 0, 0, 0}) :
    GrothendieckContraFunctor.objBase
      (praPolyDirectionsFunctor.{0, 0, 0, 0, 0, 0}.obj X) =
    (GrothendieckContraFunctor.objBase X.base).2 :=
  praPolyDirectionsFunctor_base.{0, 0, 0, 0, 0, 0} X

example (X : praPolyDirectionsSource.{0, 0, 0, 0, 0, 0}) :
    GrothendieckContraFunctor.objFiber
      (praPolyDirectionsFunctor.{0, 0, 0, 0, 0, 0}.obj X) =
    (praPolyDirectionsData.{0, 0, 0, 0, 0, 0}.fibFib X.base).obj
      X.fiber :=
  praPolyDirectionsFunctor_fibre.{0, 0, 0, 0, 0, 0} X

end CollapseTest
