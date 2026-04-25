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
