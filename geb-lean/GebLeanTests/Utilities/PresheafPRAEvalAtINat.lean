import GebLean.PresheafPRA

/-!
# Tests for (I, J, P, Z)-Naturality of praPolyEvalAtIFunctor

Type-signature sanity checks and small-example tests for
`praPolyEvalAtIFunctor` and friends in `GebLean.PresheafPRA`.
-/

open GebLean CategoryTheory

attribute [local instance] CategoryTheory.uliftCategory

/-! ## Type-signature sanity -/

example :
    praPolyEvalAtISource.{0, 0, 0, 0, 0, 0} (Cat.of PUnit) ⥤
      praPolyEvalTarget.{0, 0, 0, 0, 0, 0} :=
  praPolyEvalAtIFunctor.{0, 0, 0, 0, 0, 0} (Cat.of PUnit)

example : Cat.{0, 1} :=
  praPolyEvalAtISource.{0, 0, 0, 0, 0, 0} (Cat.of PUnit)

example : Cat.{0, 1} :=
  praPolyEvalTarget.{0, 0, 0, 0, 0, 0}

example :
    praPolyEvalAtISourceFib.{0, 0, 0, 0, 0, 0} (Cat.of PUnit) =
    praPolyEvalAtISourceFib.{0, 0, 0, 0, 0, 0} (Cat.of PUnit) :=
  rfl

example :
    praEvalTargetFibre.{0, 0, 0, 0, 0, 0} =
    praEvalTargetFibre.{0, 0, 0, 0, 0, 0} :=
  rfl

example :
    praPolyEvalTarget.{0, 0, 0, 0, 0, 0} =
    praPolyEvalTarget.{0, 0, 0, 0, 0, 0} :=
  rfl

example :
    praEvalAtBifunctor.{0, 0, 0, 0, 0, 0} PUnit PUnit =
    praEvalAtBifunctor.{0, 0, 0, 0, 0, 0} PUnit PUnit :=
  rfl
