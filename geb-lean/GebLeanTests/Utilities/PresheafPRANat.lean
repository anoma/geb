import GebLean.PresheafPRA

/-!
# Tests for (I, J)-Naturality of praPositionsFunctor

Type-signature sanity checks and small-example tests for
`praPositionsNat` and friends in `GebLean.PresheafPRA`.
-/

open GebLean CategoryTheory

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
