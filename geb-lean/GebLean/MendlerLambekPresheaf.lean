import GebLean.MendlerLambekEndPower
import Mathlib.CategoryTheory.Monoidal.Closed.FunctorToTypes
import Mathlib.CategoryTheory.Monoidal.FunctorCategory

/-!
# Mendler-Lambek Equivalence for Presheaf Categories

Instantiates the Mendler-Lambek end-power framework
for presheaf categories `E ⥤ Type w`, where the
monoidal closed structure, copowers, and powers
all exist.

## Unconditional equivalence

`MendlerAlgebra G ≌ PowerEndMendlerAlgebra G`
holds for any profunctor `G` on a presheaf
category, with no hypotheses beyond the
monoidal closed structure, copowers, and powers
(all of which are automatic).

## Conditional equivalence

The full equivalence
`PowerEndMendlerAlgebra G ≌
  ConventionalAlgebra (GExtFunctor G)`
requires `HasAllHomToProfCoends G` (existence of
restricted coends).
-/

namespace GebLean

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Monoidal
open MonoidalClosed

universe u₁ v₁ w₁

variable {E : Type u₁} [Category.{v₁} E]

section PresheafMendlerAlgPowerEnd

variable
  (G : (E ⥤ Type (max w₁ v₁ u₁))ᵒᵖ ⥤
    (E ⥤ Type (max w₁ v₁ u₁)) ⥤
      (E ⥤ Type (max w₁ v₁ u₁)))

/-- The equivalence between Mendler algebras and
power-end Mendler algebras for presheaf categories.
No hypotheses beyond the monoidal closed structure,
copowers, and powers (all automatic for presheaf
categories). -/
def presheafMendlerAlgPowerEndEquiv :
    MendlerAlgebra G ≌ PowerEndMendlerAlgebra G :=
  mendlerAlgPowerEndEquiv G

end PresheafMendlerAlgPowerEnd

section PresheafMendlerLambek

variable
  (G : (E ⥤ Type (max w₁ v₁ u₁))ᵒᵖ ⥤
    (E ⥤ Type (max w₁ v₁ u₁)) ⥤
      (E ⥤ Type (max w₁ v₁ u₁)))
  [HasAllHomToProfCoends G]

/-- The power-end Mendler-Lambek equivalence for
presheaf categories: power-end Mendler algebras
are equivalent to conventional algebras of the
GExt functor.

Requires `HasAllHomToProfCoends G` (existence of
restricted coends for `G` with `HomToProf`
weight). -/
def presheafMendlerLambekEndPowerEquiv :
    PowerEndMendlerAlgebra G ≌
      ConventionalAlgebra
        (HasAllHomToProfCoends.GExtFunctor G) :=
  mendlerLambekEndPowerEquiv G

end PresheafMendlerLambek

end GebLean
