import GebLean.Polynomial
import GebLean.PresheafPRA
import Mathlib.CategoryTheory.Discrete.Basic

/-!
# Over X as a Presheaf Category on Discrete X

The slice category `Over X` for a type `X` is equivalent to
the presheaf category `(Discrete X)ᵒᵖ ⥤ Type u`.  The
equivalence composes three steps:

1. `familySliceEquiv.symm : Over X ≌ (X → Type u)`
2. `piEquivalenceFunctorDiscrete X (Type u) :
     (X → Type u) ≌ (Discrete X ⥤ Type u)`
3. `(Discrete.opposite X).symm.congrLeft :
     (Discrete X ⥤ Type u) ≌ ((Discrete X)ᵒᵖ ⥤ Type u)`
-/

namespace GebLean

open CategoryTheory

universe u

/--
The equivalence between `Over X` and the presheaf
category `(Discrete X)ᵒᵖ ⥤ Type u`.

Composes `familySliceEquiv.symm`, which identifies
`Over X` with `X`-indexed families of types, with
`piEquivalenceFunctorDiscrete`, which identifies
families with functors out of `Discrete X`, and finally
precomposition by `(Discrete.opposite X).symm` to pass
from `Discrete X` to `(Discrete X)ᵒᵖ`.
-/
def overDiscretePresheafEquiv (X : Type u) :
    Over X ≌ ((Discrete X)ᵒᵖ ⥤ Type u) :=
  (familySliceEquiv X).symm |>.trans
    (piEquivalenceFunctorDiscrete X (Type u))
    |>.trans
    ((Discrete.opposite X).symm.congrLeft)

end GebLean
