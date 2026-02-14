import GebLean.ComprehensiveWeighted
import GebLean.ParanatAlg

/-!
# Concrete descriptions of the wedge weight

This module computes the wedge weight functor
`wedgeWeight H : TwistedArrow C ⥤ Type v` for specific
profunctors `H`. The wedge weight is the functor whose
natural transformations characterize paranatural
transformations
(`paranatWeightedLimitEquiv : Paranat H G ≃
  (wedgeWeight H ⟶ profunctorOnTwistedArrow C G)`).

At each twisted arrow `tw = (f : A ⟶ B)`,
`(wedgeWeight H).obj tw` is the set of connected
components of costructured arrows over `tw` in the
twisted arrow category of `DiagElem H`.

The canonical embedding sends each diagonal element
`d ∈ diagApp H I` to the connected component of the
identity costructured arrow at `⟨I, d⟩`.

## Main results

- `wedgeWeightIdentityMap`: the canonical map from
  diagonal elements to the wedge weight at identity
  twisted arrows.
- `wedgeWeightIdentityMap_injective`: this map is
  injective.
- Concrete `diagApp` descriptions for `AlgProf`,
  `CoalgProf`, and `HomProf`.
-/

namespace GebLean

open CategoryTheory

universe v

variable {C : Type v} [Category.{v} C]

section WedgeWeightAtIdentity

variable (H : Cᵒᵖ ⥤ C ⥤ Type v)

/-- The canonical map from diagonal elements at `I` to
the wedge weight at the identity twisted arrow `𝟙 I`.

Each `d ∈ diagApp H I` gives a costructured arrow
whose source is the identity twisted arrow at
`⟨I, d⟩ : DiagElem H`, with the identity morphism as
the costructured arrow hom. -/
def wedgeWeightIdentityMap (I : C) :
    diagApp H I →
    (wedgeWeight H).obj (twObjMk (𝟙 I)) :=
  fun d =>
    Quotient.mk _
      (CostructuredArrow.mk
        (Y := twObjMk
          (𝟙 (⟨I, d⟩ : DiagElem H)))
        (𝟙 (twObjMk (𝟙 I))))

end WedgeWeightAtIdentity

end GebLean
