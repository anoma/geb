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

/-- Extraction function mapping a costructured arrow
over the identity twisted arrow at `I` to a diagonal
element at `I`.

Given a costructured arrow `σ` whose source twisted
arrow has domain element `(A, a) : DiagElem H` and
hom components `domArr : I ⟶ A` and `codArr : B ⟶ I`,
the extraction applies the covariant action by
`h ≫ codArr` (where `h` is the base of the source
twisted arrow) and then the contravariant action by
`domArr`. -/
def wedgeWeightExtract (I : C)
    (σ : CostructuredArrow
      (twistedArrowMap (DiagElem.forget H))
      (twObjMk (𝟙 I))) :
    diagApp H I :=
  (H.map (twDomArr σ.hom).op).app I
    ((H.obj (Opposite.op (twDom σ.left).base)).map
      ((twArr σ.left).base ≫ twCodArr σ.hom)
      (twDom σ.left).elem)

/-- The extraction function sends canonical arrows to
their diagonal elements. -/
theorem wedgeWeightExtract_canonical (I : C)
    (d : diagApp H I) :
    wedgeWeightExtract H I
      (CostructuredArrow.mk
        (Y := twObjMk
          (𝟙 (⟨I, d⟩ : DiagElem H)))
        (𝟙 (twObjMk (𝟙 I)))) = d := by
  change (H.map (𝟙 I).op).app I
    ((H.obj (Opposite.op I)).map
      (𝟙 I ≫ 𝟙 I) d) = d
  simp

/-- The extraction function is invariant under
morphisms in the costructured arrow category. -/
theorem wedgeWeightExtract_invariant (I : C)
    {σ₁ σ₂ : CostructuredArrow
      (twistedArrowMap (DiagElem.forget H))
      (twObjMk (𝟙 I))}
    (φ : σ₁ ⟶ σ₂) :
    wedgeWeightExtract H I σ₁ =
    wedgeWeightExtract H I σ₂ := by
  unfold wedgeWeightExtract
  have hdom := congrArg twDomArr (CostructuredArrow.w φ)
  -- hdom : twDomArr σ₂.hom ≫ (twDomArr φ.left).base
  --        = twDomArr σ₁.hom
  have hcod := congrArg twCodArr (CostructuredArrow.w φ)
  -- hcod : (twCodArr φ.left).base ≫ twCodArr σ₂.hom
  --        = twCodArr σ₁.hom
  rw [← hdom, ← hcod]
  simp only [twDomArr_comp, twCodArr_comp,
    twistedArrowMap_map_domArr,
    twistedArrowMap_map_codArr,
    DiagElem.forget_map]
  simp only [op_comp, H.map_comp, NatTrans.comp_app,
    types_comp_apply]
  apply congrArg
  have htw := congrArg DiagElem.Hom.base
    (twHomComm φ.left)
  have nat_eq := congr_fun
    ((H.map (twDomArr φ.left).base.op).naturality
      ((twArr σ₁.left).base ≫
        (twCodArr φ.left).base ≫
        twCodArr σ₂.hom))
    (twDom σ₁.left).elem
  simp only [types_comp_apply] at nat_eq
  dsimp at nat_eq
  rw [nat_eq, (twDomArr φ.left).compat.symm,
    ← FunctorToTypes.map_comp_apply]
  have comm :=
    congrArg (· ≫ twCodArr σ₂.hom) htw
  dsimp at comm
  simp only [Category.assoc] at comm
  simp only [comm]

/-- The extraction function lifted to connected
components. Since the extraction is invariant under
costructured arrow morphisms
(`wedgeWeightExtract_invariant`), it descends to the
quotient defining the wedge weight. -/
def wedgeWeightExtractLifted (I : C) :
    (wedgeWeight H).obj (twObjMk (𝟙 I)) →
    diagApp H I :=
  Quotient.lift (wedgeWeightExtract H I)
    (fun σ₁ σ₂ h => by
      induction h with
      | refl => rfl
      | tail _ step ih =>
        exact ih.trans (step.elim
          (fun ⟨φ⟩ =>
            wedgeWeightExtract_invariant H I φ)
          (fun ⟨φ⟩ =>
            (wedgeWeightExtract_invariant
              H I φ).symm)))

/-- The canonical map from diagonal elements to the
wedge weight at identity twisted arrows is injective.

The proof constructs a left inverse via the extraction
function: `wedgeWeightExtractLifted` sends each
connected component to a diagonal element, and
`wedgeWeightExtract_canonical` shows this is a
retraction of `wedgeWeightIdentityMap`. -/
theorem wedgeWeightIdentityMap_injective (I : C) :
    Function.Injective
      (wedgeWeightIdentityMap H I) :=
  fun d₁ d₂ h =>
    (wedgeWeightExtract_canonical H I d₁).symm.trans
      ((congrArg
        (wedgeWeightExtractLifted H I) h).trans
        (wedgeWeightExtract_canonical H I d₂))

end WedgeWeightAtIdentity

section DiagAppDescriptions

variable (F : C ⥤ C)

/-- The diagonal of `AlgProf F` at `I` is the type of
F-algebra structures `F.obj I ⟶ I`. -/
@[simp]
theorem diagApp_algProf (I : C) :
    diagApp (AlgProf F) I = (F.obj I ⟶ I) := rfl

/-- The diagonal of `CoalgProf F` at `I` is the type
of F-coalgebra structures `I ⟶ F.obj I`. -/
@[simp]
theorem diagApp_coalgProf (I : C) :
    diagApp (CoalgProf F) I = (I ⟶ F.obj I) := rfl

end DiagAppDescriptions

end GebLean
