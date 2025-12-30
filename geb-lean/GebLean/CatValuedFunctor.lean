import GebLean.CatJudgmentAdjunction
import Mathlib.CategoryTheory.Adjunction.Whiskering

/-!
# Cat-Valued Functor Categories and Copresheaf Transformations

This file establishes that the reflective embedding
`PhiFunctor : BundledOverCategoryData → [J, Type]` (where J = CategoryJudgments)
lifts to a reflective embedding of functor categories:

  `[C, Cat] ⟵reflective⟶ [C, [J, Type]]`

for any category C.

This uses the general fact that post-composition with a fully faithful functor
is itself fully faithful (`Functor.FullyFaithful.whiskeringRight`), and that
adjunctions lift pointwise to functor categories (`Adjunction.whiskerRight`).

## Main Results

- `phiWhiskeringFullyFaithful`: Post-composition with `PhiFunctor` is fully
  faithful on functor categories.

- `catCopresheafFunctorAdjunction`: The lifted adjunction
  `(L ∘ −) ⊣ (Φ ∘ −) : [C, Cat] ⇄ [C, [J, Type]]`

- `phiWhiskering_reflective`: The whiskering functor `(Φ ∘ −)` is reflective.
-/

namespace GebLean

open CategoryTheory

universe v u

/-! ## Full Faithfulness of Whiskering with Phi

The general theorem `Functor.FullyFaithful.whiskeringRight` states that if
`F : D ⥤ E` is fully faithful, then the whiskering functor
`(F ∘ −) : [C, D] ⥤ [C, E]` is also fully faithful.

We apply this to `PhiFunctor` to get full faithfulness of post-composition. -/

section WhiskeringFullyFaithful

variable (C : Type u) [Category.{v} C]

/-- The whiskering functor `(Φ ∘ −) : [C, Cat] ⥤ [C, [J, Type]]`.
    This sends a functor `F : C ⥤ BundledOverCategoryData` to `F ⋙ PhiFunctor`. -/
abbrev phiWhiskering :
    (C ⥤ BundledOverCategoryData.{u, u}) ⥤
    (C ⥤ CategoryJudgments.FunctorData (Type u)) :=
  (Functor.whiskeringRight C BundledOverCategoryData _).obj PhiFunctor

/-- Post-composition with `PhiFunctor` is fully faithful on functor categories.
    This is an instance of the general theorem that whiskering with a fully
    faithful functor preserves full faithfulness. -/
def phiWhiskeringFullyFaithful :
    (phiWhiskering C).FullyFaithful :=
  phiFunctorFullyFaithful.whiskeringRight C

/-- The whiskering functor with Phi is full. -/
instance phiWhiskering_full : (phiWhiskering C).Full :=
  (phiWhiskeringFullyFaithful C).full

/-- The whiskering functor with Phi is faithful. -/
instance phiWhiskering_faithful : (phiWhiskering C).Faithful :=
  (phiWhiskeringFullyFaithful C).faithful

end WhiskeringFullyFaithful

/-! ## Lifted Adjunction for Functor Categories

The adjunction `LFunctor ⊣ PhiFunctor` lifts pointwise to functor categories:
`(L ∘ −) ⊣ (Φ ∘ −) : [C, [J, Type]] ⇄ [C, Cat]`

This uses mathlib's `Adjunction.whiskerRight`. -/

section LiftedAdjunction

variable (C : Type u) [Category.{v} C]

/-- The whiskering functor `(L ∘ −) : [C, [J, Type]] ⥤ [C, Cat]`.
    This is the left adjoint to `phiWhiskering`. -/
abbrev lWhiskering :
    (C ⥤ CategoryJudgments.FunctorData (Type u)) ⥤
    (C ⥤ BundledOverCategoryData.{u, u}) :=
  (Functor.whiskeringRight C _ BundledOverCategoryData).obj LFunctor

/-- The lifted adjunction `(L ∘ −) ⊣ (Φ ∘ −)` on functor categories.
    This is constructed by lifting the base adjunction pointwise. -/
def catCopresheafFunctorAdjunction :
    lWhiskering C ⊣ phiWhiskering C :=
  Adjunction.whiskerRight C catCopresheafMathlibAdjunction

/-- The whiskering functor with Phi is a right adjoint. -/
instance phiWhiskering_isRightAdjoint : (phiWhiskering C).IsRightAdjoint where
  exists_leftAdjoint := ⟨lWhiskering C, ⟨catCopresheafFunctorAdjunction C⟩⟩

/-- The whiskering functor with L is a left adjoint. -/
instance lWhiskering_isLeftAdjoint : (lWhiskering C).IsLeftAdjoint where
  exists_rightAdjoint := ⟨phiWhiskering C, ⟨catCopresheafFunctorAdjunction C⟩⟩

end LiftedAdjunction

/-! ## Reflectivity of the Lifted Embedding

Since the original adjunction is reflective (counit is an isomorphism),
the lifted adjunction is also reflective. This follows because:
1. The counit of `adj.whiskerRight C` has components `(adj.counit.app (F c))_c`
2. Each such component is an iso by the original reflectivity
3. Hence the lifted counit is also an iso -/

section LiftedReflectivity

variable (C : Type u) [Category.{v} C]

/-- The counit of the lifted adjunction at a functor F has iso components. -/
instance catCopresheafFunctorAdjunction_counit_app_isIso
    (F : C ⥤ BundledOverCategoryData.{u, u}) :
    IsIso ((catCopresheafFunctorAdjunction C).counit.app F) := by
  apply NatIso.isIso_of_isIso_app

/-- The counit of the lifted adjunction is a natural isomorphism. -/
instance catCopresheafFunctorAdjunction_counit_isIso :
    IsIso (catCopresheafFunctorAdjunction C).counit :=
  NatIso.isIso_of_isIso_app _

/-- The whiskering functor `(Φ ∘ −)` is reflective: it is a fully faithful
    right adjoint. This establishes that `[C, Cat]` is a reflective subcategory
    of `[C, [J, Type]]`. -/
instance phiWhiskering_reflective : Reflective (phiWhiskering C) where
  L := lWhiskering C
  adj := catCopresheafFunctorAdjunction C

end LiftedReflectivity

/-! ## Natural Transformation Equivalence

For explicit use, we provide the equivalence between natural transformations
`F ⟶ G` and `F ⋙ Phi ⟶ G ⋙ Phi` derived from the full faithfulness. -/

section NatTransEquiv

variable {C : Type u} [Category.{v} C]
variable (F G : C ⥤ BundledOverCategoryData.{u, u})

/-- The equivalence between natural transformations `F ⋙ Phi ⟶ G ⋙ Phi` and
    natural transformations `F ⟶ G`.

    This is an instance of the general fact that post-composition with a fully
    faithful functor induces bijections on hom-sets. -/
def natTransEquiv :
    (F ⋙ PhiFunctor ⟶ G ⋙ PhiFunctor) ≃ (F ⟶ G) :=
  (phiWhiskeringFullyFaithful C).homEquiv.symm

/-- The preimage of a whiskered natural transformation is the original. -/
@[simp]
theorem natTransEquiv_whiskerRight (α : F ⟶ G) :
    natTransEquiv F G (Functor.whiskerRight α PhiFunctor) = α :=
  (phiWhiskeringFullyFaithful C).preimage_map α

/-- The whiskered form of the preimage is the original transformation. -/
@[simp]
theorem whiskerRight_natTransEquiv (η : F ⋙ PhiFunctor ⟶ G ⋙ PhiFunctor) :
    Functor.whiskerRight (natTransEquiv F G η) PhiFunctor = η :=
  (phiWhiskeringFullyFaithful C).map_preimage η

end NatTransEquiv

end GebLean
