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

/-! ## Slice Category Adjunction Lifting

The reflective embedding `PhiFunctor : Cat → [J, Type]` lifts to slice categories:
for any category X (as `BundledOverCategoryData`), we get a reflective embedding

  `Cat/X ⟵reflective⟶ [J, Type]/Phi(X)`

This uses mathlib's `Over.postAdjunctionRight` to lift the adjunction, and
`Functor.FullyFaithful.over` to lift full faithfulness. -/

section SliceAdjunction

variable (X : BundledOverCategoryData.{u, u})

/-- Post-composition with PhiFunctor on slice categories.
    This sends an object `(A, f : A ⟶ X)` in `Cat/X` to
    `(Phi(A), Phi.map f : Phi(A) ⟶ Phi(X))` in `[J, Type]/Phi(X)`. -/
abbrev phiSlice : Over X ⥤ Over (PhiFunctor.obj X) :=
  Over.post PhiFunctor

/-- Post-composition with LFunctor on slice categories.
    Combined with mapping by the counit, this is the left adjoint to phiSlice. -/
abbrev lSliceBase : Over (PhiFunctor.obj X) ⥤ Over (LFunctor.obj (PhiFunctor.obj X)) :=
  Over.post LFunctor

/-- The left adjoint to phiSlice, combining post-composition with L and
    mapping by the counit isomorphism. -/
abbrev lSlice : Over (PhiFunctor.obj X) ⥤ Over X :=
  lSliceBase X ⋙ Over.map (catCopresheafMathlibAdjunction.counit.app X)

/-- The slice adjunction: `lSlice X ⊣ phiSlice X`.
    This lifts the base adjunction `LFunctor ⊣ PhiFunctor` to slice categories
    over X and Phi(X). -/
def sliceAdjunction : lSlice X ⊣ phiSlice X :=
  Over.postAdjunctionRight catCopresheafMathlibAdjunction

/-- phiSlice is a right adjoint. -/
instance phiSlice_isRightAdjoint : (phiSlice X).IsRightAdjoint where
  exists_leftAdjoint := ⟨lSlice X, ⟨sliceAdjunction X⟩⟩

/-- lSlice is a left adjoint. -/
instance lSlice_isLeftAdjoint : (lSlice X).IsLeftAdjoint where
  exists_rightAdjoint := ⟨phiSlice X, ⟨sliceAdjunction X⟩⟩

/-- Post-composition with PhiFunctor is fully faithful on slice categories.
    This follows from PhiFunctor being fully faithful. -/
def phiSliceFullyFaithful : (phiSlice X).FullyFaithful :=
  phiFunctorFullyFaithful.over X

/-- phiSlice is full. -/
instance phiSlice_full : (phiSlice X).Full :=
  (phiSliceFullyFaithful X).full

/-- phiSlice is faithful. -/
instance phiSlice_faithful : (phiSlice X).Faithful :=
  (phiSliceFullyFaithful X).faithful

end SliceAdjunction

/-! ## Reflectivity of the Slice Embedding

The slice adjunction is reflective: the counit is an isomorphism.
This follows because the base counit `L ⋙ Phi ≅ Id` is an isomorphism. -/

section SliceReflectivity

variable (X : BundledOverCategoryData.{u, u})

/-- The counit of the slice adjunction at an object of Over X is an isomorphism.

    For an object `(A, f : A ⟶ X)` in `Over X`, the counit component is:
    `(L(Phi(A)), L(Phi(f)) ≫ counit_X) ⟶ (A, f)`

    The left component is `counit_A : L(Phi(A)) ⟶ A`, which is an isomorphism
    by reflectivity of the base adjunction. -/
instance sliceAdjunction_counit_app_isIso (Y : Over X) :
    IsIso ((sliceAdjunction X).counit.app Y) := by
  -- The counit left component is the base counit, which is an iso
  have h : IsIso ((sliceAdjunction X).counit.app Y).left := inferInstance
  -- Use Over.isoMk to construct the iso, then extract IsIso from the fact that
  -- the morphism equals the hom of an iso
  let i : Over _ := (lSlice X).obj ((phiSlice X).obj Y)
  let j : Over X := Y
  let iso : i ≅ j := Over.isoMk (asIso ((sliceAdjunction X).counit.app Y).left)
  have heq : iso.hom = (sliceAdjunction X).counit.app Y := by
    apply Over.OverMorphism.ext
    rfl
  rw [← heq]
  exact iso.isIso_hom

/-- The counit of the slice adjunction is a natural isomorphism. -/
instance sliceAdjunction_counit_isIso : IsIso (sliceAdjunction X).counit :=
  NatIso.isIso_of_isIso_app _

/-- The slice embedding `phiSlice X : Cat/X ⥤ [J, Type]/Phi(X)` is reflective.
    This establishes that `Cat/X` is a reflective subcategory of `[J, Type]/Phi(X)`. -/
instance phiSlice_reflective : Reflective (phiSlice X) where
  L := lSlice X
  adj := sliceAdjunction X

end SliceReflectivity

/-! ## Slice Morphism Equivalence

The equivalence on hom-sets induced by full faithfulness of phiSlice. -/

section SliceHomEquiv

variable {X : BundledOverCategoryData.{u, u}}
variable (A B : Over X)

/-- The equivalence between morphisms in the slice over Phi(X) and morphisms
    in the slice over X, induced by full faithfulness of phiSlice. -/
def sliceHomEquiv : ((phiSlice X).obj A ⟶ (phiSlice X).obj B) ≃ (A ⟶ B) :=
  (phiSliceFullyFaithful X).homEquiv.symm

/-- Applying phiSlice to the preimage gives the original morphism. -/
@[simp]
theorem sliceHomEquiv_map (f : A ⟶ B) :
    sliceHomEquiv A B ((phiSlice X).map f) = f :=
  (phiSliceFullyFaithful X).preimage_map f

/-- The image under phiSlice of the preimage is the original morphism. -/
@[simp]
theorem map_sliceHomEquiv (g : (phiSlice X).obj A ⟶ (phiSlice X).obj B) :
    (phiSlice X).map (sliceHomEquiv A B g) = g :=
  (phiSliceFullyFaithful X).map_preimage g

end SliceHomEquiv

/-! ## Slice-Valued Functor Categories

For a fixed category X (as `BundledOverCategoryData`), we lift the reflective embedding
of slice categories to functor categories:

  `[C, Cat/X] ⟵reflective⟶ [C, [J, Type]/Phi(X)]`

This is constructed by whiskering with `phiSlice X`, analogously to how we lifted
the base adjunction to functor categories. -/

section SliceValuedFunctorCategories

variable (C : Type u) [Category.{v} C]
variable (X : BundledOverCategoryData.{u, u})

/-- The whiskering functor `(phiSlice X ∘ −) : [C, Cat/X] ⥤ [C, [J, Type]/Phi(X)]`.
    This sends a functor `F : C ⥤ Over X` to `F ⋙ phiSlice X`. -/
abbrev phiSliceWhiskering :
    (C ⥤ Over X) ⥤ (C ⥤ Over (PhiFunctor.obj X)) :=
  (Functor.whiskeringRight C (Over X) _).obj (phiSlice X)

/-- The whiskering functor `(lSlice X ∘ −) : [C, [J, Type]/Phi(X)] ⥤ [C, Cat/X]`.
    This is the left adjoint to `phiSliceWhiskering`. -/
abbrev lSliceWhiskering :
    (C ⥤ Over (PhiFunctor.obj X)) ⥤ (C ⥤ Over X) :=
  (Functor.whiskeringRight C _ (Over X)).obj (lSlice X)

/-- Post-composition with `phiSlice X` is fully faithful on functor categories.
    This follows from `phiSlice X` being fully faithful. -/
def phiSliceWhiskeringFullyFaithful :
    (phiSliceWhiskering C X).FullyFaithful :=
  (phiSliceFullyFaithful X).whiskeringRight C

/-- The whiskering functor with phiSlice is full. -/
instance phiSliceWhiskering_full : (phiSliceWhiskering C X).Full :=
  (phiSliceWhiskeringFullyFaithful C X).full

/-- The whiskering functor with phiSlice is faithful. -/
instance phiSliceWhiskering_faithful : (phiSliceWhiskering C X).Faithful :=
  (phiSliceWhiskeringFullyFaithful C X).faithful

/-- The lifted adjunction `(lSlice X ∘ −) ⊣ (phiSlice X ∘ −)` on functor categories
    valued in slices. -/
def sliceValuedAdjunction :
    lSliceWhiskering C X ⊣ phiSliceWhiskering C X :=
  Adjunction.whiskerRight C (sliceAdjunction X)

/-- phiSliceWhiskering is a right adjoint. -/
instance phiSliceWhiskering_isRightAdjoint : (phiSliceWhiskering C X).IsRightAdjoint where
  exists_leftAdjoint := ⟨lSliceWhiskering C X, ⟨sliceValuedAdjunction C X⟩⟩

/-- lSliceWhiskering is a left adjoint. -/
instance lSliceWhiskering_isLeftAdjoint : (lSliceWhiskering C X).IsLeftAdjoint where
  exists_rightAdjoint := ⟨phiSliceWhiskering C X, ⟨sliceValuedAdjunction C X⟩⟩

/-- The counit of the slice-valued functor adjunction at a functor F has iso components. -/
instance sliceValuedAdjunction_counit_app_isIso
    (F : C ⥤ Over X) :
    IsIso ((sliceValuedAdjunction C X).counit.app F) := by
  apply NatIso.isIso_of_isIso_app

/-- The counit of the slice-valued functor adjunction is a natural isomorphism. -/
instance sliceValuedAdjunction_counit_isIso :
    IsIso (sliceValuedAdjunction C X).counit :=
  NatIso.isIso_of_isIso_app _

/-- The whiskering functor `(phiSlice X ∘ −)` is reflective.
    This establishes that `[C, Cat/X]` is a reflective subcategory of
    `[C, [J, Type]/Phi(X)]`. -/
instance phiSliceWhiskering_reflective : Reflective (phiSliceWhiskering C X) where
  L := lSliceWhiskering C X
  adj := sliceValuedAdjunction C X

end SliceValuedFunctorCategories

/-! ## Natural Transformation Equivalence for Slice-Valued Functors

The equivalence on natural transformations induced by full faithfulness of
the slice-valued whiskering functor. -/

section SliceNatTransEquiv

variable {C : Type u} [Category.{v} C]
variable {X : BundledOverCategoryData.{u, u}}
variable (F G : C ⥤ Over X)

/-- The equivalence between natural transformations in the slice-valued image
    and natural transformations in the original functor category. -/
def sliceNatTransEquiv :
    (F ⋙ phiSlice X ⟶ G ⋙ phiSlice X) ≃ (F ⟶ G) :=
  (phiSliceWhiskeringFullyFaithful C X).homEquiv.symm

/-- Applying phiSlice to the preimage gives the original transformation. -/
@[simp]
theorem sliceNatTransEquiv_whiskerRight (α : F ⟶ G) :
    sliceNatTransEquiv F G (Functor.whiskerRight α (phiSlice X)) = α :=
  (phiSliceWhiskeringFullyFaithful C X).preimage_map α

/-- The image under phiSlice of the preimage is the original transformation. -/
@[simp]
theorem whiskerRight_sliceNatTransEquiv (η : F ⋙ phiSlice X ⟶ G ⋙ phiSlice X) :
    Functor.whiskerRight (sliceNatTransEquiv F G η) (phiSlice X) = η :=
  (phiSliceWhiskeringFullyFaithful C X).map_preimage η

end SliceNatTransEquiv

end GebLean
