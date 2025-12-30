import GebLean.CatJudgmentAdjunction

/-!
# Cat-Valued Functors and Copresheaf Transformations

This file establishes that natural transformations between Cat-valued functors
correspond bijectively to natural transformations between their images under
the copresheaf embedding.

Given the reflective embedding `Phi : BundledOverCategoryData → [J, Type]`
(where J = CategoryJudgments), and functors `F, G : C ⥤ BundledOverCategoryData`,
we prove:

  `(F ⋙ Phi ⟶ G ⋙ Phi) ≃ (F ⟶ G)`

This follows from the full faithfulness of Phi, which implies that
post-composition with Phi induces equivalences on hom-sets, and this
extends to natural transformation spaces.

## Main Results

- `natTransOfWhiskeredPhi`: Given a natural transformation between
  `F ⋙ Phi` and `G ⋙ Phi`, construct the corresponding natural
  transformation between `F` and `G`.

- `natTransEquiv`: The equivalence between natural transformations
  `F ⋙ Phi ⟶ G ⋙ Phi` and natural transformations `F ⟶ G`.
-/

namespace GebLean

open CategoryTheory

universe v u

variable {C : Type u} [Category.{v} C]

section NatTransEquiv

variable (F G : C ⥤ BundledOverCategoryData.{u, u})

/--
Whisker a natural transformation `α : F ⟶ G` with `PhiFunctor` on the right.
This constructs a natural transformation `F ⋙ PhiFunctor ⟶ G ⋙ PhiFunctor`
whose components are `PhiFunctor.map (α.app c)`.
-/
@[simps]
def whiskerRightPhi (α : F ⟶ G) : F ⋙ PhiFunctor ⟶ G ⋙ PhiFunctor where
  app c := PhiFunctor.map (α.app c)
  naturality {c c'} f := by
    simp only [Functor.comp_obj, Functor.comp_map]
    rw [← PhiFunctor.map_comp, ← PhiFunctor.map_comp]
    congr 1
    exact α.naturality f

/--
Given a natural transformation `η : F ⋙ PhiFunctor ⟶ G ⋙ PhiFunctor`,
construct the corresponding natural transformation `F ⟶ G` by applying
the preimage at each component.
-/
@[simps]
def natTransOfWhiskeredPhi
    (η : F ⋙ PhiFunctor ⟶ G ⋙ PhiFunctor) : F ⟶ G where
  app c := phiPreimage (η.app c)
  naturality {c c'} f := by
    apply phiFunctorFullyFaithful.map_injective
    simp only [Functor.map_comp, phi_map_preimage]
    have h1 := η.naturality f
    simp only [Functor.comp_map] at h1
    exact h1

/--
Whiskering a natural transformation with PhiFunctor on the right preserves
the original transformation when we apply the preimage construction.
-/
theorem natTransOfWhiskeredPhi_whiskerRightPhi (α : F ⟶ G) :
    natTransOfWhiskeredPhi F G (whiskerRightPhi F G α) = α := by
  ext c
  simp only [natTransOfWhiskeredPhi_app, whiskerRightPhi_app, phi_preimage_map]

/--
The preimage construction followed by whiskering with PhiFunctor gives back
the original natural transformation.
-/
theorem whiskerRightPhi_natTransOfWhiskeredPhi
    (η : F ⋙ PhiFunctor ⟶ G ⋙ PhiFunctor) :
    whiskerRightPhi F G (natTransOfWhiskeredPhi F G η) = η := by
  ext c
  simp only [whiskerRightPhi_app, natTransOfWhiskeredPhi_app, phi_map_preimage]

/--
The equivalence between natural transformations `F ⋙ Phi ⟶ G ⋙ Phi` and
natural transformations `F ⟶ G`, where `Phi = PhiFunctor` is the fully
faithful embedding of categories into copresheaves on CategoryJudgments.

This shows that post-composing Cat-valued functors with the copresheaf
embedding preserves and reflects natural transformations: the embedding
does not introduce any "extra" transformations nor collapse any.
-/
def natTransEquiv :
    (F ⋙ PhiFunctor ⟶ G ⋙ PhiFunctor) ≃ (F ⟶ G) where
  toFun := natTransOfWhiskeredPhi F G
  invFun := whiskerRightPhi F G
  left_inv := whiskerRightPhi_natTransOfWhiskeredPhi F G
  right_inv := natTransOfWhiskeredPhi_whiskerRightPhi F G

/--
The forward direction of `natTransEquiv` applied to a whiskered transformation.
-/
@[simp]
theorem natTransEquiv_apply (α : F ⟶ G) :
    natTransEquiv F G (whiskerRightPhi F G α) = α :=
  natTransOfWhiskeredPhi_whiskerRightPhi F G α

/--
The inverse direction of `natTransEquiv`.
-/
@[simp]
theorem natTransEquiv_symm_apply (α : F ⟶ G) :
    (natTransEquiv F G).symm α = whiskerRightPhi F G α := rfl

end NatTransEquiv

end GebLean
