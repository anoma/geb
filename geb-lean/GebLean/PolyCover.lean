import GebLean.Polynomial
import GebLean.Utilities.Presheaf
import Mathlib.CategoryTheory.Preadditive.Projective.Basic
import Mathlib.CategoryTheory.Limits.Presheaf

/-!
# Regular Projective Cover by Coproducts of Representables

Individual representables are projective in any
(co)presheaf category: for `C : Type u` with
`Category.{v} C` and auxiliary universe `w`,
`uliftYoneda.{w}.obj X` is projective in
`Cᵒᵖ ⥤ Type (max w v)` and `uliftCoyoneda.{w}.obj X`
is projective in `C ⥤ Type (max w v)`, with no
dependence on `u`.

For `EnoughProjectives`, the projective cover of a
presheaf `P : Cᵒᵖ ⥤ Type (max w v)` is a coproduct
indexed by `P.Elements : Type (max u w v)`, which
includes a sum over `Ob(C) : Type u`.  The cover
therefore lands in `Cᵒᵖ ⥤ Type (max u w v)`, and its
canonical map targets `P` lifted into the larger
universe.  Since any presheaf in `Type (max u w v)` is
isomorphic to a lifted presheaf from `Type (max u w v)`
(via `Equiv.ulift`), we obtain
`EnoughProjectives (Cᵒᵖ ⥤ Type (max u w v))`.

For presheaves, the projective objects are coproducts of
contravariant representables `uliftYoneda.obj c`,
corresponding to objects of `FreeCoprodCompletionCat C`.
For copresheaves, the projective objects are coproducts
of covariant representables, corresponding to objects of
`CoprodCovarRepCat C`.
-/

namespace GebLean

open CategoryTheory Limits

universe w v u

variable {C : Type u} [Category.{v} C]

open Presheaf in
instance uliftYoneda_projective (X : C) :
    Projective
      (uliftYoneda.{w}.obj X :
        Cᵒᵖ ⥤ Type (max w v)) where
  factors {E F} f e := by
    intro
    have hep : Function.Surjective
        (e.app (Opposite.op X)) :=
      surjective_of_epi _
    obtain ⟨x, hx⟩ := hep (uliftYonedaEquiv f)
    exact ⟨uliftYonedaEquiv.symm x,
      uliftYonedaEquiv.injective (by
        rw [uliftYonedaEquiv_comp,
          Equiv.apply_symm_apply, hx])⟩

section PresheafCover

open Presheaf Opposite

variable (P : Cᵒᵖ ⥤ Type (max w v))

/--
The coproduct-of-representables presheaf covering `P`.
The input `P` lands in `Type (max w v)`; the cover
lands in `Type (max u w v)`, absorbing `u` from the
sum over objects of `C`.
-/
@[simp]
def presheafCover :
    Cᵒᵖ ⥤ Type (max u w v) where
  obj Y :=
    Σ (j : P.Elementsᵒᵖ),
      (uliftYoneda.{max u w}.obj
        j.unop.1.unop).obj Y
  map {Y Z} f := fun ⟨j, g⟩ ↦
    ⟨j,
      (uliftYoneda.{max u w}.obj
        j.unop.1.unop).map f g⟩
  map_id Y := by
    funext ⟨j, ⟨g⟩⟩
    simp [uliftYoneda]
  map_comp f g := by
    funext ⟨j, ⟨h⟩⟩
    simp [uliftYoneda]

/--
The canonical map from `presheafCover P` to `P` lifted
into the larger universe.  Sends `(j, f)` — where
`j = (c, x)` is an element of `P` and
`f : Y.unop ⟶ c.unop` — to `ULift.up (P.map f.op x)`.
-/
def presheafCoverMap :
    presheafCover.{w, v, u} P ⟶
      P ⋙ uliftFunctor.{u, max w v} where
  app Y := fun ⟨j, ⟨f⟩⟩ ↦
    ULift.up (P.map f.op j.unop.2)
  naturality {Y Z} g := by
    ext ⟨j, ⟨f⟩⟩
    simp [presheafCover, uliftFunctor]

instance presheafCoverMap_epi :
    Epi (presheafCoverMap.{w, v, u} P) := by
  rw [NatTrans.epi_iff_epi_app]
  intro Y
  rw [epi_iff_surjective]
  intro ⟨y⟩
  exact ⟨⟨op (Functor.elementsMk P Y y),
    ⟨𝟙 Y.unop⟩⟩,
    by simp [presheafCoverMap]⟩

def presheafCoverIncl (j : P.Elementsᵒᵖ) :
    uliftYoneda.{max u w}.obj j.unop.1.unop ⟶
      presheafCover.{w, v, u} P where
  app _ g := ⟨j, g⟩
  naturality _ _ _ := rfl

private lemma presheafCover_factors_aux
    {E F : Cᵒᵖ ⥤ Type (max u w v)}
    (f : presheafCover.{w, v, u} P ⟶ F)
    (e : E ⟶ F) [Epi e]
    (j : P.Elementsᵒᵖ) :
    ∃ g : uliftYoneda.{max u w}.obj
        j.unop.1.unop ⟶ E,
      g ≫ e = presheafCoverIncl P j ≫ f :=
  Projective.factors
    (presheafCoverIncl P j ≫ f) e

instance presheafCover_projective :
    Projective (presheafCover.{w, v, u} P) where
  factors {E F} f e := by
    intro
    have h := fun j ↦
      presheafCover_factors_aux P f e j
    choose g hg using h
    refine ⟨⟨fun Y ⟨j, x⟩ ↦
      (g j).app Y x,
        fun {Y Z} fYZ ↦ ?_⟩, ?_⟩
    · ext ⟨j, x⟩
      exact congr_fun
        ((g j).naturality fYZ) x
    · ext Y ⟨j, x⟩
      exact congr_fun
        (NatTrans.congr_app (hg j) Y) x

def presheafProjectivePresentation :
    ProjectivePresentation
      (P ⋙ uliftFunctor.{u, max w v} :
        Cᵒᵖ ⥤ Type (max u w v)) where
  p := presheafCover.{w, v, u} P
  f := presheafCoverMap P

end PresheafCover

private def uliftPresheafIso
    (Q : Cᵒᵖ ⥤ Type (max u w v)) :
    Q ⋙ uliftFunctor.{u, max u w v} ≅ Q :=
  NatIso.ofComponents
    (fun Y ↦ {
      hom := ULift.down
      inv := ULift.up
    })

instance presheaf_enoughProjectives :
    EnoughProjectives
      (Cᵒᵖ ⥤ Type (max u w v)) where
  presentation Q := by
    have pp := presheafProjectivePresentation.{
      max u w, v, u} Q
    exact ⟨{
      p := pp.p
      f := pp.f ≫ (uliftPresheafIso Q).hom
    }⟩

instance uliftCoyoneda_projective (X : Cᵒᵖ) :
    Projective
      (uliftCoyoneda.{w}.obj X :
        C ⥤ Type (max w v)) where
  factors {E F} f e := by
    intro
    have hep : Function.Surjective
        (e.app X.unop) :=
      surjective_of_epi _
    obtain ⟨x, hx⟩ :=
      hep (uliftCoyonedaEquiv f)
    exact ⟨uliftCoyonedaEquiv.symm x,
      uliftCoyonedaEquiv.injective (by
        rw [uliftCoyonedaEquiv_comp,
          Equiv.apply_symm_apply, hx])⟩

section CopresheafCover

open Opposite

variable (F : C ⥤ Type (max w v))

def copresheafCover :
    C ⥤ Type (max u w v) where
  obj Y :=
    Σ (j : F.Elementsᵒᵖ),
      (uliftCoyoneda.{max u w}.obj
        (op j.unop.1)).obj Y
  map {Y Z} f := fun ⟨j, g⟩ ↦
    ⟨j,
      (uliftCoyoneda.{max u w}.obj
        (op j.unop.1)).map f g⟩
  map_id Y := by
    funext ⟨j, ⟨g⟩⟩
    simp [uliftCoyoneda, uliftYoneda]
  map_comp f g := by
    funext ⟨j, ⟨h⟩⟩
    simp [uliftCoyoneda, uliftYoneda]

def copresheafCoverMap :
    copresheafCover.{w, v, u} F ⟶
      F ⋙ uliftFunctor.{u, max w v} where
  app Y := fun ⟨j, ⟨f⟩⟩ ↦
    ULift.up (F.map f j.unop.2)
  naturality {Y Z} g := by
    ext ⟨j, ⟨f⟩⟩
    simp [copresheafCover, uliftFunctor]

instance copresheafCoverMap_epi :
    Epi (copresheafCoverMap.{w, v, u} F) := by
  rw [NatTrans.epi_iff_epi_app]
  intro Y
  rw [epi_iff_surjective]
  intro ⟨y⟩
  exact ⟨⟨op (Functor.elementsMk F Y y),
    ⟨𝟙 Y⟩⟩,
    by simp [copresheafCoverMap]⟩

def copresheafCoverIncl (j : F.Elementsᵒᵖ) :
    uliftCoyoneda.{max u w}.obj
      (op j.unop.1) ⟶
      copresheafCover.{w, v, u} F where
  app _ g := ⟨j, g⟩
  naturality _ _ _ := rfl

private lemma copresheafCover_factors_aux
    {E G : C ⥤ Type (max u w v)}
    (f : copresheafCover.{w, v, u} F ⟶ G)
    (e : E ⟶ G) [Epi e]
    (j : F.Elementsᵒᵖ) :
    ∃ g : uliftCoyoneda.{max u w}.obj
        (op j.unop.1) ⟶ E,
      g ≫ e = copresheafCoverIncl F j ≫ f :=
  Projective.factors
    (copresheafCoverIncl F j ≫ f) e

instance copresheafCover_projective :
    Projective
      (copresheafCover.{w, v, u} F) where
  factors {E G} f e := by
    intro
    have h := fun j ↦
      copresheafCover_factors_aux F f e j
    choose g hg using h
    refine ⟨⟨fun Y ⟨j, x⟩ ↦
      (g j).app Y x,
        fun {Y Z} fYZ ↦ ?_⟩, ?_⟩
    · ext ⟨j, x⟩
      exact congr_fun
        ((g j).naturality fYZ) x
    · ext Y ⟨j, x⟩
      exact congr_fun
        (NatTrans.congr_app (hg j) Y) x

def copresheafProjectivePresentation :
    ProjectivePresentation
      (F ⋙ uliftFunctor.{u, max w v} :
        C ⥤ Type (max u w v)) where
  p := copresheafCover.{w, v, u} F
  f := copresheafCoverMap F

end CopresheafCover

private def uliftCopresheafIso
    (Q : C ⥤ Type (max u w v)) :
    Q ⋙ uliftFunctor.{u, max u w v} ≅ Q :=
  NatIso.ofComponents
    (fun Y ↦ {
      hom := ULift.down
      inv := ULift.up
    })

instance copresheaf_enoughProjectives :
    EnoughProjectives
      (C ⥤ Type (max u w v)) where
  presentation Q := by
    have pp := copresheafProjectivePresentation.{
      max u w, v, u} Q
    exact ⟨{
      p := pp.p
      f := pp.f ≫
        (uliftCopresheafIso Q).hom
    }⟩

end GebLean
