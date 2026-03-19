import GebLean.Polynomial
import GebLean.Utilities.Elements
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

variable {C : Type u} [Category.{v, u} C]

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

variable (P : Cᵒᵖ ⥤ Type (max v w))

/--
The `FreeCoprodCompletionCat C` object whose evaluation
is the projective cover of `P`.  Indexed by the
contravariant elements of `P`, with family sending
each element to the underlying object of `C`.
-/
def presheafCoverObj :
    FreeCoprodCompletionCat.{u, v, max u w v} C :=
  fcObjMk (fun j : P.ElementsPre =>
    ((CategoryOfElements.π P).obj
      j.unop).unop)

/--
The projective cover of a presheaf `P`, defined as
the evaluation of `presheafCoverObj P`.
-/
def presheafCover :
    Cᵒᵖ ⥤ Type (max u w v) :=
  fcToFunctor (presheafCoverObj P)

/--
The canonical map from `presheafCover P` to `P`
lifted into the larger universe.
-/
def presheafCoverMap :
    presheafCover.{w, v, u} P ⟶
      P ⋙ uliftFunctor.{u, max w v} where
  app Y := fun ⟨j, f⟩ ↦
    ULift.up (P.map f.op j.unop.2)
  naturality {Y Z} g := by
    ext ⟨j, f⟩
    simp [presheafCover, fcToFunctor,
      fcEvalMap, uliftFunctor]

instance presheafCoverMap_epi :
    Epi (presheafCoverMap.{w, v, u} P) := by
  rw [NatTrans.epi_iff_epi_app]
  intro Y
  rw [epi_iff_surjective]
  intro ⟨y⟩
  exact ⟨⟨op (Functor.elementsMk P Y y),
    𝟙 Y.unop⟩, by
    simp only [presheafCoverMap]
    exact congrArg ULift.up
      (congr_fun (P.map_id Y) y)⟩

def presheafCoverIncl (j : P.ElementsPre) :
    uliftYoneda.{max u w}.obj
      j.unop.1.unop ⟶
      presheafCover.{w, v, u} P where
  app _ g := ⟨j, g.down⟩
  naturality _ _ _ := rfl

private lemma presheafCover_factors_aux
    {E F : Cᵒᵖ ⥤ Type (max u w v)}
    (f : presheafCover.{w, v, u} P ⟶ F)
    (e : E ⟶ F) [Epi e]
    (j : P.ElementsPre) :
    ∃ g : uliftYoneda.{max u w}.obj
        j.unop.1.unop ⟶ E,
      g ≫ e = presheafCoverIncl P j ≫ f :=
  Projective.factors
    (presheafCoverIncl P j ≫ f) e

instance presheafCover_projective :
    Projective
      (presheafCover.{w, v, u} P) where
  factors {E F} f e := by
    intro
    have h := fun j ↦
      presheafCover_factors_aux P f e j
    choose g hg using h
    refine ⟨⟨fun Y ⟨j, x⟩ ↦
      (g j).app Y (ULift.up x),
        fun {Y Z} fYZ ↦ ?_⟩, ?_⟩
    · ext ⟨j, x⟩
      exact congr_fun
        ((g j).naturality fYZ)
        (ULift.up x)
    · ext Y ⟨j, x⟩
      exact congr_fun
        (NatTrans.congr_app (hg j) Y)
        (ULift.up x)

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

variable (F : C ⥤ Type (max v w))

/--
The `CoprodCovarRepCat C` object whose evaluation is the
projective cover of `F`.  Indexed by elements of `F`,
with family sending each element `(c, x)` to `c`.
-/
def copresheafCoverObj :
    CoprodCovarRepCat.{u, v, max u w v} C :=
  ccrObjMk (CategoryOfElements.π F).obj

/--
The projective cover of a copresheaf `F`, defined as
the evaluation of `copresheafCoverObj F`.
-/
def copresheafCover :
    C ⥤ Type (max u w v) :=
  ccrToFunctor (copresheafCoverObj F)

/--
The canonical map from `copresheafCover F` to `F`
lifted into the larger universe.
-/
def copresheafCoverMap :
    copresheafCover.{w, v, u} F ⟶
      F ⋙ uliftFunctor.{u, max w v} where
  app Y := fun ⟨j, f⟩ ↦
    ULift.up (F.map f j.2)
  naturality {Y Z} g := by
    ext ⟨j, f⟩
    simp [copresheafCover, ccrToFunctor,
      ccrEvalMap, uliftFunctor]

instance copresheafCoverMap_epi :
    Epi (copresheafCoverMap.{w, v, u} F) := by
  rw [NatTrans.epi_iff_epi_app]
  intro Y
  rw [epi_iff_surjective]
  intro ⟨y⟩
  exact ⟨⟨Functor.elementsMk F Y y,
    𝟙 Y⟩, by
    simp only [copresheafCoverMap]
    exact congrArg ULift.up
      (congr_fun (F.map_id Y) y)⟩

def copresheafCoverIncl (j : F.Elements) :
    uliftCoyoneda.{max u w}.obj (op j.1) ⟶
      copresheafCover.{w, v, u} F where
  app _ g := ⟨j, g.down⟩
  naturality _ _ _ := rfl

private lemma copresheafCover_factors_aux
    {E G : C ⥤ Type (max u w v)}
    (f : copresheafCover.{w, v, u} F ⟶ G)
    (e : E ⟶ G) [Epi e]
    (j : F.Elements) :
    ∃ g : uliftCoyoneda.{max u w}.obj
        (op j.1) ⟶ E,
      g ≫ e =
        copresheafCoverIncl F j ≫ f :=
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
      (g j).app Y (ULift.up x),
        fun {Y Z} fYZ ↦ ?_⟩, ?_⟩
    · ext ⟨j, x⟩
      exact congr_fun
        ((g j).naturality fYZ) (ULift.up x)
    · ext Y ⟨j, x⟩
      exact congr_fun
        (NatTrans.congr_app (hg j) Y)
        (ULift.up x)

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
