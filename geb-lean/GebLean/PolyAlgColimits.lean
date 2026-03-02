import GebLean.PolyFilteredColimits
import Mathlib.CategoryTheory.Limits.Shapes.Reflexive

/-!
# Colimits in Polynomial Algebras

Finitary polynomial endofunctors preserve reflexive
coequalizers.  Combined with filtered colimit
preservation (`PolyFilteredColimits.lean`) and
standard categorical machinery, this yields
`HasColimitsOfSize.{u,u} (PolyAlg P)`.

The reflexive coequalizer argument: a polynomial
functor `Σ_i (B_i → -)` preserves reflexive
coequalizers when each `B_i` is finite, because a
function `B → coeq(f,g)` lifts to `B → Y` (by
finiteness and surjectivity of the coequalizer map),
and the section allows changing one coordinate at a
time to show the lifted value is independent of the
choice of lift.
-/

namespace GebLean

open CategoryTheory CategoryTheory.Limits
open WalkingReflexivePair WalkingReflexivePair.Hom

universe u

/-! ## Factorization Through Zero for WRP Colimits -/

section WrpFactorization

variable {X : Type u}

private lemma wrpSurjZero
    {K : WalkingReflexivePair ⥤ Over X}
    {c : Cocone K} (hc : IsColimit c)
    (x : c.pt.left) :
    ∃ y : (K.obj zero).left,
      (c.ι.app zero).left y = x := by
  have hcT : IsColimit
      ((Over.forget X).mapCocone c) :=
    isColimitOfPreserves (Over.forget X) hc
  obtain ⟨j, y, hy⟩ :=
    Types.jointly_surjective_of_isColimit hcT x
  cases j with
  | zero => exact ⟨y, hy⟩
  | one =>
    refine ⟨(K.map left).left y, ?_⟩
    have hw := congr_fun
      (((Over.forget X).mapCocone c).w left) y
    simp only [Functor.comp_obj,
      Functor.comp_map, Functor.mapCocone_pt,
      Functor.mapCocone_ι_app,
      types_comp_apply] at hw
    exact hw.trans hy

set_option linter.unusedFintypeInType false in
private lemma overWrpFactor
    {K : WalkingReflexivePair ⥤ Over X}
    {c : Cocone K} (hc : IsColimit c)
    {B : Over X} [Fintype B.left]
    (f : B ⟶ c.pt) :
    ∃ g : B ⟶ K.obj zero,
      g ≫ c.ι.app zero = f := by
  have hsurj : ∀ b : B.left,
      ∃ y : (K.obj zero).left,
        (c.ι.app zero).left y = f.left b :=
    fun b => wrpSurjZero hc (f.left b)
  choose yB hyB using hsurj
  have hg_over :
      (K.obj zero).hom ∘ yB = B.hom := by
    funext b
    have hcw := Over.w (c.ι.app zero)
    have hfw := Over.w f
    calc (K.obj zero).hom (yB b)
        = ((c.ι.app zero).left ≫
            c.pt.hom) (yB b) :=
          (congr_fun hcw (yB b)).symm
      _ = c.pt.hom (f.left b) := by
          simp only [types_comp_apply, hyB b]
      _ = B.hom b := congr_fun hfw b
  exact ⟨Over.homMk yB hg_over,
    Over.OverMorphism.ext (funext hyB)⟩

end WrpFactorization

/-! ## CCR Preserves Reflexive Coequalizers -/

section CcrReflexiveColimits

variable {X : Type u}

private lemma wrpCcrNatApp
    {P : CoprodCovarRepCat (Over (X : Type u))}
    {K : WalkingReflexivePair ⥤ Over X}
    (s : Cocone (K ⋙ ccrToFunctor P))
    (i : ccrIndex P)
    {j₁ j₂ : WalkingReflexivePair}
    (g : ccrFamily P i ⟶ K.obj j₁)
    (h : j₁ ⟶ j₂) :
    s.ι.app j₁ (ccrEvalMk i g) =
    s.ι.app j₂
      (ccrEvalMk i (g ≫ K.map h)) := by
  have := congr_fun (s.w h) (ccrEvalMk i g)
  simp only [Functor.comp_map,
    types_comp_apply] at this
  exact this.symm

private lemma wrpCcrCoequalize
    {P : CoprodCovarRepCat (Over (X : Type u))}
    {K : WalkingReflexivePair ⥤ Over X}
    (s : Cocone (K ⋙ ccrToFunctor P))
    (i : ccrIndex P)
    (h : ccrFamily P i ⟶ K.obj one) :
    s.ι.app zero
      (ccrEvalMk i (h ≫ K.map left)) =
    s.ι.app zero
      (ccrEvalMk i (h ≫ K.map right)) :=
  (wrpCcrNatApp s i h left).symm.trans
    (wrpCcrNatApp s i h right)

end CcrReflexiveColimits

end GebLean
