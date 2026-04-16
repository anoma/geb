import GebLean.PolyFilteredColimits
import Mathlib.CategoryTheory.Limits.Shapes.Reflexive
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Monad.Coequalizer
import Mathlib.CategoryTheory.Limits.Constructions.FiniteProductsOfBinaryProducts
import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers
import Mathlib.CategoryTheory.Limits.Constructions.Filtered

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

set_option backward.isDefEq.respectTransparency false in
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

set_option linter.unusedFintypeInType false in
private def wrpUpdateMor
    {P : CoprodCovarRepCat' (Over (X : Type u))}
    {K : WalkingReflexivePair ⥤ Over X}
    (i : ccrIndex P)
    [DecidableEq (ccrFamily P i).left]
    (g : ccrFamily P i ⟶ K.obj zero)
    (b : (ccrFamily P i).left)
    (y : (K.obj zero).left)
    (hy : (K.obj zero).hom y =
      (ccrFamily P i).hom b) :
    ccrFamily P i ⟶ K.obj zero :=
  Over.homMk
    (Function.update g.left b y)
    (by funext b'
        simp only [types_comp_apply,
          Function.update]
        split
        · next h => subst h; exact hy
        · exact congr_fun (Over.w g) b')

private lemma wrpCcrNatApp
    {P : CoprodCovarRepCat' (Over (X : Type u))}
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
    {P : CoprodCovarRepCat' (Over (X : Type u))}
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

private lemma wrpReflLeft
    {K : WalkingReflexivePair ⥤ Over (X : Type u)}
    (y : (K.obj zero).left) :
    (K.map left).left
      ((K.map reflexion).left y) = y := by
  have h := congr_arg CommaMorphism.left
    (map_reflexion_comp_map_left K)
  simp only [Over.comp_left, Over.id_left] at h
  exact congr_fun h y

private lemma wrpReflRight
    {K : WalkingReflexivePair ⥤ Over (X : Type u)}
    (y : (K.obj zero).left) :
    (K.map right).left
      ((K.map reflexion).left y) = y := by
  have h := congr_arg CommaMorphism.left
    (map_reflexion_comp_map_right K)
  simp only [Over.comp_left, Over.id_left] at h
  exact congr_fun h y

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedFintypeInType false in
private lemma wrpCcrOneStep
    {P : CoprodCovarRepCat' (Over (X : Type u))}
    {K : WalkingReflexivePair ⥤ Over X}
    {c : Cocone K} (hc : IsColimit c)
    (s : Cocone (K ⋙ ccrToFunctor P))
    (i : ccrIndex P)
    [DecidableEq (ccrFamily P i).left]
    (g : ccrFamily P i ⟶ K.obj zero)
    (b : (ccrFamily P i).left)
    (y₁ y₂ : (K.obj zero).left)
    (hy₁ : (K.obj zero).hom y₁ =
      (ccrFamily P i).hom b)
    (hy₂ : (K.obj zero).hom y₂ =
      (ccrFamily P i).hom b)
    (heq : (c.ι.app zero).left y₁ =
      (c.ι.app zero).left y₂) :
    s.ι.app zero
      (ccrEvalMk i
        (wrpUpdateMor i g b y₁ hy₁)) =
    s.ι.app zero
      (ccrEvalMk i
        (wrpUpdateMor i g b y₂ hy₂)) := by
  haveI : DecidableEq X := Classical.decEq X
  have hcT : IsColimit
      ((Over.forget X).mapCocone c) :=
    isColimitOfPreserves (Over.forget X) hc
  let Ψ : (K.obj zero).left → s.pt :=
    fun y =>
      if h : (K.obj zero).hom y =
          (ccrFamily P i).hom b
      then s.ι.app zero
        (ccrEvalMk i
          (wrpUpdateMor i g b y h))
      else s.ι.app zero (ccrEvalMk i g)
  have hΨy₁ : Ψ y₁ = s.ι.app zero
      (ccrEvalMk i
        (wrpUpdateMor i g b y₁ hy₁)) :=
    dif_pos hy₁
  have hΨy₂ : Ψ y₂ = s.ι.app zero
      (ccrEvalMk i
        (wrpUpdateMor i g b y₂ hy₂)) :=
    dif_pos hy₂
  rw [← hΨy₁, ← hΨy₂]
  have hfiberLR : ∀ z : (K.obj one).left,
      (K.obj zero).hom ((K.map left).left z) =
      (K.obj zero).hom
        ((K.map right).left z) := by
    intro z
    have hl :=
      congr_fun (Over.w (K.map left)) z
    have hr :=
      congr_fun (Over.w (K.map right)) z
    simp only [types_comp_apply] at hl hr
    exact hl.trans hr.symm
  have hΨeq : ∀ z : (K.obj one).left,
      Ψ ((K.map left).left z) =
        Ψ ((K.map right).left z) := by
    intro z
    simp only [Ψ]
    by_cases hfib : (K.obj zero).hom
        ((K.map left).left z) =
        (ccrFamily P i).hom b
    · rw [dif_pos hfib,
        dif_pos ((hfiberLR z) ▸ hfib)]
      have hzfib : (K.obj one).hom z =
          (ccrFamily P i).hom b := by
        have := congr_fun
          (Over.w (K.map left)) z
        simp only [types_comp_apply] at this
        exact this.symm.trans hfib
      let hMor : ccrFamily P i ⟶ K.obj one :=
        Over.homMk
          (Function.update
            ((K.map reflexion).left ∘ g.left)
            b z)
          (by funext b'
              simp only [types_comp_apply,
                Function.update]
              split
              · next h => subst h; exact hzfib
              · simp only [Function.comp_apply]
                have := congr_fun
                  (Over.w (K.map reflexion))
                  (g.left b')
                simp only [types_comp_apply]
                  at this
                exact this.trans
                  (congr_fun (Over.w g) b'))
      have hMorL : hMor ≫ K.map left =
          wrpUpdateMor i g b
            ((K.map left).left z) hfib := by
        apply Over.OverMorphism.ext; funext b'
        change (K.map left).left
            (Function.update
              ((K.map reflexion).left ∘ g.left)
              b z b') =
          Function.update g.left b
            ((K.map left).left z) b'
        simp only [Function.update_apply]
        split
        · rfl
        · simp only [Function.comp_apply]
          exact wrpReflLeft (g.left b')
      have hMorR : hMor ≫ K.map right =
          wrpUpdateMor i g b
            ((K.map right).left z)
            ((hfiberLR z) ▸ hfib) := by
        apply Over.OverMorphism.ext; funext b'
        change (K.map right).left
            (Function.update
              ((K.map reflexion).left ∘ g.left)
              b z b') =
          Function.update g.left b
            ((K.map right).left z) b'
        simp only [Function.update_apply]
        split
        · rfl
        · simp only [Function.comp_apply]
          exact wrpReflRight (g.left b')
      rw [← hMorL, ← hMorR]
      exact wrpCcrCoequalize s i hMor
    · rw [dif_neg hfib,
        dif_neg (by rwa [hfiberLR z] at hfib)]
  let F' := K ⋙ Over.forget X
  let qCone : Cocone F' :=
    { pt := F'.ColimitType
      ι := {
        app := F'.ιColimitType
        naturality := by
          intro j₁ j₂ f; funext x
          simp only [Functor.const_obj_obj,
            Functor.const_obj_map,
            types_comp_apply,
            Functor.ιColimitType_map,
            types_id_apply]
      } }
  have hι : F'.ιColimitType zero y₁ =
      F'.ιColimitType zero y₂ := by
    have h₁ := congr_fun
      (hcT.fac qCone zero) y₁
    have h₂ := congr_fun
      (hcT.fac qCone zero) y₂
    simp only [types_comp_apply,
      Functor.mapCocone_ι_app] at h₁ h₂
    dsimp only [qCone] at h₁ h₂
    rw [← h₁, ← h₂]
    exact congr_arg (hcT.desc qCone) heq
  let ql : (Σ j, F'.obj j) → s.pt :=
    fun | ⟨.zero, y⟩ => Ψ y
        | ⟨.one, z⟩ =>
          Ψ ((K.map left).left z)
  have qlr : ∀ a b,
      F'.ColimitTypeRel a b →
      ql a = ql b := by
    intro ⟨j₁, x₁⟩ ⟨j₂, x₂⟩ ⟨f, hfx⟩
    cases f with
    | left =>
      dsimp at hfx; subst hfx; rfl
    | right =>
      dsimp at hfx; subst hfx
      exact hΨeq x₁
    | reflexion =>
      dsimp at hfx; subst hfx
      change Ψ x₁ = Ψ ((K.map left).left
        ((K.map reflexion).left x₁))
      rw [wrpReflLeft]
    | id =>
      dsimp at hfx; subst hfx
      exact (congr_arg (fun y => ql ⟨_, y⟩)
        (congr_fun (F'.map_id _) x₁)).symm
    | leftCompReflexion =>
      dsimp at hfx; subst hfx
      change Ψ ((K.map left).left x₁) =
        Ψ ((K.map left).left
          ((K.map (left ≫ reflexion)).left
            x₁))
      have hc :=
        congr_arg CommaMorphism.left
          (K.map_comp left reflexion)
      simp only [Over.comp_left] at hc
      rw [hc, types_comp_apply, wrpReflLeft]
    | rightCompReflexion =>
      dsimp at hfx; subst hfx
      change Ψ ((K.map left).left x₁) =
        Ψ ((K.map left).left
          ((K.map (right ≫ reflexion)).left
            x₁))
      have hc :=
        congr_arg CommaMorphism.left
          (K.map_comp right reflexion)
      simp only [Over.comp_left] at hc
      rw [hc, types_comp_apply, wrpReflLeft]
      exact hΨeq x₁
  exact congr_arg (Quot.lift ql qlr) hι

set_option linter.unusedFintypeInType false in
private lemma wrpCcrWellDefined
    {P : CoprodCovarRepCat' (Over (X : Type u))}
    {K : WalkingReflexivePair ⥤ Over X}
    {c : Cocone K} (hc : IsColimit c)
    (s : Cocone (K ⋙ ccrToFunctor P))
    (i : ccrIndex P)
    [Fintype (ccrFamily P i).left]
    (g₁ g₂ : ccrFamily P i ⟶ K.obj zero)
    (heq : g₁ ≫ c.ι.app zero =
      g₂ ≫ c.ι.app zero) :
    s.ι.app zero (ccrEvalMk i g₁) =
    s.ι.app zero (ccrEvalMk i g₂) := by
  haveI : DecidableEq (ccrFamily P i).left :=
    Classical.decEq _
  suffices h : ∀ S : Finset (ccrFamily P i).left,
      ∀ g : ccrFamily P i ⟶ K.obj zero,
      (∀ b ∈ S, g.left b = g₁.left b) →
      (∀ b, b ∉ S → g.left b = g₂.left b) →
      s.ι.app zero (ccrEvalMk i g) =
        s.ι.app zero (ccrEvalMk i g₂) by
    exact h Finset.univ g₁ (fun b _ => rfl)
      (fun b hb =>
        absurd (Finset.mem_univ b) hb)
  intro S
  induction S using Finset.cons_induction with
  | empty =>
    intro g _ hout
    have hg : g = g₂ :=
      Over.OverMorphism.ext (funext fun b =>
        hout b (by simp))
    rw [hg]
  | cons b S hbS ih =>
    intro g hin hout
    have hfibg : (K.obj zero).hom (g.left b) =
        (ccrFamily P i).hom b := by
      have := congr_fun (Over.w g) b
      simp only [types_comp_apply] at this
      exact this
    have hfib₂ : (K.obj zero).hom (g₂.left b) =
        (ccrFamily P i).hom b := by
      have := congr_fun (Over.w g₂) b
      simp only [types_comp_apply] at this
      exact this
    have hgb : g.left b = g₁.left b :=
      hin b (Finset.mem_cons_self b S)
    have hcolim :
        (c.ι.app zero).left (g.left b) =
        (c.ι.app zero).left (g₂.left b) := by
      rw [hgb]
      exact congr_fun
        (congr_arg CommaMorphism.left heq) b
    have hup_self :
        wrpUpdateMor i g b (g.left b)
          hfibg = g :=
      Over.OverMorphism.ext
        (Function.update_eq_self b g.left)
    have hstep := wrpCcrOneStep hc s i g b
      (g.left b) (g₂.left b) hfibg
      hfib₂ hcolim
    rw [hup_self] at hstep
    exact hstep.trans (ih
      (wrpUpdateMor i g b (g₂.left b) hfib₂)
      (fun b' hb' => by
        change Function.update g.left b
          (g₂.left b) b' = g₁.left b'
        rw [Function.update_apply, if_neg]
        · exact hin b'
            (Finset.mem_cons.mpr (Or.inr hb'))
        · exact fun h => absurd (h ▸ hb') hbS)
      (fun b' hb' => by
        change Function.update g.left b
          (g₂.left b) b' = g₂.left b'
        rw [Function.update_apply]
        split
        · next h => rw [h]
        · next h => exact hout b' (fun hm =>
            (Finset.mem_cons.mp hm).elim
              h hb')))

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedFintypeInType false in
instance ccrPreservesReflexiveColimits
    (P : CoprodCovarRepCat' (Over (X : Type u)))
    (hfin : ∀ i, Fintype (ccrFamily P i).left) :
    PreservesColimitsOfShape WalkingReflexivePair
      (ccrToFunctor P) where
  preservesColimit {K} := {
    preserves := fun {c} hc => by
      have descFact :
          ∀ x : ccrEval P c.pt,
          ∃ g : ccrFamily P
            (ccrEvalIndex x) ⟶ K.obj zero,
          g ≫ c.ι.app zero =
            ccrEvalMor x := fun x => by
        haveI := hfin (ccrEvalIndex x)
        exact overWrpFactor hc (ccrEvalMor x)
      exact ⟨{
        desc := fun s x =>
          s.ι.app zero
            (ccrEvalMk (ccrEvalIndex x)
              (descFact x).choose)
        fac := fun s j => by
          funext y
          simp only [types_comp_apply]
          haveI := hfin (ccrEvalIndex y)
          cases j with
          | zero =>
            let gz := (descFact
              (ccrEvalMap
                (c.ι.app zero) y)).choose
            let hgz := (descFact
              (ccrEvalMap
                (c.ι.app zero) y)).choose_spec
            change s.ι.app zero
                (ccrEvalMk (ccrEvalIndex y)
                  gz) =
              s.ι.app zero
                (ccrEvalMk (ccrEvalIndex y)
                  (ccrEvalMor y))
            exact wrpCcrWellDefined hc s _
              gz (ccrEvalMor y) hgz
          | one =>
            let gz := (descFact
              (ccrEvalMap
                (c.ι.app one) y)).choose
            let hgz := (descFact
              (ccrEvalMap
                (c.ι.app one) y)).choose_spec
            change s.ι.app zero
                (ccrEvalMk (ccrEvalIndex y)
                  gz) =
              s.ι.app one
                (ccrEvalMk (ccrEvalIndex y)
                  (ccrEvalMor y))
            exact (wrpCcrWellDefined hc s _
              gz (ccrEvalMor y ≫ K.map left)
              (by rw [Category.assoc, c.w left]
                  exact hgz)).trans
              (wrpCcrNatApp s _
                (ccrEvalMor y) left).symm
        uniq := fun s m hm => by
          funext x
          haveI := hfin (ccrEvalIndex x)
          let gx := (descFact x).choose
          let hgx := (descFact x).choose_spec
          have hx :
              ccrEvalMap (c.ι.app zero)
                (ccrEvalMk (ccrEvalIndex x)
                  gx) = x :=
            Sigma.ext rfl (heq_of_eq hgx)
          conv_lhs => rw [← hx]
          have hmz := congr_fun (hm zero)
            (ccrEvalMk (ccrEvalIndex x) gx)
          simp only [types_comp_apply] at hmz
          exact hmz
      }⟩
  }

end CcrReflexiveColimits

/-! ## Universe-Flexible Pi Colimits

Mathlib's `pi.coconeOfCoconeEvalIsColimit`
constrains `I` and `J` to the same universe.
The following versions allow `I` and `J` in
different universes.
-/

section PiColimitFlex

variable {I : Type*} {C : I → Type*}
  [∀ i, Category (C i)]
  {J : Type*} [Category J]
  {F : J ⥤ ∀ i, C i}

private def piCoconeEval
    (c : Cocone F) (i : I) :
    Cocone (F ⋙ Pi.eval C i) where
  pt := c.pt i
  ι := {
    app := fun j => c.ι.app j i
    naturality := fun _ _ f =>
      congr_fun (c.ι.naturality f) i
  }

private def piIsColimitOfEval
    {c : Cocone F}
    (hc : ∀ i,
      IsColimit (piCoconeEval c i)) :
    IsColimit c where
  desc s i :=
    (hc i).desc (piCoconeEval s i)
  fac s j := by
    funext i
    exact (hc i).fac (piCoconeEval s i) j
  uniq s m w := by
    funext i
    exact (hc i).uniq (piCoconeEval s i)
      (m i) fun j => congr_fun (w j) i

end PiColimitFlex

/-! ## Lifting Through Polynomial Layers -/

section PolyFamilyReflexiveColimits

variable {X Y : Type u}

set_option linter.unusedFintypeInType false in
instance polyToOverFamilyPreservesReflexive
    (P : PolyToOverCat (D := Over X) Y)
    (hfin : ∀ (y : Y) (i : ccrIndex (P y)),
      Fintype (ccrFamily (P y) i).left) :
    PreservesColimitsOfShape WalkingReflexivePair
      (polyToOverFamilyFunctor Y P) where
  preservesColimit {K} := {
    preserves := fun {c} hc => by
      have hcy : ∀ y,
          IsColimit
            (piCoconeEval
              ((polyToOverFamilyFunctor Y
                P).mapCocone c) y) := by
        intro y
        have inst :
            PreservesColimitsOfShape
              WalkingReflexivePair
              (ccrToFunctor (P y)) :=
          ccrPreservesReflexiveColimits
            (P y) (hfin y)
        exact (inst.preservesColimit
          (K := K) |>.preserves hc).some
      exact
        ⟨piIsColimitOfEval hcy⟩
  }

set_option linter.unusedFintypeInType false in
instance polyToOverPreservesReflexive
    (P : PolyToOverCat (D := Over X) Y)
    (hfin : ∀ (y : Y) (i : ccrIndex (P y)),
      Fintype (ccrFamily (P y) i).left) :
    PreservesColimitsOfShape WalkingReflexivePair
      (polyToOverFunctor Y P) := by
  haveI : (familySliceForward Y).IsEquivalence :=
    (familySliceEquiv Y).isEquivalence_functor
  haveI : PreservesColimitsOfShape
      WalkingReflexivePair
      (polyToOverFamilyFunctor Y P) :=
    polyToOverFamilyPreservesReflexive P hfin
  exact inferInstanceAs
    (PreservesColimitsOfShape
      WalkingReflexivePair
      (polyToOverFamilyFunctor Y P ⋙
        familySliceForward Y))

end PolyFamilyReflexiveColimits

section PolyBetweenReflexiveColimits

variable {X Y : Type u}

instance polyBetweenPreservesReflexive
    (P : PolyFunctorBetweenCat X Y)
    [hf : PolyBetweenFinitary X Y P] :
    PreservesColimitsOfShape WalkingReflexivePair
      (polyBetweenEvalFunctor X Y P) :=
  polyToOverPreservesReflexive P
    (fun y i => hf.data.familyFintype y i)

instance polyEndoPreservesReflexive
    (P : PolyEndo X)
    [PolyBetweenFinitary X X P] :
    PreservesColimitsOfShape WalkingReflexivePair
      (polyEndoFunctor X P) :=
  polyBetweenPreservesReflexive P

end PolyBetweenReflexiveColimits

section FreeMonadReflexiveColimits

variable {X : Type u}

instance polyFreeMonadPreservesReflexive
    (P : PolyEndo X)
    [PolyBetweenFinitary X X P] :
    PreservesColimitsOfShape WalkingReflexivePair
      (polyFreeMonad X P).toFunctor :=
  preservesColimitsOfShape_of_natIso
    (polyFreeMonadIso X P).symm

end FreeMonadReflexiveColimits

section AlgReflexiveColimits

variable {X : Type u}

instance polyAlgHasWrpColimits
    (P : PolyEndo X)
    [PolyBetweenFinitary X X P] :
    HasColimitsOfShape WalkingReflexivePair
      (PolyAlg P) := by
  haveI : HasColimitsOfShape
      WalkingReflexivePair
      (polyFreeMonad X P).Algebra :=
    hasColimitsOfShape_of_hasColimitsOfShape_createsColimitsOfShape
      (Monad.forget (polyFreeMonad X P))
  exact Adjunction.hasColimitsOfShape_of_equivalence
    (polyAlgMonadEquiv X P).functor

instance polyAlgHasReflexiveCoequalizers
    (P : PolyEndo X)
    [PolyBetweenFinitary X X P] :
    HasReflexiveCoequalizers (PolyAlg P) :=
  hasReflexiveCoequalizers_iff.mp inferInstance

end AlgReflexiveColimits

section AlgInitial

variable {X : Type u}

instance polyAlgHasInitial
    (P : PolyEndo X) :
    HasInitial (PolyAlg P) :=
  (polyFixAlg_isInitial P).hasInitial

end AlgInitial

section BeckCoprod

set_option backward.isDefEq.respectTransparency false in
/--
Monad algebras have binary coproducts when the base
category does and the algebra category has reflexive
coequalizers.  The coproduct is the reflexive
coequalizer of a pair of free-algebra maps induced
by the two algebra structure maps and the monad
multiplication on the coproduct of the underlying
objects.
-/
lemma monadAlgHasBinaryCoproducts
    {C : Type*} [Category C]
    [HasBinaryCoproducts C]
    (T : Monad C)
    [HasReflexiveCoequalizers T.Algebra] :
    HasBinaryCoproducts T.Algebra := by
  suffices h : ∀ (α β : T.Algebra),
      HasColimit (pair α β) by
    exact @hasBinaryCoproducts_of_hasColimit_pair
      T.Algebra _ (fun {X Y} => h X Y)
  intro α β
  let C0 := α.A ⨿ β.A
  let C1 := (T : C ⥤ C).obj α.A ⨿
    (T : C ⥤ C).obj β.A
  let φ : T.free.obj C1 ⟶ T.free.obj C0 :=
    T.free.map
      (coprod.desc
        (α.a ≫ coprod.inl)
        (β.a ≫ coprod.inr))
  let g : C1 ⟶ (T : C ⥤ C).obj C0 :=
    coprod.desc
      ((T : C ⥤ C).map coprod.inl)
      ((T : C ⥤ C).map coprod.inr)
  let ψ : T.free.obj C1 ⟶ T.free.obj C0 :=
    { f := (T : C ⥤ C).map g ≫ T.μ.app C0
      h := by
        simp [← T.μ.naturality_assoc,
          T.assoc] }
  let s : T.free.obj C0 ⟶ T.free.obj C1 :=
    T.free.map
      (coprod.desc
        (T.η.app α.A ≫ coprod.inl)
        (T.η.app β.A ≫ coprod.inr))
  have hsφ : s ≫ φ = 𝟙 _ := by
    change T.free.map _ ≫ T.free.map _ = _
    rw [← T.free.map_comp, ← T.free.map_id]
    congr 1
    apply coprod.hom_ext
    · rw [coprod.inl_desc_assoc, Category.assoc,
        coprod.inl_desc, ← Category.assoc,
        α.unit, Category.id_comp, Category.comp_id]
    · rw [coprod.inr_desc_assoc, Category.assoc,
        coprod.inr_desc, ← Category.assoc,
        β.unit, Category.id_comp, Category.comp_id]
  have inner : coprod.desc
      (T.η.app α.A ≫ coprod.inl)
      (T.η.app β.A ≫ coprod.inr) ≫ g =
    T.η.app C0 := by
    apply coprod.hom_ext
    · rw [coprod.inl_desc_assoc,
        Category.assoc, coprod.inl_desc]
      exact (T.η.naturality coprod.inl).symm
    · rw [coprod.inr_desc_assoc,
        Category.assoc, coprod.inr_desc]
      exact (T.η.naturality coprod.inr).symm
  have hsψ : s ≫ ψ = 𝟙 _ := by
    apply Monad.Algebra.Hom.ext
    change s.f ≫ ψ.f = 𝟙 _
    change (T : C ⥤ C).map
        (coprod.desc
          (T.η.app α.A ≫ coprod.inl)
          (T.η.app β.A ≫ coprod.inr)) ≫
      ((T : C ⥤ C).map g ≫ T.μ.app C0) = 𝟙 _
    rw [← Category.assoc, ← (T : C ⥤ C).map_comp,
      inner]
    exact T.right_unit C0
  haveI : IsReflexivePair φ ψ :=
    IsReflexivePair.mk' s hsφ hsψ
  have hφ_inl :
      Monad.FreeCoequalizer.topMap α ≫
        T.free.map
          (coprod.inl : α.A ⟶ C0) =
      T.free.map
        (coprod.inl :
          (T : C ⥤ C).obj α.A ⟶ C1) ≫ φ := by
    change T.free.map _ ≫ T.free.map _ =
      T.free.map _ ≫ T.free.map _
    simp only [← T.free.map_comp,
      coprod.inl_desc]
  have hψ_inl :
      Monad.FreeCoequalizer.bottomMap α ≫
        T.free.map
          (coprod.inl : α.A ⟶ C0) =
      T.free.map
        (coprod.inl :
          (T : C ⥤ C).obj α.A ⟶ C1) ≫ ψ := by
    apply Monad.Algebra.Hom.ext
    change T.μ.app α.A ≫
        (T : C ⥤ C).map
          (coprod.inl : α.A ⟶ C0) =
      (T : C ⥤ C).map
        (coprod.inl :
          (T : C ⥤ C).obj α.A ⟶ C1) ≫
      ((T : C ⥤ C).map g ≫ T.μ.app C0)
    rw [← Category.assoc,
      ← (T : C ⥤ C).map_comp,
      show (coprod.inl :
            (T : C ⥤ C).obj α.A ⟶ C1) ≫ g =
          (T : C ⥤ C).map coprod.inl
        from coprod.inl_desc _ _]
    exact (T.μ.naturality coprod.inl).symm
  have hinl :
      Monad.FreeCoequalizer.topMap α ≫
        T.free.map coprod.inl ≫
        coequalizer.π φ ψ =
      Monad.FreeCoequalizer.bottomMap α ≫
        T.free.map coprod.inl ≫
        coequalizer.π φ ψ := by
    rw [← Category.assoc, hφ_inl,
      ← Category.assoc, hψ_inl,
      Category.assoc, Category.assoc,
      coequalizer.condition]
  have hφ_inr :
      Monad.FreeCoequalizer.topMap β ≫
        T.free.map
          (coprod.inr : β.A ⟶ C0) =
      T.free.map
        (coprod.inr :
          (T : C ⥤ C).obj β.A ⟶ C1) ≫ φ := by
    change T.free.map _ ≫ T.free.map _ =
      T.free.map _ ≫ T.free.map _
    simp only [← T.free.map_comp,
      coprod.inr_desc]
  have hψ_inr :
      Monad.FreeCoequalizer.bottomMap β ≫
        T.free.map
          (coprod.inr : β.A ⟶ C0) =
      T.free.map
        (coprod.inr :
          (T : C ⥤ C).obj β.A ⟶ C1) ≫ ψ := by
    apply Monad.Algebra.Hom.ext
    change T.μ.app β.A ≫
        (T : C ⥤ C).map
          (coprod.inr : β.A ⟶ C0) =
      (T : C ⥤ C).map
        (coprod.inr :
          (T : C ⥤ C).obj β.A ⟶ C1) ≫
      ((T : C ⥤ C).map g ≫ T.μ.app C0)
    rw [← Category.assoc,
      ← (T : C ⥤ C).map_comp,
      show (coprod.inr :
            (T : C ⥤ C).obj β.A ⟶ C1) ≫ g =
          (T : C ⥤ C).map coprod.inr
        from coprod.inr_desc _ _]
    exact (T.μ.naturality coprod.inr).symm
  have hinr :
      Monad.FreeCoequalizer.topMap β ≫
        T.free.map coprod.inr ≫
        coequalizer.π φ ψ =
      Monad.FreeCoequalizer.bottomMap β ≫
        T.free.map coprod.inr ≫
        coequalizer.π φ ψ := by
    rw [← Category.assoc, hφ_inr,
      ← Category.assoc, hψ_inr,
      Category.assoc, Category.assoc,
      coequalizer.condition]
  let inl_alg : α ⟶ coequalizer φ ψ :=
    (Monad.beckAlgebraCoequalizer α).desc
      (Cofork.ofπ
        (T.free.map coprod.inl ≫
          coequalizer.π φ ψ)
        hinl)
  let inr_alg : β ⟶ coequalizer φ ψ :=
    (Monad.beckAlgebraCoequalizer β).desc
      (Cofork.ofπ
        (T.free.map coprod.inr ≫
          coequalizer.π φ ψ)
        hinr)
  have beck_fac_inl :
      Monad.FreeCoequalizer.π α ≫ inl_alg =
        T.free.map coprod.inl ≫
          coequalizer.π φ ψ :=
    (Monad.beckAlgebraCoequalizer α).fac _
      WalkingParallelPair.one
  have beck_fac_inr :
      Monad.FreeCoequalizer.π β ≫ inr_alg =
        T.free.map coprod.inr ≫
          coequalizer.π φ ψ :=
    (Monad.beckAlgebraCoequalizer β).fac _
      WalkingParallelPair.one
  let cofan := BinaryCofan.mk inl_alg inr_alg
  -- Construct the desc map: given algebra homs
  -- f' : α → γ, g' : β → γ, produce Q → γ
  -- via the coequalizer universal property
  have mk_desc :
      ∀ (γ : T.Algebra)
        (f' : α ⟶ γ) (g' : β ⟶ γ),
      ∃ (d : cofan.pt ⟶ γ),
        cofan.inl ≫ d = f' ∧
        cofan.inr ≫ d = g' ∧
        ∀ (m : cofan.pt ⟶ γ),
          cofan.inl ≫ m = f' →
          cofan.inr ≫ m = g' → m = d := by
    intro γ f' g'
    let u : C0 ⟶ γ.A :=
      coprod.desc f'.f g'.f
    let h_cand : T.free.obj C0 ⟶ γ :=
      { f := (T : C ⥤ C).map u ≫ γ.a
        h := by
          change (T : C ⥤ C).map
              ((T : C ⥤ C).map u ≫ γ.a) ≫
                γ.a =
            T.μ.app C0 ≫
              ((T : C ⥤ C).map u ≫ γ.a)
          simp only [(T : C ⥤ C).map_comp,
            Category.assoc, γ.assoc.symm]
          simp only [← Category.assoc]
          congr 1
          rw [← Functor.comp_map
            T.toFunctor T.toFunctor]
          exact T.μ.naturality u }
    have desc_comp_u :
        coprod.desc (α.a ≫ coprod.inl)
          (β.a ≫ coprod.inr) ≫ u =
        coprod.desc
          ((T : C ⥤ C).map f'.f ≫ γ.a)
          ((T : C ⥤ C).map g'.f ≫ γ.a) := by
      change coprod.desc (α.a ≫ coprod.inl)
          (β.a ≫ coprod.inr) ≫
        coprod.desc f'.f g'.f = _
      apply coprod.hom_ext
      · rw [coprod.inl_desc_assoc,
          Category.assoc, coprod.inl_desc,
          coprod.inl_desc, ← f'.h]
      · rw [coprod.inr_desc_assoc,
          Category.assoc, coprod.inr_desc,
          coprod.inr_desc, ← g'.h]
    have g_comp_u :
        g ≫ (T : C ⥤ C).map u ≫ γ.a =
        coprod.desc
          ((T : C ⥤ C).map f'.f ≫ γ.a)
          ((T : C ⥤ C).map g'.f ≫ γ.a) := by
      change coprod.desc
          ((T : C ⥤ C).map coprod.inl)
          ((T : C ⥤ C).map coprod.inr) ≫
        (T : C ⥤ C).map
          (coprod.desc f'.f g'.f) ≫ γ.a = _
      apply coprod.hom_ext
      · rw [coprod.inl_desc_assoc,
          ← Category.assoc,
          ← (T : C ⥤ C).map_comp,
          coprod.inl_desc, coprod.inl_desc]
      · rw [coprod.inr_desc_assoc,
          ← Category.assoc,
          ← (T : C ⥤ C).map_comp,
          coprod.inr_desc, coprod.inr_desc]
    have h_coeq : φ ≫ h_cand = ψ ≫ h_cand := by
      apply Monad.Algebra.Hom.ext
      change φ.f ≫ h_cand.f = ψ.f ≫ h_cand.f
      let common := coprod.desc
        ((T : C ⥤ C).map f'.f ≫ γ.a)
        ((T : C ⥤ C).map g'.f ≫ γ.a)
      have h_lhs :
          φ.f ≫ h_cand.f =
          (T : C ⥤ C).map common ≫ γ.a := by
        change (T : C ⥤ C).map
            (coprod.desc (α.a ≫ coprod.inl)
              (β.a ≫ coprod.inr)) ≫
          ((T : C ⥤ C).map u ≫ γ.a) = _
        rw [← Category.assoc,
          ← (T : C ⥤ C).map_comp,
          desc_comp_u]
      have h_rhs :
          ψ.f ≫ h_cand.f =
          (T : C ⥤ C).map common ≫ γ.a := by
        change ((T : C ⥤ C).map g ≫ T.μ.app C0) ≫
          ((T : C ⥤ C).map u ≫ γ.a) = _
        rw [Category.assoc,
          ← T.μ.naturality_assoc u]
        rw [γ.assoc,
          Functor.comp_map
            T.toFunctor T.toFunctor]
        simp only [← Category.assoc]
        congr 1
        simp only [← (T : C ⥤ C).map_comp]
        congr 1
        rw [Category.assoc]
        exact g_comp_u
      rw [h_lhs, h_rhs]
    let d : cofan.pt ⟶ γ :=
      coequalizer.desc h_cand h_coeq
    have fac_inl : cofan.inl ≫ d = f' := by
      apply Cofork.IsColimit.hom_ext
        (Monad.beckAlgebraCoequalizer α)
      change Monad.FreeCoequalizer.π α ≫
        inl_alg ≫ d =
        Monad.FreeCoequalizer.π α ≫ f'
      rw [← Category.assoc,
        beck_fac_inl, Category.assoc,
        coequalizer.π_desc]
      apply Monad.Algebra.Hom.ext
      change (T : C ⥤ C).map coprod.inl ≫
        ((T : C ⥤ C).map u ≫ γ.a) =
        α.a ≫ f'.f
      rw [← Category.assoc,
        ← (T : C ⥤ C).map_comp]
      change (T : C ⥤ C).map
        (coprod.inl ≫ coprod.desc f'.f g'.f) ≫
        γ.a = α.a ≫ f'.f
      rw [coprod.inl_desc]
      exact f'.h
    have fac_inr : cofan.inr ≫ d = g' := by
      apply Cofork.IsColimit.hom_ext
        (Monad.beckAlgebraCoequalizer β)
      change Monad.FreeCoequalizer.π β ≫
        inr_alg ≫ d =
        Monad.FreeCoequalizer.π β ≫ g'
      rw [← Category.assoc,
        beck_fac_inr, Category.assoc,
        coequalizer.π_desc]
      apply Monad.Algebra.Hom.ext
      change (T : C ⥤ C).map coprod.inr ≫
        ((T : C ⥤ C).map u ≫ γ.a) =
        β.a ≫ g'.f
      rw [← Category.assoc,
        ← (T : C ⥤ C).map_comp]
      change (T : C ⥤ C).map
        (coprod.inr ≫ coprod.desc f'.f g'.f) ≫
        γ.a = β.a ≫ g'.f
      rw [coprod.inr_desc]
      exact g'.h
    refine ⟨d, fac_inl, fac_inr, fun m hml hmr => ?_⟩
    apply coequalizer.hom_ext
    rw [coequalizer.π_desc]
    have gen_eq :
        T.η.app C0 ≫
          (coequalizer.π φ ψ ≫ m).f =
        u := by
      apply coprod.hom_ext
      · change coprod.inl ≫ T.η.app C0 ≫
            (coequalizer.π φ ψ ≫ m).f =
          coprod.inl ≫ coprod.desc f'.f g'.f
        rw [coprod.inl_desc]
        simp only [← Category.assoc]
        rw [show coprod.inl ≫ T.η.app C0 =
          T.η.app α.A ≫
            (T : C ⥤ C).map coprod.inl
          from T.η.naturality coprod.inl]
        simp only [Category.assoc]
        change T.η.app α.A ≫
          (T.free.map coprod.inl ≫
            coequalizer.π φ ψ ≫ m).f = f'.f
        rw [← Category.assoc,
          beck_fac_inl.symm,
          Category.assoc]
        change T.η.app α.A ≫
          α.a ≫ (inl_alg ≫ m).f = f'.f
        rw [← Category.assoc, α.unit]
        exact (Category.id_comp _).trans
          (congrArg Monad.Algebra.Hom.f hml)
      · change coprod.inr ≫ T.η.app C0 ≫
            (coequalizer.π φ ψ ≫ m).f =
          coprod.inr ≫ coprod.desc f'.f g'.f
        rw [coprod.inr_desc]
        simp only [← Category.assoc]
        rw [show coprod.inr ≫ T.η.app C0 =
          T.η.app β.A ≫
            (T : C ⥤ C).map coprod.inr
          from T.η.naturality coprod.inr]
        simp only [Category.assoc]
        change T.η.app β.A ≫
          (T.free.map coprod.inr ≫
            coequalizer.π φ ψ ≫ m).f = g'.f
        rw [← Category.assoc,
          beck_fac_inr.symm,
          Category.assoc]
        change T.η.app β.A ≫
          β.a ≫ (inr_alg ≫ m).f = g'.f
        rw [← Category.assoc, β.unit]
        exact (Category.id_comp _).trans
          (congrArg Monad.Algebra.Hom.f hmr)
    apply Monad.Algebra.Hom.ext
    calc (coequalizer.π φ ψ ≫ m).f
        = (T : C ⥤ C).map
            (T.η.app C0 ≫
              (coequalizer.π φ ψ ≫ m).f) ≫
            γ.a := by
          rw [(T : C ⥤ C).map_comp,
            Category.assoc,
            (coequalizer.π φ ψ ≫ m).h,
            ← Category.assoc]
          change (coequalizer.π φ ψ ≫ m).f =
            (T.map (T.η.app C0) ≫
              T.μ.app C0) ≫
            (coequalizer.π φ ψ ≫ m).f
          rw [T.right_unit]
          exact (Category.id_comp _).symm
      _ = (T : C ⥤ C).map u ≫ γ.a := by
          rw [gen_eq]
      _ = h_cand.f := rfl
  exact ⟨⟨cofan, BinaryCofan.IsColimit.mk cofan
    (fun f' g' =>
      (mk_desc _ f' g').choose)
    (fun f' g' =>
      (mk_desc _ f' g').choose_spec.1)
    (fun f' g' =>
      (mk_desc _ f' g').choose_spec.2.1)
    (fun f' g' m hml hmr =>
      (mk_desc _ f' g').choose_spec.2.2
        m hml hmr)⟩⟩

end BeckCoprod

section AlgFiniteCoproducts

variable {X : Type u}

instance polyAlgHasBinaryCoproducts
    (P : PolyEndo X)
    [PolyBetweenFinitary X X P] :
    HasBinaryCoproducts (PolyAlg P) := by
  haveI : HasReflexiveCoequalizers
      (polyFreeMonad X P).Algebra := by
    haveI : HasColimitsOfShape
        WalkingReflexivePair
        (polyFreeMonad X P).Algebra :=
      Adjunction.hasColimitsOfShape_of_equivalence
        (polyAlgMonadEquiv X P).inverse
    exact hasReflexiveCoequalizers_iff.mp
      inferInstance
  haveI : HasBinaryCoproducts (Over X) :=
    hasColimitsOfShape_of_hasColimitsOfShape_createsColimitsOfShape
      (Over.forget X)
  haveI : HasBinaryCoproducts
      (polyFreeMonad X P).Algebra :=
    monadAlgHasBinaryCoproducts
      (polyFreeMonad X P)
  exact Adjunction.hasColimitsOfShape_of_equivalence
    (polyAlgMonadEquiv X P).functor

instance polyAlgHasFiniteCoproducts
    (P : PolyEndo X)
    [PolyBetweenFinitary X X P] :
    HasFiniteCoproducts (PolyAlg P) :=
  hasFiniteCoproducts_of_has_binary_and_initial

end AlgFiniteCoproducts

section CoprodCoeqTrick

set_option backward.isDefEq.respectTransparency false in
lemma hasCoequalizer_of_reflexive_and_binary
    {C : Type*} [Category C]
    [HasBinaryCoproducts C]
    [HasReflexiveCoequalizers C]
    {A B : C} (f g : A ⟶ B) :
    HasCoequalizer f g := by
  let f' : A ⨿ B ⟶ B := coprod.desc f (𝟙 B)
  let g' : A ⨿ B ⟶ B := coprod.desc g (𝟙 B)
  haveI : IsReflexivePair f' g' :=
    IsReflexivePair.mk' coprod.inr
      (coprod.inr_desc _ _)
      (coprod.inr_desc _ _)
  haveI : HasCoequalizer f' g' :=
    HasReflexiveCoequalizers.has_coeq f' g'
  have cond : f ≫ coequalizer.π f' g' =
      g ≫ coequalizer.π f' g' := by
    have h := coequalizer.condition f' g'
    rw [show f = coprod.inl ≫ f' from
      (coprod.inl_desc _ _).symm,
      show g = coprod.inl ≫ g' from
      (coprod.inl_desc _ _).symm,
      Category.assoc, h, Category.assoc]
  have desc : ∀ s : Cofork f g,
      f' ≫ Cofork.π s = g' ≫ Cofork.π s := by
    intro s
    apply coprod.hom_ext
    · rw [coprod.inl_desc_assoc,
        coprod.inl_desc_assoc]
      exact s.condition
    · rw [coprod.inr_desc_assoc,
        coprod.inr_desc_assoc]
  exact HasColimit.mk ⟨
    Cofork.ofπ (coequalizer.π f' g') cond,
    Cofork.IsColimit.mk _
      (fun s => coequalizer.desc
        (f := f') (g := g')
        (Cofork.π s) (desc s))
      (fun s => coequalizer.π_desc _ _)
      (fun s m hm =>
        coequalizer.hom_ext (f := f') (g := g')
          (by rw [coequalizer.π_desc]; exact hm))⟩

lemma hasCoequalizers_of_hasReflexive_and_binary
    {C : Type*} [Category C]
    [HasBinaryCoproducts C]
    [HasReflexiveCoequalizers C] :
    HasCoequalizers C := by
  haveI : ∀ {X Y : C} {f g : X ⟶ Y},
      HasColimit (parallelPair f g) :=
    fun {_ _ f g} =>
      hasCoequalizer_of_reflexive_and_binary f g
  exact hasCoequalizers_of_hasColimit_parallelPair
    (C := C)

end CoprodCoeqTrick

section AlgFullColimits

variable {X : Type u}

instance polyAlgHasCoequalizers
    (P : PolyEndo X)
    [PolyBetweenFinitary X X P] :
    HasCoequalizers (PolyAlg P) :=
  hasCoequalizers_of_hasReflexive_and_binary

instance polyAlgHasFiniteColimits
    (P : PolyEndo X)
    [PolyBetweenFinitary X X P] :
    HasFiniteColimits (PolyAlg P) :=
  hasFiniteColimits_of_hasCoequalizers_and_finite_coproducts

instance polyAlgHasColimitsOfSize
    (P : PolyEndo X)
    [PolyBetweenFinitary X X P] :
    HasColimitsOfSize.{u, u} (PolyAlg P) := by
  haveI : HasFilteredColimitsOfSize.{u, u}
      (PolyAlg P) := ⟨fun _ _ _ => inferInstance⟩
  exact has_colimits_of_finite_and_filtered

end AlgFullColimits

end GebLean
