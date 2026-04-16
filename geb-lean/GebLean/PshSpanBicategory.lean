import GebLean.PshRelDouble
import Mathlib.CategoryTheory.Bicategory.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Cospan

open CategoryTheory Limits

namespace GebLean

universe u v w

variable {C : Type u} [Category.{v} C]

/-- The functor category of walking-span-shaped
diagrams in `PSh(C)`. Objects are span diagrams
`P ← R → Q`; morphisms are natural transformations
between such diagrams. -/
abbrev PshSpanCat (C : Type u) [Category.{v} C] :=
  WalkingSpan ⥤ (Cᵒᵖ ⥤ Type w)

/-- Wrapper type for presheaves viewed as 0-cells
of the span bicategory.  A 1-cell from `P` to `Q`
is a span `P ← R → Q` in `PSh(C)`, encoded as an
object of `Over (P × Q)`.  The distinct type avoids
conflict with the functor-category `Category` instance
on `Cᵒᵖ ⥤ Type w`. -/
@[ext]
structure PshSpanBicat
    (C : Type u) [Category.{v} C] where
  /-- The underlying presheaf. -/
  obj : Cᵒᵖ ⥤ Type w

instance pshSpanBicatCategoryStruct
    (C : Type u) [Category.{v} C] :
    CategoryStruct
      (PshSpanBicat.{u, v, w} C) where
  Hom P Q := PshProdOver P.obj Q.obj
  id P := pshProdOverId P.obj
  comp R S := pshProdOverComp R S

set_option backward.isDefEq.respectTransparency false in
/-- Left whiskering of a 2-cell by a 1-cell.
Given a span `R : P → Q` and a 2-cell `η : S₁ ⟶ S₂`
(both spans `Q → W`), produces a 2-cell
`R ; S₁ ⟶ R ; S₂` by lifting through the pullback. -/
def pshSpanWhiskerLeft
    {P Q W : Cᵒᵖ ⥤ Type w}
    (R : PshProdOver P Q)
    {S₁ S₂ : PshProdOver Q W}
    (η : S₁ ⟶ S₂) :
    pshProdOverComp R S₁ ⟶
      pshProdOverComp R S₂ :=
  Over.homMk
    (presheafPullbackLift
      (R.hom ≫ pshProdSnd P Q)
      (S₂.hom ≫ pshProdFst Q W)
      (presheafPullbackFst
        (R.hom ≫ pshProdSnd P Q)
        (S₁.hom ≫ pshProdFst Q W))
      (presheafPullbackSnd
        (R.hom ≫ pshProdSnd P Q)
        (S₁.hom ≫ pshProdFst Q W) ≫
        η.left)
      (by
        have hpb := presheafPullbackCondition
          (R.hom ≫ pshProdSnd P Q)
          (S₁.hom ≫ pshProdFst Q W)
        have hw := Over.w η
        simp only [Category.assoc] at hpb ⊢
        rw [hpb]; congr 1
        rw [← hw, Category.assoc]))
    (by
      simp only [pshProdOverComp, Over.mk_hom]
      apply pshProdPresheaf_hom_ext
      · simp only [Category.assoc,
          FunctorToTypes.prod.lift_fst,
          PullbackCone.IsLimit.lift_fst_assoc]
      · simp only [Category.assoc,
          FunctorToTypes.prod.lift_snd,
          PullbackCone.IsLimit.lift_snd_assoc]
        rw [← Over.w η]
        simp only [Category.assoc])

set_option backward.isDefEq.respectTransparency false in
/-- Right whiskering of a 2-cell by a 1-cell.
Given a 2-cell `η : R₁ ⟶ R₂` (both spans `P → Q`)
and a span `S : Q → W`, produces a 2-cell
`R₁ ; S ⟶ R₂ ; S` by lifting through the pullback. -/
def pshSpanWhiskerRight
    {P Q W : Cᵒᵖ ⥤ Type w}
    {R₁ R₂ : PshProdOver P Q}
    (η : R₁ ⟶ R₂)
    (S : PshProdOver Q W) :
    pshProdOverComp R₁ S ⟶
      pshProdOverComp R₂ S :=
  Over.homMk
    (presheafPullbackLift
      (R₂.hom ≫ pshProdSnd P Q)
      (S.hom ≫ pshProdFst Q W)
      (presheafPullbackFst
        (R₁.hom ≫ pshProdSnd P Q)
        (S.hom ≫ pshProdFst Q W) ≫
        η.left)
      (presheafPullbackSnd
        (R₁.hom ≫ pshProdSnd P Q)
        (S.hom ≫ pshProdFst Q W))
      (by
        have hpb := presheafPullbackCondition
          (R₁.hom ≫ pshProdSnd P Q)
          (S.hom ≫ pshProdFst Q W)
        have hw := Over.w η
        simp only [Category.assoc] at hpb ⊢
        rw [← hpb]; congr 1
        rw [← reassoc_of% hw]))
    (by
      simp only [pshProdOverComp, Over.mk_hom]
      apply pshProdPresheaf_hom_ext
      · simp only [Category.assoc,
          FunctorToTypes.prod.lift_fst,
          PullbackCone.IsLimit.lift_fst_assoc]
        rw [← Over.w η]
        simp only [Category.assoc]
      · simp only [Category.assoc,
          FunctorToTypes.prod.lift_snd,
          PullbackCone.IsLimit.lift_snd_assoc])

theorem pshSpanWhiskerLeft_id
    {P Q W : Cᵒᵖ ⥤ Type w}
    (R : PshProdOver P Q)
    (S : PshProdOver Q W) :
    pshSpanWhiskerLeft R (𝟙 S) =
      𝟙 (pshProdOverComp R S) := by
  apply Over.OverMorphism.ext
  apply PullbackCone.IsLimit.hom_ext
    (presheafPullbackIsLimit ..) <;>
  · dsimp [pshSpanWhiskerLeft, pshProdOverComp]
    simp [PullbackCone.IsLimit.lift_fst,
      PullbackCone.IsLimit.lift_snd]

theorem pshSpanIdWhiskerRight
    {P Q W : Cᵒᵖ ⥤ Type w}
    (R : PshProdOver P Q)
    (S : PshProdOver Q W) :
    pshSpanWhiskerRight (𝟙 R) S =
      𝟙 (pshProdOverComp R S) := by
  apply Over.OverMorphism.ext
  apply PullbackCone.IsLimit.hom_ext
    (presheafPullbackIsLimit ..) <;>
  · dsimp [pshSpanWhiskerRight, pshProdOverComp]
    simp [PullbackCone.IsLimit.lift_fst,
      PullbackCone.IsLimit.lift_snd]

theorem pshSpanWhiskerLeft_comp
    {P Q W : Cᵒᵖ ⥤ Type w}
    (R : PshProdOver P Q)
    {S₁ S₂ S₃ : PshProdOver Q W}
    (η : S₁ ⟶ S₂) (θ : S₂ ⟶ S₃) :
    pshSpanWhiskerLeft R (η ≫ θ) =
      pshSpanWhiskerLeft R η ≫
        pshSpanWhiskerLeft R θ := by
  apply Over.OverMorphism.ext
  apply PullbackCone.IsLimit.hom_ext
    (presheafPullbackIsLimit ..) <;>
  · dsimp [pshSpanWhiskerLeft, pshProdOverComp]
    simp [PullbackCone.IsLimit.lift_fst,
      PullbackCone.IsLimit.lift_snd,
      PullbackCone.IsLimit.lift_snd_assoc,
      Category.assoc]

theorem pshSpanCompWhiskerRight
    {P Q W : Cᵒᵖ ⥤ Type w}
    {R₁ R₂ R₃ : PshProdOver P Q}
    (η : R₁ ⟶ R₂) (θ : R₂ ⟶ R₃)
    (S : PshProdOver Q W) :
    pshSpanWhiskerRight (η ≫ θ) S =
      pshSpanWhiskerRight η S ≫
        pshSpanWhiskerRight θ S := by
  apply Over.OverMorphism.ext
  apply PullbackCone.IsLimit.hom_ext
    (presheafPullbackIsLimit ..) <;>
  · dsimp [pshSpanWhiskerRight, pshProdOverComp]
    simp [PullbackCone.IsLimit.lift_fst,
      PullbackCone.IsLimit.lift_snd,
      PullbackCone.IsLimit.lift_fst_assoc,
      Category.assoc]

theorem pshSpanWhiskerExchange
    {P Q W : Cᵒᵖ ⥤ Type w}
    {R₁ R₂ : PshProdOver P Q}
    {S₁ S₂ : PshProdOver Q W}
    (η : R₁ ⟶ R₂) (θ : S₁ ⟶ S₂) :
    pshSpanWhiskerLeft R₁ θ ≫
      pshSpanWhiskerRight η S₂ =
    pshSpanWhiskerRight η S₁ ≫
      pshSpanWhiskerLeft R₂ θ := by
  apply Over.OverMorphism.ext
  apply PullbackCone.IsLimit.hom_ext
    (presheafPullbackIsLimit ..) <;>
  · dsimp [pshSpanWhiskerLeft,
      pshSpanWhiskerRight, pshProdOverComp]
    simp [PullbackCone.IsLimit.lift_fst,
      PullbackCone.IsLimit.lift_snd,
      PullbackCone.IsLimit.lift_fst_assoc,
      PullbackCone.IsLimit.lift_snd_assoc,
      Category.assoc]

set_option backward.isDefEq.respectTransparency false in
theorem pshSpanIdWhiskerLeft
    {P Q : Cᵒᵖ ⥤ Type w}
    {R₁ R₂ : PshProdOver P Q}
    (η : R₁ ⟶ R₂) :
    pshSpanWhiskerLeft (pshProdOverId P) η =
      (pshProdOverComp_id_left R₁).hom ≫ η ≫
        (pshProdOverComp_id_left R₂).inv := by
  apply Over.OverMorphism.ext
  apply PullbackCone.IsLimit.hom_ext
    (presheafPullbackIsLimit ..)
  · dsimp [pshSpanWhiskerLeft, pshProdOverComp,
      pshProdOverComp_id_left,
      presheafPullbackIdLeftIso]
    simp only [Category.assoc,
      PullbackCone.IsLimit.lift_fst]
    have h := presheafPullbackCondition
      (𝟙 P) (R₁.hom ≫ pshProdFst P Q)
    simp only [Category.comp_id] at h
    rw [reassoc_of% (Over.w η)]
    exact h
  · dsimp [pshSpanWhiskerLeft, pshProdOverComp,
      pshProdOverComp_id_left,
      presheafPullbackIdLeftIso]
    simp only [Category.assoc,
      PullbackCone.IsLimit.lift_snd,
      Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
theorem pshSpanWhiskerRightId
    {P Q : Cᵒᵖ ⥤ Type w}
    {R₁ R₂ : PshProdOver P Q}
    (η : R₁ ⟶ R₂) :
    pshSpanWhiskerRight η (pshProdOverId Q) =
      (pshProdOverComp_id_right R₁).hom ≫ η ≫
        (pshProdOverComp_id_right R₂).inv := by
  apply Over.OverMorphism.ext
  apply PullbackCone.IsLimit.hom_ext
    (presheafPullbackIsLimit ..)
  · dsimp [pshSpanWhiskerRight, pshProdOverComp,
      pshProdOverComp_id_right,
      presheafPullbackIdRightIso]
    simp only [Category.assoc,
      PullbackCone.IsLimit.lift_fst,
      Category.comp_id]
  · dsimp [pshSpanWhiskerRight, pshProdOverComp,
      pshProdOverComp_id_right,
      presheafPullbackIdRightIso]
    simp only [Category.assoc,
      PullbackCone.IsLimit.lift_snd]
    have h := presheafPullbackCondition
      (R₁.hom ≫ pshProdSnd P Q) (𝟙 Q)
    simp only [Category.comp_id] at h
    rw [reassoc_of% (Over.w η)]
    exact h.symm

theorem pshSpanCompWhiskerLeft
    {P Q W X : Cᵒᵖ ⥤ Type w}
    (R : PshProdOver P Q)
    (S : PshProdOver Q W)
    {T₁ T₂ : PshProdOver W X}
    (η : T₁ ⟶ T₂) :
    pshSpanWhiskerLeft (pshProdOverComp R S) η =
      (pshProdOverComp_assoc R S T₁).hom ≫
        pshSpanWhiskerLeft R
          (pshSpanWhiskerLeft S η) ≫
        (pshProdOverComp_assoc R S T₂).inv := by
  apply Over.OverMorphism.ext
  dsimp [pshSpanWhiskerLeft, pshProdOverComp,
    pshProdOverComp_assoc, presheafPullbackAssocIso]
  apply PullbackCone.IsLimit.hom_ext
    (presheafPullbackIsLimit ..)
  · apply PullbackCone.IsLimit.hom_ext
      (presheafPullbackIsLimit ..) <;>
    simp [presheafPullbackLift]
  · simp [presheafPullbackLift]

theorem pshSpanWhiskerRightComp
    {P Q W X : Cᵒᵖ ⥤ Type w}
    {R₁ R₂ : PshProdOver P Q}
    (η : R₁ ⟶ R₂)
    (S : PshProdOver Q W)
    (T : PshProdOver W X) :
    pshSpanWhiskerRight η (pshProdOverComp S T) =
      (pshProdOverComp_assoc R₁ S T).inv ≫
        pshSpanWhiskerRight
          (pshSpanWhiskerRight η S) T ≫
        (pshProdOverComp_assoc R₂ S T).hom := by
  apply Over.OverMorphism.ext
  dsimp [pshSpanWhiskerRight, pshProdOverComp,
    pshProdOverComp_assoc, presheafPullbackAssocIso]
  apply PullbackCone.IsLimit.hom_ext
    (presheafPullbackIsLimit ..)
  · simp [presheafPullbackLift]
  · apply PullbackCone.IsLimit.hom_ext
      (presheafPullbackIsLimit ..) <;>
    simp [presheafPullbackLift]

theorem pshSpanWhiskerAssoc
    {P Q W X : Cᵒᵖ ⥤ Type w}
    (R : PshProdOver P Q)
    {S₁ S₂ : PshProdOver Q W}
    (η : S₁ ⟶ S₂)
    (T : PshProdOver W X) :
    pshSpanWhiskerRight
      (pshSpanWhiskerLeft R η) T =
      (pshProdOverComp_assoc R S₁ T).hom ≫
        pshSpanWhiskerLeft R
          (pshSpanWhiskerRight η T) ≫
        (pshProdOverComp_assoc R S₂ T).inv := by
  apply Over.OverMorphism.ext
  dsimp [pshSpanWhiskerLeft, pshSpanWhiskerRight,
    pshProdOverComp,
    pshProdOverComp_assoc, presheafPullbackAssocIso]
  apply PullbackCone.IsLimit.hom_ext
    (presheafPullbackIsLimit ..)
  · apply PullbackCone.IsLimit.hom_ext
      (presheafPullbackIsLimit ..) <;>
    simp [presheafPullbackLift]
  · simp [presheafPullbackLift]

theorem pshSpanPentagon
    {P Q W X Y : Cᵒᵖ ⥤ Type w}
    (R : PshProdOver P Q)
    (S : PshProdOver Q W)
    (T : PshProdOver W X)
    (U : PshProdOver X Y) :
    pshSpanWhiskerRight
      (pshProdOverComp_assoc R S T).hom U ≫
      (pshProdOverComp_assoc R
        (pshProdOverComp S T) U).hom ≫
      pshSpanWhiskerLeft R
        (pshProdOverComp_assoc S T U).hom =
    (pshProdOverComp_assoc
      (pshProdOverComp R S) T U).hom ≫
    (pshProdOverComp_assoc R S
      (pshProdOverComp T U)).hom := by
  apply Over.OverMorphism.ext
  dsimp [pshSpanWhiskerLeft, pshSpanWhiskerRight,
    pshProdOverComp,
    pshProdOverComp_assoc, presheafPullbackAssocIso]
  apply PullbackCone.IsLimit.hom_ext
    (presheafPullbackIsLimit ..)
  · simp [presheafPullbackLift]
  · apply PullbackCone.IsLimit.hom_ext
      (presheafPullbackIsLimit ..)
    · simp [presheafPullbackLift]
    · apply PullbackCone.IsLimit.hom_ext
        (presheafPullbackIsLimit ..) <;>
      simp [presheafPullbackLift]

theorem pshSpanTriangle
    {P Q W : Cᵒᵖ ⥤ Type w}
    (R : PshProdOver P Q)
    (S : PshProdOver Q W) :
    (pshProdOverComp_assoc R
      (pshProdOverId Q) S).hom ≫
      pshSpanWhiskerLeft R
        (pshProdOverComp_id_left S).hom =
    pshSpanWhiskerRight
      (pshProdOverComp_id_right R).hom S := by
  apply Over.OverMorphism.ext
  dsimp [pshSpanWhiskerLeft, pshSpanWhiskerRight,
    pshProdOverComp, pshProdOverId,
    pshProdOverComp_assoc, presheafPullbackAssocIso,
    pshProdOverComp_id_left,
    presheafPullbackIdLeftIso,
    pshProdOverComp_id_right,
    presheafPullbackIdRightIso]
  apply PullbackCone.IsLimit.hom_ext
    (presheafPullbackIsLimit ..) <;>
  simp [presheafPullbackLift]

instance pshSpanBicategory
    (C : Type u) [Category.{v} C] :
    Bicategory
      (PshSpanBicat.{u, v, w} C) where
  homCategory a b :=
    show Category (PshProdOver a.obj b.obj)
      from inferInstance
  whiskerLeft {_ _ _} R {_ _} η :=
    pshSpanWhiskerLeft R η
  whiskerRight {_ _ _} {_ _} η S :=
    pshSpanWhiskerRight η S
  associator {_ _ _ _} R S T :=
    pshProdOverComp_assoc R S T
  leftUnitor {_ _} R :=
    pshProdOverComp_id_left R
  rightUnitor {_ _} R :=
    pshProdOverComp_id_right R
  whiskerLeft_id {_ _ _} R S :=
    pshSpanWhiskerLeft_id R S
  whiskerLeft_comp {_ _ _} R {_ _ _} η θ :=
    pshSpanWhiskerLeft_comp R η θ
  id_whiskerLeft {_ _} {_ _} η :=
    pshSpanIdWhiskerLeft η
  id_whiskerRight {_ _ _} R S :=
    pshSpanIdWhiskerRight R S
  comp_whiskerRight {_ _ _} {_ _ _} η θ S :=
    pshSpanCompWhiskerRight η θ S
  whiskerRight_id {_ _} {_ _} η :=
    pshSpanWhiskerRightId η
  whisker_exchange {_ _ _} {_ _} {_ _} η θ :=
    pshSpanWhiskerExchange η θ
  comp_whiskerLeft {_ _ _ _} R S {_ _} η :=
    pshSpanCompWhiskerLeft R S η
  whiskerRight_comp {_ _ _ _} {_ _} η S T :=
    pshSpanWhiskerRightComp η S T
  whisker_assoc {_ _ _ _} R {_ _} η S :=
    pshSpanWhiskerAssoc R η S
  pentagon {_ _ _ _ _} R S T U :=
    pshSpanPentagon R S T U
  triangle {_ _ _} R S :=
    pshSpanTriangle R S

end GebLean
