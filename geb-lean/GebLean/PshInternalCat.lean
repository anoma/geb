import GebLean.PshSpanBicategory
import Mathlib.CategoryTheory.Bicategory.End
import Mathlib.CategoryTheory.Monoidal.Mon_

open CategoryTheory Limits

namespace GebLean

universe u v w

variable {C : Type u} [Category.{v} C]

/-- An internal category in presheaves over `C`,
defined as a monoid object in the endomorphism
monoidal category of the span bicategory of
presheaves.  The object `objs` is the
presheaf of objects; the monoid `cat` bundles
the endomorphism span (presheaf of morphisms
with source and target projections) together
with identity and composition 2-cells satisfying
the category axioms. -/
structure PshInternalCat
    (C : Type u) [Category.{v} C] where
  /-- The object-of-objects presheaf. -/
  objs : PshSpanBicat.{u, v, w} C
  /-- The endomorphism span with monoid structure:
  the object of morphisms, source/target maps,
  identity assignment, and composition. -/
  cat : Mon (EndMonoidal objs)

variable (X : PshInternalCat.{u, v, w} C)

/-- The presheaf of objects of an internal
category. -/
abbrev PshInternalCat.objPresheaf :
    Cᵒᵖ ⥤ Type w :=
  X.objs.obj

/-- The endomorphism span encoding the morphism
structure: an object of
`Over (X.objPresheaf × X.objPresheaf)`. -/
abbrev PshInternalCat.morSpan :
    PshProdOver X.objPresheaf X.objPresheaf :=
  X.cat.X

/-- The presheaf of morphisms of an internal
category (the apex of the span). -/
abbrev PshInternalCat.morPresheaf :
    Cᵒᵖ ⥤ Type w :=
  X.morSpan.left

/-- The source map: the composite of the span
map with the first projection. -/
abbrev PshInternalCat.src :
    X.morPresheaf ⟶ X.objPresheaf :=
  X.morSpan.hom ≫ pshProdFst _ _

/-- The target map: the composite of the span
map with the second projection. -/
abbrev PshInternalCat.tgt :
    X.morPresheaf ⟶ X.objPresheaf :=
  X.morSpan.hom ≫ pshProdSnd _ _

/-- The identity assignment map of an internal
category, extracted from the monoid unit. -/
abbrev PshInternalCat.idMap :
    X.objPresheaf ⟶ X.morPresheaf :=
  (MonObj.one (X := X.cat.X)).left

/-- The composition map of an internal category,
extracted from the monoid multiplication.  The
domain is the presheaf of composable pairs
(the pullback of target with source). -/
abbrev PshInternalCat.compMap :
    (pshProdOverComp X.morSpan X.morSpan).left ⟶
      X.morPresheaf :=
  (MonObj.mul (X := X.cat.X)).left

variable {X}

set_option backward.isDefEq.respectTransparency false in
/-- Given maps `F₀` on objects and `F₁` on
morphisms satisfying source/target compatibility,
the induced map on composable pairs: applies `F₁`
to each component of a composable pair in `X` to
obtain a composable pair in `Y`. -/
def pshInternalCompPairsMap
    {Y : PshInternalCat.{u, v, w} C}
    (F₀ : X.objPresheaf ⟶ Y.objPresheaf)
    (F₁ : X.morPresheaf ⟶ Y.morPresheaf)
    (compat : F₁ ≫ Y.morSpan.hom =
      X.morSpan.hom ≫ pshProdMap F₀ F₀) :
    (pshProdOverComp X.morSpan X.morSpan).left ⟶
      (pshProdOverComp Y.morSpan Y.morSpan).left :=
  presheafPullbackLift
    (Y.morSpan.hom ≫ pshProdSnd _ _)
    (Y.morSpan.hom ≫ pshProdFst _ _)
    (presheafPullbackFst
      (X.morSpan.hom ≫ pshProdSnd _ _)
      (X.morSpan.hom ≫ pshProdFst _ _) ≫ F₁)
    (presheafPullbackSnd
      (X.morSpan.hom ≫ pshProdSnd _ _)
      (X.morSpan.hom ≫ pshProdFst _ _) ≫ F₁)
    (by
      simp only [Category.assoc,
        reassoc_of% compat,
        pshProdMap_snd, pshProdMap_fst]
      simp only [← Category.assoc]
      congr 1
      simp only [Category.assoc,
        presheafPullbackCondition])

/-- An internal functor between internal
categories in presheaves.  Consists of a map on
object presheaves, a map on morphism presheaves
compatible with source/target, and preservation
of identities and composition. -/
structure PshInternalFunctor
    (X Y : PshInternalCat.{u, v, w} C) where
  /-- The map on object presheaves. -/
  objMap : X.objPresheaf ⟶ Y.objPresheaf
  /-- The map on morphism presheaves. -/
  morMap : X.morPresheaf ⟶ Y.morPresheaf
  /-- Source/target compatibility: the morphism
  map commutes with the span projections through
  `objMap`. -/
  compat :
    morMap ≫ Y.morSpan.hom =
      X.morSpan.hom ≫ pshProdMap objMap objMap
  /-- Preservation of identities: applying
  the morphism map to an identity gives an
  identity. -/
  id_pres :
    X.idMap ≫ morMap = objMap ≫ Y.idMap
  /-- Preservation of composition: the morphism
  map commutes with the composition maps through
  the induced map on composable pairs. -/
  comp_pres :
    X.compMap ≫ morMap =
      pshInternalCompPairsMap objMap morMap compat
        ≫ Y.compMap

set_option backward.isDefEq.respectTransparency false in
/-- The composable-pairs map for the identity
morphism data is itself the identity. -/
theorem pshInternalCompPairsMap_id
    (X : PshInternalCat.{u, v, w} C)
    (h : (𝟙 X.morPresheaf) ≫ X.morSpan.hom =
      X.morSpan.hom ≫
        pshProdMap (𝟙 X.objPresheaf)
          (𝟙 X.objPresheaf)) :
    pshInternalCompPairsMap
      (𝟙 X.objPresheaf) (𝟙 X.morPresheaf) h =
      𝟙 _ := by
  apply PullbackCone.IsLimit.hom_ext
    (presheafPullbackIsLimit _ _)
  · simp [pshInternalCompPairsMap,
      presheafPullbackLift, presheafPullbackFst]
  · simp [pshInternalCompPairsMap,
      presheafPullbackLift, presheafPullbackSnd]

set_option backward.isDefEq.respectTransparency false in
/-- Composing composable-pairs maps corresponds
to composing the underlying morphism maps. -/
theorem pshInternalCompPairsMap_comp
    {Y Z : PshInternalCat.{u, v, w} C}
    (F₀ : X.objPresheaf ⟶ Y.objPresheaf)
    (F₁ : X.morPresheaf ⟶ Y.morPresheaf)
    (hF : F₁ ≫ Y.morSpan.hom =
      X.morSpan.hom ≫ pshProdMap F₀ F₀)
    (G₀ : Y.objPresheaf ⟶ Z.objPresheaf)
    (G₁ : Y.morPresheaf ⟶ Z.morPresheaf)
    (hG : G₁ ≫ Z.morSpan.hom =
      Y.morSpan.hom ≫ pshProdMap G₀ G₀)
    (hFG : (F₁ ≫ G₁) ≫ Z.morSpan.hom =
      X.morSpan.hom ≫
        pshProdMap (F₀ ≫ G₀) (F₀ ≫ G₀)) :
    pshInternalCompPairsMap (F₀ ≫ G₀)
        (F₁ ≫ G₁) hFG =
      pshInternalCompPairsMap F₀ F₁ hF ≫
        pshInternalCompPairsMap G₀ G₁ hG := by
  apply PullbackCone.IsLimit.hom_ext
    (presheafPullbackIsLimit _ _)
  · simp [pshInternalCompPairsMap,
      presheafPullbackLift, presheafPullbackFst]
  · simp [pshInternalCompPairsMap,
      presheafPullbackLift, presheafPullbackSnd]

/-- The identity internal functor. -/
def PshInternalFunctor.id
    (X : PshInternalCat.{u, v, w} C) :
    PshInternalFunctor X X where
  objMap := 𝟙 _
  morMap := 𝟙 _
  compat := by simp [pshProdMap_id]
  id_pres := by simp
  comp_pres := by
    simp only [PshInternalCat.compMap,
      Category.comp_id,
      pshInternalCompPairsMap_id,
      Category.id_comp]

set_option backward.isDefEq.respectTransparency false in
/-- Composition of internal functors. -/
def PshInternalFunctor.comp
    {X Y Z : PshInternalCat.{u, v, w} C}
    (F : PshInternalFunctor X Y)
    (G : PshInternalFunctor Y Z) :
    PshInternalFunctor X Z where
  objMap := F.objMap ≫ G.objMap
  morMap := F.morMap ≫ G.morMap
  compat := by
    rw [Category.assoc, G.compat,
      ← Category.assoc, F.compat, Category.assoc,
      ← pshProdMap_comp]
  id_pres := by
    rw [← Category.assoc, F.id_pres,
      Category.assoc, G.id_pres,
      ← Category.assoc]
  comp_pres := by
    rw [← Category.assoc, F.comp_pres,
      Category.assoc, G.comp_pres,
      ← Category.assoc,
      pshInternalCompPairsMap_comp]

@[ext]
theorem PshInternalFunctor.ext'
    {X Y : PshInternalCat.{u, v, w} C}
    {F G : PshInternalFunctor X Y}
    (h₀ : F.objMap = G.objMap)
    (h₁ : F.morMap = G.morMap) : F = G := by
  cases F; cases G
  simp only [mk.injEq] at *
  exact ⟨h₀, h₁⟩

instance pshInternalCatCategory
    (C : Type u) [Category.{v} C] :
    Category
      (PshInternalCat.{u, v, w} C) where
  Hom := PshInternalFunctor
  id := PshInternalFunctor.id
  comp := PshInternalFunctor.comp
  id_comp F := by
    apply PshInternalFunctor.ext' <;> simp [
      PshInternalFunctor.comp,
      PshInternalFunctor.id]
  comp_id F := by
    apply PshInternalFunctor.ext' <;> simp [
      PshInternalFunctor.comp,
      PshInternalFunctor.id]
  assoc F G H := by
    apply PshInternalFunctor.ext' <;> simp [
      PshInternalFunctor.comp]

section DiscreteUnitEquiv

open Functor

universe w'

/-- The constant presheaf over `Discrete Unit`
at a type `α`. -/
abbrev constPsh (α : Type w') :
    (Discrete Unit)ᵒᵖ ⥤ Type w' :=
  (const (Discrete Unit)ᵒᵖ).obj α

/-- A natural transformation between constant
presheaves over `Discrete Unit` is determined
by a function between the underlying types. -/
abbrev constPshMap {α β : Type w'} (f : α → β) :
    constPsh α ⟶ constPsh β :=
  (const (Discrete Unit)ᵒᵖ).map (TypeCat.ofHom f)

/-- The type of morphisms of a category, bundled
with source and target: `Σ (a b : α), (a ⟶ b)`. -/
abbrev CatMorSigma (α : Type w') [Category.{w'} α] :
    Type w' :=
  Σ (a b : α), (a ⟶ b)

/-- The source-target pairing for a category's
morphisms, as a function to the product type. -/
abbrev catMorSrcTgt (α : Type w')
    [Category.{w'} α] :
    CatMorSigma α → α × α :=
  fun ⟨a, b, _⟩ => (a, b)

/-- The source-target pairing as a natural
transformation to the product presheaf. -/
abbrev catMorSrcTgtNat (α : Type w')
    [Category.{w'} α] :
    constPsh (CatMorSigma α) ⟶
      pshProdPresheaf (constPsh α)
        (constPsh α) :=
  pshProdLift
    (constPshMap (fun m => m.1))
    (constPshMap (fun m => m.2.1))

/-- The morphism span of a category as a
`PshProdOver` in presheaves over
`Discrete Unit`. -/
abbrev catMorSpanOver (α : Type w')
    [Category.{w'} α] :
    PshProdOver
      (constPsh α) (constPsh α) :=
  Over.mk (catMorSrcTgtNat α)

/-- The identity assignment as a morphism of
spans: from the identity span to the morphism
span.  Sends `a` to `⟨a, a, 𝟙 a⟩`. -/
def catIdentitySpanMor (α : Type w')
    [Category.{w'} α] :
    pshProdOverId (constPsh α) ⟶
      catMorSpanOver α :=
  Over.homMk
    (constPshMap (fun (a : α) =>
      (⟨a, a, 𝟙 a⟩ : CatMorSigma α)))
    (by
      simp only [pshProdOverId,
        catMorSpanOver, catMorSrcTgtNat]
      apply pshProdPresheaf_hom_ext
      · ext; simp [constPshMap, constPsh]
      · ext; simp [constPshMap, constPsh])

/-- The target map on morphism sigmas, as a
natural transformation. -/
abbrev catMorTgt (α : Type w')
    [Category.{w'} α] :
    constPsh (CatMorSigma α) ⟶ constPsh α :=
  catMorSrcTgtNat α ≫
    pshProdSnd (constPsh α) (constPsh α)

/-- The source map on morphism sigmas, as a
natural transformation. -/
abbrev catMorSrc (α : Type w')
    [Category.{w'} α] :
    constPsh (CatMorSigma α) ⟶ constPsh α :=
  catMorSrcTgtNat α ≫
    pshProdFst (constPsh α) (constPsh α)

/-- The composition map as a natural transformation
from the composable-pairs pullback to the morphism
presheaf.  Extracts the two morphisms via the
pullback projections and composes them using the
pullback condition (target = source). -/
def catCompNat (α : Type w') [Category.{w'} α] :
    (pshProdOverComp (catMorSpanOver α)
      (catMorSpanOver α)).left ⟶
      constPsh (CatMorSigma α) where
  app X := TypeCat.ofHom fun p =>
    let m₁ := (presheafPullbackFst
      (catMorTgt α) (catMorSrc α)).app X p
    let m₂ := (presheafPullbackSnd
      (catMorTgt α) (catMorSrc α)).app X p
    have h : m₁.2.1 = m₂.1 := by
      have hh := ConcreteCategory.congr_hom
        (NatTrans.congr_app
          (presheafPullbackCondition
            (catMorTgt α) (catMorSrc α)) X) p
      simp only [NatTrans.comp_app,
        ConcreteCategory.comp_apply] at hh
      exact hh
    ⟨m₁.1, m₂.2.1,
      m₁.2.2 ≫ eqToHom h ≫ m₂.2.2⟩
  naturality := by
    intro X Y f
    have hXY : X = Y := Subsingleton.elim _ _
    subst hXY
    have hf : f = 𝟙 _ := Subsingleton.elim _ _
    subst hf; simp

/-- The composition span morphism: from the
composable-pairs span to the morphism span.
Sends a composable pair `(f, g)` with matching
target/source to `f ≫ g`. -/
def catCompSpanMor (α : Type w')
    [Category.{w'} α] :
    pshProdOverComp (catMorSpanOver α)
      (catMorSpanOver α) ⟶
      catMorSpanOver α :=
  Over.homMk (catCompNat α) (by
    simp only [pshProdOverComp,
      catMorSpanOver, Over.mk_hom]
    apply pshProdPresheaf_hom_ext
    · ext ⟨⟨⟩⟩ p
      rfl
    · ext ⟨⟨⟩⟩ p
      rfl)

set_option backward.isDefEq.respectTransparency false in
/-- The monoid-object structure on the morphism
span: identity and composition satisfying the
category axioms. -/
instance catMonObj (α : Type w')
    [Category.{w'} α] :
    @MonObj
      (EndMonoidal
        (⟨constPsh α⟩ : PshSpanBicat.{0, 0, w'}
          (Discrete Unit)))
      _
      (inferInstance : MonoidalCategory
        (EndMonoidal
          (⟨constPsh α⟩ :
            PshSpanBicat.{0, 0, w'}
              (Discrete Unit))))
      (catMorSpanOver α) where
  one := catIdentitySpanMor α
  mul := catCompSpanMor α
  one_mul := by
    change pshSpanWhiskerRight
      (catIdentitySpanMor α)
      (catMorSpanOver α) ≫
      catCompSpanMor α =
      (pshProdOverComp_id_left
        (catMorSpanOver α)).hom
    apply Over.OverMorphism.ext
    ext ⟨⟨⟩⟩ p
    simp only [Over.comp_left,
      NatTrans.comp_app,
      Over.homMk_left, Over.isoMk_hom_left,
      pshSpanWhiskerRight,
      catCompSpanMor,
      catIdentitySpanMor,
      pshProdOverComp_id_left,
      presheafPullbackIdLeftIso,
      pshProdOverId_snd]
    obtain ⟨⟨a, ⟨b, c, f⟩⟩, hab⟩ := p
    dsimp [pshProdOverId, constPsh, constPshMap,
      catMorSpanOver, catMorSrcTgtNat,
      pshProdLift, pshProdFst, pshProdSnd]
      at a hab ⊢
    subst hab
    change (⟨_, _, 𝟙 a ≫ eqToHom rfl ≫ f⟩ :
      CatMorSigma α) = ⟨a, c, f⟩
    simp only [eqToHom_refl, Category.id_comp]
  mul_one := by
    change pshSpanWhiskerLeft
      (catMorSpanOver α)
      (catIdentitySpanMor α) ≫
      catCompSpanMor α =
      (pshProdOverComp_id_right
        (catMorSpanOver α)).hom
    apply Over.OverMorphism.ext
    ext ⟨⟨⟩⟩ p
    simp only [Over.comp_left,
      NatTrans.comp_app,
      Over.homMk_left, Over.isoMk_hom_left,
      pshSpanWhiskerLeft,
      catCompSpanMor,
      catIdentitySpanMor,
      pshProdOverComp_id_right,
      presheafPullbackIdRightIso,
      pshProdOverId_fst]
    obtain ⟨⟨⟨a, b, f⟩, c⟩, hbc⟩ := p
    dsimp [pshProdOverId, constPsh, constPshMap,
      catMorSpanOver, catMorSrcTgtNat,
      pshProdLift, pshProdFst, pshProdSnd]
      at c hbc ⊢
    subst hbc
    change (⟨_, _, f ≫ eqToHom rfl ≫ 𝟙 b⟩ :
      CatMorSigma α) = ⟨a, b, f⟩
    simp only [eqToHom_refl, Category.comp_id]
  mul_assoc := by
    change pshSpanWhiskerRight
      (catCompSpanMor α)
      (catMorSpanOver α) ≫
      catCompSpanMor α =
      (pshProdOverComp_assoc
        (catMorSpanOver α)
        (catMorSpanOver α)
        (catMorSpanOver α)).hom ≫
      pshSpanWhiskerLeft
        (catMorSpanOver α)
        (catCompSpanMor α) ≫
      catCompSpanMor α
    apply Over.OverMorphism.ext
    ext ⟨⟨⟩⟩ p
    simp only [Over.comp_left,
      NatTrans.comp_app,
      Over.homMk_left, Over.isoMk_hom_left,
      pshSpanWhiskerRight,
      pshSpanWhiskerLeft,
      catCompSpanMor,
      pshProdOverComp_assoc,
      presheafPullbackAssocIso]
    obtain ⟨⟨inner, ⟨d, e, h⟩⟩, hde⟩ := p
    obtain ⟨⟨⟨a, b, f⟩, ⟨c, c', g⟩⟩,
      hbc⟩ := inner
    dsimp [pshProdOverComp, pshProdOverId,
      constPsh, constPshMap,
      catMorSpanOver, catMorSrcTgtNat,
      pshProdLift, pshProdFst, pshProdSnd]
      at c' e hbc hde ⊢
    subst hbc; subst hde
    change
      (⟨a, e,
        (f ≫ 𝟙 b ≫ g) ≫ 𝟙 c' ≫ h⟩ :
        CatMorSigma α) =
      ⟨a, e, f ≫ 𝟙 b ≫ (g ≫ 𝟙 c' ≫ h)⟩
    simp only [Category.id_comp,
      Category.assoc]

/-- The internal category in presheaves over
`Discrete Unit` corresponding to a category
`α`.  The presheaf of objects is the constant
presheaf at `α`, and the monoid object encodes
morphisms with composition and identity. -/
def catToPshInternalCat (α : Type w')
    [Category.{w'} α] :
    PshInternalCat.{0, 0, w'}
      (Discrete Unit) where
  objs := ⟨constPsh α⟩
  cat := Mon.mk (catMorSpanOver α)

variable
    (X : PshInternalCat.{0, 0, w'}
      (Discrete Unit))

/-- The type of objects of an internal category
over `Discrete Unit`, evaluated at the unique
object. -/
abbrev icObj :=
  X.objPresheaf.obj (Opposite.op ⟨⟨⟩⟩)

/-- The type of all morphisms of an internal
category over `Discrete Unit`, evaluated at the
unique object. -/
abbrev icAllMor :=
  X.morPresheaf.obj (Opposite.op ⟨⟨⟩⟩)

/-- The source function at the unique object. -/
abbrev icSrcFn : icAllMor X → icObj X :=
  X.src.app (Opposite.op ⟨⟨⟩⟩)

/-- The target function at the unique object. -/
abbrev icTgtFn : icAllMor X → icObj X :=
  X.tgt.app (Opposite.op ⟨⟨⟩⟩)

/-- The hom-type of an internal category over
`Discrete Unit`: morphisms with specified source
and target. -/
def icHom (a b : icObj X) : Type w' :=
  { m : icAllMor X //
    icSrcFn X m = a ∧ icTgtFn X m = b }

/-- The identity morphism assignment of an
internal category over `Discrete Unit`,
evaluated at the unique object. -/
abbrev icIdFn : icObj X → icAllMor X :=
  X.idMap.app (Opposite.op ⟨⟨⟩⟩)

/-- Composing the identity assignment with the
source map yields the identity: `src ∘ id = 𝟙`.
Follows from the `Over.w` condition of
`MonObj.one`. -/
theorem icIdMap_src :
    X.idMap ≫ X.src = 𝟙 X.objPresheaf := by
  change (MonObj.one (X := X.cat.X)).left ≫
    X.morSpan.hom ≫ pshProdFst _ _ = 𝟙 _
  rw [← Category.assoc,
    Over.w (MonObj.one (X := X.cat.X))]
  change pshProdLift (𝟙 X.objPresheaf)
    (𝟙 X.objPresheaf) ≫ pshProdFst _ _ =
    𝟙 X.objPresheaf
  simp [pshProdLift]

/-- Composing the identity assignment with the
target map yields the identity: `tgt ∘ id = 𝟙`.
Follows from the `Over.w` condition of
`MonObj.one`. -/
theorem icIdMap_tgt :
    X.idMap ≫ X.tgt = 𝟙 X.objPresheaf := by
  change (MonObj.one (X := X.cat.X)).left ≫
    X.morSpan.hom ≫ pshProdSnd _ _ = 𝟙 _
  rw [← Category.assoc,
    Over.w (MonObj.one (X := X.cat.X))]
  change pshProdLift (𝟙 X.objPresheaf)
    (𝟙 X.objPresheaf) ≫ pshProdSnd _ _ =
    𝟙 X.objPresheaf
  simp [pshProdLift]

/-- The source of the identity morphism is the
object itself. -/
theorem icSrc_id (a : icObj X) :
    icSrcFn X (icIdFn X a) = a :=
  ConcreteCategory.congr_hom (NatTrans.congr_app
    (icIdMap_src X) (Opposite.op ⟨⟨⟩⟩)) a

/-- The target of the identity morphism is the
object itself. -/
theorem icTgt_id (a : icObj X) :
    icTgtFn X (icIdFn X a) = a :=
  ConcreteCategory.congr_hom (NatTrans.congr_app
    (icIdMap_tgt X) (Opposite.op ⟨⟨⟩⟩)) a

/-- The identity element of `icHom`. -/
def icId (a : icObj X) : icHom X a a :=
  ⟨icIdFn X a, ⟨icSrc_id X a, icTgt_id X a⟩⟩

/-- The composable-pairs presheaf of the internal
category, evaluated at the unique object. -/
abbrev icCompPairs :=
  (pshProdOverComp X.morSpan X.morSpan).left.obj
    (Opposite.op ⟨⟨⟩⟩)

/-- Given composable morphisms `f : a ⟶ b` and
`g : b ⟶ c`, construct the composable pair as an
element of the pullback presheaf. -/
def icMkCompPair {a b c : icObj X}
    (f : icHom X a b) (g : icHom X b c) :
    icCompPairs X :=
  ⟨⟨f.val, g.val⟩, f.2.2.trans g.2.1.symm⟩

/-- Apply the composition map to a composable
pair. -/
abbrev icCompApply (p : icCompPairs X) :
    icAllMor X :=
  X.compMap.app (Opposite.op ⟨⟨⟩⟩) p

set_option backward.isDefEq.respectTransparency false in
/-- The source of a composite equals the source
of the first morphism. -/
theorem icCompMap_src :
    X.compMap ≫ X.src =
      presheafPullbackFst X.tgt X.src ≫
        X.src := by
  change (MonObj.mul (X := X.cat.X)).left ≫
    X.morSpan.hom ≫ pshProdFst _ _ =
    presheafPullbackFst X.tgt X.src ≫
      X.morSpan.hom ≫ pshProdFst _ _
  rw [← Category.assoc,
    Over.w (MonObj.mul (X := X.cat.X))]
  change pshProdLift
    (presheafPullbackFst X.tgt X.src ≫ X.src)
    (presheafPullbackSnd X.tgt X.src ≫ X.tgt) ≫
    pshProdFst _ _ =
    presheafPullbackFst X.tgt X.src ≫
      X.morSpan.hom ≫ pshProdFst _ _
  simp [pshProdLift]

set_option backward.isDefEq.respectTransparency false in
/-- The target of a composite equals the target
of the second morphism. -/
theorem icCompMap_tgt :
    X.compMap ≫ X.tgt =
      presheafPullbackSnd X.tgt X.src ≫
        X.tgt := by
  change (MonObj.mul (X := X.cat.X)).left ≫
    X.morSpan.hom ≫ pshProdSnd _ _ =
    presheafPullbackSnd X.tgt X.src ≫
      X.morSpan.hom ≫ pshProdSnd _ _
  rw [← Category.assoc,
    Over.w (MonObj.mul (X := X.cat.X))]
  change pshProdLift
    (presheafPullbackFst X.tgt X.src ≫ X.src)
    (presheafPullbackSnd X.tgt X.src ≫ X.tgt) ≫
    pshProdSnd _ _ =
    presheafPullbackSnd X.tgt X.src ≫
      X.morSpan.hom ≫ pshProdSnd _ _
  simp [pshProdLift]

/-- Pointwise: the source of a composite equals
the source of the first morphism. -/
theorem icSrc_comp (p : icCompPairs X) :
    icSrcFn X (icCompApply X p) =
      icSrcFn X p.val.1 :=
  ConcreteCategory.congr_hom (NatTrans.congr_app
    (icCompMap_src X) (Opposite.op ⟨⟨⟩⟩)) p

/-- Pointwise: the target of a composite equals
the target of the second morphism. -/
theorem icTgt_comp (p : icCompPairs X) :
    icTgtFn X (icCompApply X p) =
      icTgtFn X p.val.2 :=
  ConcreteCategory.congr_hom (NatTrans.congr_app
    (icCompMap_tgt X) (Opposite.op ⟨⟨⟩⟩)) p

/-- Composition of morphisms in the internal
category. -/
def icComp {a b c : icObj X}
    (f : icHom X a b) (g : icHom X b c) :
    icHom X a c :=
  ⟨icCompApply X (icMkCompPair X f g),
    ⟨(icSrc_comp X (icMkCompPair X f g)).trans
       f.2.1,
     (icTgt_comp X (icMkCompPair X f g)).trans
       g.2.2⟩⟩

/-- Extensionality for `icHom`: two morphisms
are equal iff their underlying elements are. -/
theorem icHom_ext {a b : icObj X}
    {f g : icHom X a b}
    (h : f.val = g.val) : f = g :=
  Subtype.ext h

/-- Left identity: `id ≫ f = f`. Extracted
pointwise from `MonObj.one_mul`. -/
theorem icComp_id_left {a b : icObj X}
    (f : icHom X a b) :
    icComp X (icId X a) f = f := by
  apply icHom_ext
  let q : (pshProdOverComp
      (pshProdOverId X.objPresheaf)
      X.morSpan).left.obj
        (Opposite.op ⟨⟨⟩⟩) :=
    ⟨(a, f.val), f.2.1.symm⟩
  have hnt : (MonoidalCategoryStruct.whiskerRight
      (MonObj.one (X := X.cat.X)) X.cat.X ≫
      MonObj.mul (X := X.cat.X)).left =
      (MonoidalCategoryStruct.leftUnitor
        X.cat.X).hom.left :=
    congrArg (·.left)
      (MonObj.one_mul (X := X.cat.X))
  have h := ConcreteCategory.congr_hom
    (NatTrans.congr_app hnt (Opposite.op ⟨⟨⟩⟩)) q
  convert h using 1

/-- Right identity: `f ≫ id = f`. Extracted
pointwise from `MonObj.mul_one`. -/
theorem icComp_id_right {a b : icObj X}
    (f : icHom X a b) :
    icComp X f (icId X b) = f := by
  apply icHom_ext
  let q : (pshProdOverComp
      X.morSpan
      (pshProdOverId X.objPresheaf)).left.obj
        (Opposite.op ⟨⟨⟩⟩) :=
    ⟨(f.val, b), f.2.2⟩
  have hnt : (MonoidalCategoryStruct.whiskerLeft
      X.cat.X (MonObj.one (X := X.cat.X)) ≫
      MonObj.mul (X := X.cat.X)).left =
      (MonoidalCategoryStruct.rightUnitor
        X.cat.X).hom.left :=
    congrArg (·.left)
      (MonObj.mul_one (X := X.cat.X))
  have h := ConcreteCategory.congr_hom
    (NatTrans.congr_app hnt (Opposite.op ⟨⟨⟩⟩)) q
  convert h using 1

/-- Associativity: `(f ≫ g) ≫ h = f ≫ (g ≫ h)`.
Extracted pointwise from `MonObj.mul_assoc`. -/
theorem icComp_assoc {a b c d : icObj X}
    (f : icHom X a b) (g : icHom X b c)
    (h : icHom X c d) :
    icComp X (icComp X f g) h =
      icComp X f (icComp X g h) := by
  apply icHom_ext
  let pair_fg : (pshProdOverComp
      X.morSpan X.morSpan).left.obj
        (Opposite.op ⟨⟨⟩⟩) :=
    icMkCompPair X f g
  let q : (pshProdOverComp
      (pshProdOverComp X.morSpan X.morSpan)
      X.morSpan).left.obj
        (Opposite.op ⟨⟨⟩⟩) :=
    ⟨(pair_fg, h.val),
      g.2.2.trans h.2.1.symm⟩
  have hnt : (MonoidalCategoryStruct.whiskerRight
      (MonObj.mul (X := X.cat.X)) X.cat.X ≫
      MonObj.mul (X := X.cat.X)).left =
      ((MonoidalCategoryStruct.associator
          X.cat.X X.cat.X X.cat.X).hom ≫
        MonoidalCategoryStruct.whiskerLeft
          X.cat.X
          (MonObj.mul (X := X.cat.X)) ≫
        MonObj.mul (X := X.cat.X)).left :=
    congrArg (·.left)
      (MonObj.mul_assoc (X := X.cat.X))
  have hax := ConcreteCategory.congr_hom
    (NatTrans.congr_app hnt (Opposite.op ⟨⟨⟩⟩)) q
  convert hax using 1

/-- The category structure on the objects of
an internal category over `Discrete Unit`. -/
instance icCategory :
    Category (icObj X) where
  Hom := icHom X
  id := icId X
  comp f g := icComp X f g
  id_comp := icComp_id_left X
  comp_id := icComp_id_right X
  assoc f g h := icComp_assoc X f g h

/-- The value of a composition in `icCategory`
is `X.compMap` applied to the composable pair. -/
theorem icComp_val {a b c : icObj X}
    (f : icHom X a b) (g : icHom X b c) :
    (icComp X f g).val =
      X.compMap.app (Opposite.op ⟨⟨⟩⟩)
        ⟨⟨f.val, g.val⟩,
          f.2.2.trans g.2.1.symm⟩ := rfl

/-- The value of `eqToHom h ≫ f` equals
`f.val`: composing with a transported identity
on the left does not change the underlying
morphism. -/
theorem icEqToHom_comp_val
    {a b c : icObj X}
    (h : a = b) (f : icHom X b c) :
    (icComp X (eqToHom h) f).val =
      f.val := by
  subst h
  exact congr_arg Subtype.val
    (icComp_id_left X f)

/-- The value of `f ≫ eqToHom h` equals
`f.val`: composing with a transported identity
on the right does not change the underlying
morphism. -/
theorem icComp_eqToHom_val
    {a b c : icObj X}
    (f : icHom X a b) (h : b = c) :
    (icComp X f (eqToHom h)).val =
      f.val := by
  subst h
  exact congr_arg Subtype.val
    (icComp_id_right X f)

/-- The category obtained from an internal
category over `Discrete Unit`: objects are the
elements of the object presheaf, morphisms are
elements of the morphism presheaf with specified
source and target. -/
def pshInternalCatToCat
    (X : PshInternalCat.{0, 0, w'}
      (Discrete Unit)) :
    Cat.{w', w'} :=
  Cat.of (icObj X)

/-- In the forward-then-backward roundtrip,
the objects are definitionally equal to `α`. -/
abbrev rtObjEquiv (α : Type w')
    [Category.{w'} α] :
    icObj (catToPshInternalCat α) = α :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Equivalence between the hom-types: morphisms
in the recovered category correspond to morphisms
in the original category. -/
def rtHomEquiv (α : Type w')
    [Category.{w'} α] (a b : α) :
    icHom (catToPshInternalCat α) a b ≃
      (a ⟶ b) where
  toFun m :=
    eqToHom m.2.1.symm ≫
      m.val.2.2 ≫ eqToHom m.2.2
  invFun f := ⟨⟨a, b, f⟩, ⟨rfl, rfl⟩⟩
  left_inv m := by
    apply Subtype.ext
    obtain ⟨⟨a', b', f⟩, ha, hb⟩ := m
    subst ha; subst hb
    simp only [eqToHom_refl, Category.id_comp,
      Category.comp_id]
    change (⟨_, ⟨_, f⟩⟩ : CatMorSigma α) =
      ⟨a', ⟨b', f⟩⟩
    rfl
  right_inv f := by simp

/-- `rtHomEquiv` sends the internal identity to
the category identity. -/
theorem rtHomEquiv_id (α : Type w')
    [Category.{w'} α] (a : α) :
    rtHomEquiv α a a
      (icId (catToPshInternalCat α) a) =
      𝟙 a := by
  dsimp [rtHomEquiv, icId, icIdFn,
    catToPshInternalCat,
    PshInternalCat.idMap]
  change 𝟙 a ≫ 𝟙 a ≫ 𝟙 a = 𝟙 a
  simp

/-- `compMap` for `catToPshInternalCat α` equals
`catCompNat α`. -/
theorem catToPsh_compMap_eq (α : Type w')
    [Category.{w'} α] :
    (catToPshInternalCat α).compMap =
      catCompNat α :=
  rfl

/-- `idMap` for `catToPshInternalCat α` sends `a`
to `⟨a, a, 𝟙 a⟩`. -/
theorem catToPsh_idMap_app (α : Type w')
    [Category.{w'} α] (a : α) :
    (catToPshInternalCat α).idMap.app
      (Opposite.op ⟨⟨⟩⟩) a =
      (⟨a, a, 𝟙 a⟩ : CatMorSigma α) :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- `rtHomEquiv` sends internal composition to
category composition. -/
theorem rtHomEquiv_comp (α : Type w')
    [Category.{w'} α]
    {a b c : α}
    (f : icHom (catToPshInternalCat α) a b)
    (g : icHom (catToPshInternalCat α) b c) :
    rtHomEquiv α a c
      (icComp (catToPshInternalCat α) f g) =
      rtHomEquiv α a b f ≫
        rtHomEquiv α b c g := by
  dsimp [rtHomEquiv, icComp, icCompApply,
    icMkCompPair]
  simp only [catToPsh_compMap_eq]
  dsimp [catCompNat, presheafPullbackFst,
    presheafPullbackSnd, presheafPullbackCone]
  simp only [Category.assoc,
    eqToHom_trans_assoc]

/-- The object map for the backward-then-forward
roundtrip: the identity at the unique object of
`Discrete Unit`, as a natural transformation from
`constPsh (icObj X)` to `X.objPresheaf`. -/
def rtBkObjMap :
    constPsh (icObj X) ⟶ X.objPresheaf where
  app := fun ⟨⟨⟨⟩⟩⟩ => TypeCat.ofHom _root_.id
  naturality := by
    intro ⟨⟨⟨⟩⟩⟩ ⟨⟨⟨⟩⟩⟩ f
    have hf : f = 𝟙 _ := Subsingleton.elim _ _
    subst hf; simp

/-- The inverse object map: the identity at the
unique object of `Discrete Unit`, as a natural
transformation from `X.objPresheaf` to
`constPsh (icObj X)`. -/
def rtBkObjMapInv :
    X.objPresheaf ⟶ constPsh (icObj X) where
  app := fun ⟨⟨⟨⟩⟩⟩ => TypeCat.ofHom _root_.id
  naturality := by
    intro ⟨⟨⟨⟩⟩⟩ ⟨⟨⟨⟩⟩⟩ f
    have hf : f = 𝟙 _ := Subsingleton.elim _ _
    subst hf; simp

/-- The morphism map for the backward-then-forward
roundtrip: sends a bundled morphism `⟨a, b, f⟩` in
`CatMorSigma (icObj X)` to the underlying element
`f.val` in `icAllMor X`. -/
def rtBkMorMap :
    constPsh (CatMorSigma (icObj X)) ⟶
      X.morPresheaf where
  app := fun ⟨⟨⟨⟩⟩⟩ =>
    TypeCat.ofHom fun m => m.2.2.val
  naturality := by
    intro ⟨⟨⟨⟩⟩⟩ ⟨⟨⟨⟩⟩⟩ f
    have hf : f = 𝟙 _ := Subsingleton.elim _ _
    subst hf; simp

/-- The morphism map commutes with the span
projections through the object map. -/
theorem rtBkCompat :
    rtBkMorMap X ≫ X.morSpan.hom =
      (catMorSpanOver (icObj X)).hom ≫
        pshProdMap (rtBkObjMap X)
          (rtBkObjMap X) := by
  apply pshProdPresheaf_hom_ext
  · ext ⟨⟨⟨⟩⟩⟩ ⟨a, b, f⟩
    dsimp [rtBkMorMap, rtBkObjMap,
      catMorSpanOver, catMorSrcTgtNat,
      pshProdLift, pshProdFst, constPshMap]
    exact f.2.1
  · ext ⟨⟨⟨⟩⟩⟩ ⟨a, b, f⟩
    dsimp [rtBkMorMap, rtBkObjMap,
      catMorSpanOver, catMorSrcTgtNat,
      pshProdLift, pshProdSnd, constPshMap]
    exact f.2.2

/-- The morphism map preserves identities:
applying it to the identity of `catToPshInternalCat`
gives the identity of `X`. -/
theorem rtBkIdPres :
    (catToPshInternalCat (icObj X)).idMap ≫
      rtBkMorMap X =
      rtBkObjMap X ≫ X.idMap := by
  ext ⟨⟨⟨⟩⟩⟩ a
  simp only [NatTrans.comp_app]
  dsimp [rtBkMorMap, rtBkObjMap]
  rfl

/-- The morphism map preserves composition:
applying it to a composite in
`catToPshInternalCat (icObj X)` gives the
composite in `X`. -/
theorem rtBkCompPres :
    (catToPshInternalCat (icObj X)).compMap ≫
      rtBkMorMap X =
      pshInternalCompPairsMap
        (rtBkObjMap X) (rtBkMorMap X)
        (rtBkCompat X) ≫ X.compMap := by
  ext ⟨⟨⟨⟩⟩⟩ p
  obtain ⟨⟨m₁, m₂⟩, h⟩ := p
  obtain ⟨a, b, f⟩ := m₁
  obtain ⟨c, d, g⟩ := m₂
  change b = c at h
  subst h
  simp only [catToPsh_compMap_eq]
  change (f ≫ eqToHom rfl ≫ g : icHom X a d).val =
    (X.compMap ≫ 𝟙 _).app _ _
  rw [Category.comp_id]
  change (f ≫ 𝟙 b ≫ g : icHom X a d).val =
    X.compMap.app _ _
  rw [Category.id_comp]
  change (icComp X f g).val = _
  rw [icComp_val]
  apply congr_arg
    (X.compMap.app (Opposite.op ⟨⟨⟩⟩))
  apply Subtype.ext
  rfl

/-- The internal functor from
`catToPshInternalCat (icObj X)` to `X`,
recovering the original internal category
structure. -/
def rtBkFunctor :
    PshInternalFunctor
      (catToPshInternalCat (icObj X)) X where
  objMap := rtBkObjMap X
  morMap := rtBkMorMap X
  compat := rtBkCompat X
  id_pres := rtBkIdPres X
  comp_pres := rtBkCompPres X

/-- The inverse morphism map: sends a morphism
`m` of the internal category `X` to the bundled
triple `⟨src m, tgt m, ⟨m, rfl, rfl⟩⟩` in
`CatMorSigma (icObj X)`. -/
def rtFwMorMap :
    X.morPresheaf ⟶
      constPsh (CatMorSigma (icObj X)) where
  app := fun ⟨⟨⟨⟩⟩⟩ => TypeCat.ofHom fun m =>
    ⟨icSrcFn X m, icTgtFn X m,
      ⟨m, rfl, rfl⟩⟩
  naturality := by
    intro ⟨⟨⟨⟩⟩⟩ ⟨⟨⟨⟩⟩⟩ f
    have hf : f = 𝟙 _ := Subsingleton.elim _ _
    subst hf; simp

/-- The inverse morphism map commutes with the
span projections through the inverse object map. -/
theorem rtFwCompat :
    rtFwMorMap X ≫
      (catMorSpanOver (icObj X)).hom =
      X.morSpan.hom ≫
        pshProdMap (rtBkObjMapInv X)
          (rtBkObjMapInv X) := by
  apply pshProdPresheaf_hom_ext
  · ext ⟨⟨⟨⟩⟩⟩ m; rfl
  · ext ⟨⟨⟨⟩⟩⟩ m; rfl

/-- Two elements of `CatMorSigma (icObj X)` are
equal when they have the same underlying
morphism. -/
theorem icCatMorSigma_val_ext
    (x y : CatMorSigma (icObj X))
    (h : x.2.2.val = y.2.2.val) : x = y := by
  obtain ⟨_, _, ⟨_, h₁s, h₁t⟩⟩ := x
  obtain ⟨_, _, ⟨_, h₂s, h₂t⟩⟩ := y
  simp only at h; subst h
  subst h₁s; subst h₁t; subst h₂s; subst h₂t
  rfl

/-- The inverse morphism map preserves
identities. -/
theorem rtFwIdPres :
    X.idMap ≫ rtFwMorMap X =
      rtBkObjMapInv X ≫
        (catToPshInternalCat (icObj X)).idMap := by
  ext ⟨⟨⟨⟩⟩⟩ a
  simp only [NatTrans.comp_app]
  dsimp [rtFwMorMap, rtBkObjMapInv]
  exact icCatMorSigma_val_ext X _ _ rfl

set_option backward.isDefEq.respectTransparency false in
/-- The inverse morphism map preserves
composition. -/
theorem rtFwCompPres :
    X.compMap ≫ rtFwMorMap X =
      pshInternalCompPairsMap
        (rtBkObjMapInv X) (rtFwMorMap X)
        (rtFwCompat X) ≫
        (catToPshInternalCat (icObj X)).compMap := by
  ext ⟨⟨⟨⟩⟩⟩ ⟨⟨m₁, m₂⟩, h⟩
  simp only [catToPsh_compMap_eq]
  apply icCatMorSigma_val_ext
  dsimp [rtFwMorMap, rtBkObjMapInv,
    catCompNat, pshInternalCompPairsMap,
    presheafPullbackFst, presheafPullbackSnd,
    presheafPullbackCone, presheafPullbackLift,
    catMorSpanOver, catMorSrcTgtNat,
    catMorTgt, catMorSrc, constPshMap,
    pshProdLift, pshProdFst, pshProdSnd]
  dsimp only [CategoryStruct.comp,
    icCategory]
  rw [icComp_val]
  apply congr_arg
    (X.compMap.app (Opposite.op ⟨⟨⟩⟩))
  apply Subtype.ext
  change (m₁, m₂) = (_, _)
  congr 1
  rw [icEqToHom_comp_val]
  rfl

/-- The forward internal functor from `X` to
`catToPshInternalCat (icObj X)`, sending each
morphism of `X` to its bundled sigma triple. -/
def rtFwFunctor :
    PshInternalFunctor X
      (catToPshInternalCat (icObj X)) where
  objMap := rtBkObjMapInv X
  morMap := rtFwMorMap X
  compat := rtFwCompat X
  id_pres := rtFwIdPres X
  comp_pres := rtFwCompPres X

/-- Roundtrip: forward then backward is the
identity on `X`. -/
theorem rtRoundtrip_fw_bk :
    rtFwFunctor X ≫ rtBkFunctor X = 𝟙 X := by
  apply PshInternalFunctor.ext'
  · change (PshInternalFunctor.comp
      (rtFwFunctor X) (rtBkFunctor X)).objMap =
        (PshInternalFunctor.id X).objMap
    ext ⟨⟨⟨⟩⟩⟩ a; rfl
  · change (PshInternalFunctor.comp
      (rtFwFunctor X) (rtBkFunctor X)).morMap =
        (PshInternalFunctor.id X).morMap
    ext ⟨⟨⟨⟩⟩⟩ m; rfl

/-- Roundtrip: backward then forward is the
identity on `catToPshInternalCat (icObj X)`. -/
theorem rtRoundtrip_bk_fw :
    rtBkFunctor X ≫ rtFwFunctor X =
      𝟙 (catToPshInternalCat (icObj X)) := by
  apply PshInternalFunctor.ext'
  · change (PshInternalFunctor.comp
      (rtBkFunctor X) (rtFwFunctor X)).objMap =
        (PshInternalFunctor.id _).objMap
    ext ⟨⟨⟨⟩⟩⟩ a; rfl
  · change (PshInternalFunctor.comp
      (rtBkFunctor X) (rtFwFunctor X)).morMap =
        (PshInternalFunctor.id _).morMap
    ext ⟨⟨⟨⟩⟩⟩ ⟨a, b, m, hs, ht⟩
    dsimp [PshInternalFunctor.comp,
      PshInternalFunctor.id,
      rtBkFunctor, rtFwFunctor,
      rtBkMorMap, rtFwMorMap]
    exact icCatMorSigma_val_ext X _ _ rfl

/-- The roundtrip isomorphism between `X` and
`catToPshInternalCat (icObj X)` in the category
`PshInternalCat (Discrete Unit)`. -/
def rtIso :
    X ≅ catToPshInternalCat (icObj X) where
  hom := rtFwFunctor X
  inv := rtBkFunctor X
  hom_inv_id := rtRoundtrip_fw_bk X
  inv_hom_id := rtRoundtrip_bk_fw X

set_option backward.isDefEq.respectTransparency false in
/-- The action of `catToPshInternalCat` on
functors: a functor `F : α ⥤ β` induces an
internal functor between the corresponding
internal categories. -/
def catToPshInternalCatMap
    {α β : Type w'} [Category.{w'} α]
    [Category.{w'} β] (F : α ⥤ β) :
    PshInternalFunctor
      (catToPshInternalCat α)
      (catToPshInternalCat β) where
  objMap := constPshMap F.obj
  morMap := constPshMap
    (fun ⟨a, b, f⟩ =>
      ⟨F.obj a, F.obj b, F.map f⟩)
  compat := by
    apply pshProdPresheaf_hom_ext
    · ext ⟨⟨⟨⟩⟩⟩ ⟨a, b, f⟩; rfl
    · ext ⟨⟨⟨⟩⟩⟩ ⟨a, b, f⟩; rfl
  id_pres := by
    ext ⟨⟨⟨⟩⟩⟩ a
    dsimp [constPshMap]
    rw [catToPsh_idMap_app, catToPsh_idMap_app]
    simp
  comp_pres := by
    ext ⟨⟨⟨⟩⟩⟩ ⟨⟨m₁, m₂⟩, h⟩
    simp only [catToPsh_compMap_eq]
    dsimp [constPshMap, catCompNat,
      pshInternalCompPairsMap,
      presheafPullbackFst, presheafPullbackSnd,
      presheafPullbackCone, presheafPullbackLift,
      catMorSpanOver, catMorSrcTgtNat,
      catMorTgt, catMorSrc,
      pshProdLift, pshProdFst, pshProdSnd]
    congr 1; congr 1
    simp only [CategoryTheory.Functor.map_comp,
      eqToHom_map]
    rfl

/-- The forward functor from `Cat` to
`PshInternalCat (Discrete Unit)`, mapping a
category to its internal-category encoding
and functors to internal functors. -/
def catToPshInternalCatFunctor :
    Cat.{w', w'} ⥤
      PshInternalCat.{0, 0, w'}
        (Discrete Unit) where
  obj C := catToPshInternalCat C
  map F := catToPshInternalCatMap F.toFunctor
  map_id C := by
    apply PshInternalFunctor.ext'
    · ext ⟨⟨⟨⟩⟩⟩ a; rfl
    · ext ⟨⟨⟨⟩⟩⟩ ⟨a, b, f⟩
      rfl
  map_comp F G := by
    apply PshInternalFunctor.ext'
    · ext ⟨⟨⟨⟩⟩⟩ a; rfl
    · ext ⟨⟨⟨⟩⟩⟩ ⟨a, b, f⟩; rfl

set_option backward.isDefEq.respectTransparency false in
/-- Extract a functor from an internal functor
between internal categories in `Psh(1)`. The
object map evaluates `F.objMap` at the unique
presheaf object; the morphism map evaluates
`F.morMap` and adjusts source/target via the
compatibility condition. -/
def pshInternalFunctorToFunctor
    {X Y : PshInternalCat.{0, 0, w'}
      (Discrete Unit)}
    (F : PshInternalFunctor X Y) :
    icObj X ⥤ icObj Y where
  obj a := F.objMap.app (Opposite.op ⟨⟨⟩⟩) a
  map {a b} f :=
    ⟨F.morMap.app (Opposite.op ⟨⟨⟩⟩) f.val,
      by
        have hc := ConcreteCategory.congr_hom
          (NatTrans.congr_app F.compat
            (Opposite.op ⟨⟨⟩⟩)) f.val
        simp only [NatTrans.comp_app_apply]
          at hc
        dsimp [pshProdMap, pshProdLift,
          pshProdFst, pshProdSnd] at hc
        have hfst := congr_arg Prod.fst hc
        have hsnd := congr_arg Prod.snd hc
        dsimp at hfst hsnd
        exact ⟨hfst.trans
            (congrArg (F.objMap.app _) f.2.1),
          hsnd.trans
            (congrArg (F.objMap.app _) f.2.2)⟩⟩
  map_id a := by
    apply Subtype.ext
    have hid := ConcreteCategory.congr_hom
      (NatTrans.congr_app F.id_pres
        (Opposite.op ⟨⟨⟩⟩)) a
    simp only [NatTrans.comp_app_apply] at hid
    exact hid
  map_comp {a b c} f g := by
    apply Subtype.ext
    have hcomp := ConcreteCategory.congr_hom
      (NatTrans.congr_app F.comp_pres
        (Opposite.op ⟨⟨⟩⟩))
      (⟨⟨f.val, g.val⟩,
        f.2.2.trans g.2.1.symm⟩ :
        (pshProdOverComp X.morSpan
          X.morSpan).left.obj
            (Opposite.op ⟨⟨⟩⟩))
    simp only [NatTrans.comp_app_apply] at hcomp
    dsimp only [CategoryStruct.comp,
      icCategory]
    rw [icComp_val]
    rw [hcomp]
    dsimp [pshInternalCompPairsMap,
      presheafPullbackFst, presheafPullbackSnd,
      presheafPullbackCone, presheafPullbackLift]
    rw [icComp_val]
    rfl

set_option backward.isDefEq.respectTransparency false in
/-- The backward functor from
`PshInternalCat (Discrete Unit)` to `Cat`,
mapping an internal category to its extracted
category and internal functors to functors. -/
def pshInternalCatToCatFunctor :
    PshInternalCat.{0, 0, w'}
      (Discrete Unit) ⥤ Cat.{w', w'} where
  obj X := Cat.of (icObj X)
  map F :=
    Cat.Hom.ofFunctor
      (pshInternalFunctorToFunctor F)
  map_id X := by
    apply Cat.Hom.ext
    refine CategoryTheory.Functor.ext
      (fun a => rfl) (fun a b f => ?_)
    simp only [eqToHom_refl, Category.id_comp,
      Category.comp_id]
    apply Subtype.ext
    dsimp [pshInternalFunctorToFunctor,
      PshInternalFunctor.id]
    rfl
  map_comp {X Y Z} F G := by
    apply Cat.Hom.ext
    refine CategoryTheory.Functor.ext
      (fun a => rfl) (fun a b f => ?_)
    simp only [eqToHom_refl, Category.id_comp,
      Category.comp_id]
    apply Subtype.ext
    dsimp [pshInternalFunctorToFunctor,
      PshInternalFunctor.comp]
    rfl

/-- The forward component of the Cat-side unit
isomorphism: wraps morphisms of the original
category into `icHom` subtypes. -/
def catToIcCat (α : Type w')
    [Category.{w'} α] :
    α ⥤ icObj (catToPshInternalCat α) where
  obj a := a
  map f := ⟨⟨_, _, f⟩, rfl, rfl⟩
  map_id a := by
    apply Subtype.ext; rfl
  map_comp f g := by
    apply Subtype.ext
    dsimp only [CategoryStruct.comp, icCategory]
    rw [icComp_val]
    simp only [catToPsh_compMap_eq]
    dsimp [catCompNat,
      presheafPullbackFst, presheafPullbackSnd,
      presheafPullbackCone]
    change _ =
      (⟨_, _, f ≫ eqToHom rfl ≫ g⟩ :
        CatMorSigma α)
    simp [eqToHom_refl, Category.id_comp]

set_option backward.isDefEq.respectTransparency false in
/-- The backward component of the Cat-side unit
isomorphism: extracts the underlying morphism from
an `icHom` subtype via `eqToHom` transport. -/
def icCatToCat (α : Type w')
    [Category.{w'} α] :
    icObj (catToPshInternalCat α) ⥤ α where
  obj a := a
  map {a b} m :=
    eqToHom m.2.1.symm ≫
      m.val.2.2 ≫ eqToHom m.2.2
  map_id a := by
    simp only [eqToHom_refl,
      Category.id_comp, Category.comp_id]
    rfl
  map_comp {a b c} f g := by
    dsimp only [CategoryStruct.comp, icCategory,
      icComp, icCompApply, icMkCompPair]
    simp only [catToPsh_compMap_eq]
    dsimp [catCompNat, presheafPullbackFst,
      presheafPullbackSnd, presheafPullbackCone]
    simp only [Category.assoc,
      eqToHom_trans_assoc]

set_option backward.isDefEq.respectTransparency false in
/-- The Cat-side isomorphism: the original
category `α` is isomorphic to the extracted
category `icObj (catToPshInternalCat α)` in
`Cat`. -/
def catIcIso (C : Cat.{w', w'}) :
    C ≅ Cat.of
      (icObj (catToPshInternalCat C)) where
  hom := Cat.Hom.ofFunctor (catToIcCat C)
  inv := Cat.Hom.ofFunctor (icCatToCat C)
  hom_inv_id := by
    apply Cat.Hom.ext
    refine CategoryTheory.Functor.ext
      (fun a => rfl) (fun a b f => ?_)
    simp only [eqToHom_refl, Category.id_comp,
      Category.comp_id]
    dsimp [catToIcCat, icCatToCat]
    simp only [Category.id_comp,
      Category.comp_id]
  inv_hom_id := by
    apply Cat.Hom.ext
    refine CategoryTheory.Functor.ext
      (fun a => rfl) (fun a b f => ?_)
    simp only [eqToHom_refl, Category.id_comp,
      Category.comp_id]
    obtain ⟨⟨a', b', f'⟩, ha, hb⟩ := f
    subst ha; subst hb
    apply Subtype.ext
    dsimp [catToIcCat, icCatToCat]
    congr 1; congr 1
    simp only [Category.id_comp,
      Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
/-- The unit natural isomorphism: the identity
functor on `Cat` is naturally isomorphic to the
composite `catToPshInternalCatFunctor ⋙
pshInternalCatToCatFunctor`. -/
def catPshInternalUnitIso :
    𝟭 Cat.{w', w'} ≅
      catToPshInternalCatFunctor ⋙
        pshInternalCatToCatFunctor :=
  NatIso.ofComponents
    (fun C => catIcIso C)
    (fun {C D} F => by
      apply Cat.Hom.ext
      refine CategoryTheory.Functor.ext
        (fun a => rfl) (fun a b f => ?_)
      simp only [eqToHom_refl,
        Category.id_comp, Category.comp_id]
      apply Subtype.ext
      dsimp [catIcIso, catToIcCat,
        pshInternalFunctorToFunctor,
        pshInternalCatToCatFunctor,
        catToPshInternalCatFunctor,
        catToPshInternalCatMap, constPshMap])

/-- The counit natural isomorphism:
`pshInternalCatToCatFunctor ⋙
catToPshInternalCatFunctor` is naturally isomorphic
to the identity on `PshInternalCat (Discrete Unit)`.
Each component is `(rtIso X).symm`. -/
def catPshInternalCounitIso :
    pshInternalCatToCatFunctor ⋙
      catToPshInternalCatFunctor ≅
      (𝟭 (PshInternalCat.{0, 0, w'}
        (Discrete Unit))) :=
  NatIso.ofComponents
    (fun X => (rtIso X).symm)
    (fun {X Y} F => by
      apply PshInternalFunctor.ext'
      · ext ⟨⟨⟨⟩⟩⟩ a; rfl
      · ext ⟨⟨⟨⟩⟩⟩ ⟨a, b, f⟩
        dsimp [PshInternalFunctor.comp,
          rtBkFunctor, rtBkMorMap,
          catToPshInternalCatFunctor,
          catToPshInternalCatMap, constPshMap,
          pshInternalCatToCatFunctor,
          pshInternalFunctorToFunctor]
        rfl)

/-- The equivalence `Cat ≌ PshInternalCat
(Discrete Unit)`: ordinary categories are
equivalent to internal categories in presheaves
over the terminal category. -/
def catPshInternalEquiv :
    Cat.{w', w'} ≌
      PshInternalCat.{0, 0, w'}
        (Discrete Unit) where
  functor := catToPshInternalCatFunctor
  inverse := pshInternalCatToCatFunctor
  unitIso := catPshInternalUnitIso
  counitIso := catPshInternalCounitIso

end DiscreteUnitEquiv

end GebLean
