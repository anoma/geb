import GebLean.EqualizerCompletion
import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers

/-!
# Finite Limits in the Free Equalizer Completion

Proves that the free equalizer completion of a
category with chosen finite products inherits
chosen finite products (constructed pointwise)
and equalizers, hence has all finite limits.
-/

namespace GebLean

open CategoryTheory

universe v u

variable {C : Type u} [Category.{v} C]
  [h : HasChosenFiniteProducts C]

/-! ## Auxiliary lemmas about cfpMap -/

theorem cfpMap_fst
    {A B A' B' : C}
    (f : A ⟶ A') (g : B ⟶ B') :
    cfpMap f g ≫ cfpFst A' B' =
      cfpFst A B ≫ f := by
  unfold cfpMap
  exact (h.product A' B').lift_fst _ _

theorem cfpMap_snd
    {A B A' B' : C}
    (f : A ⟶ A') (g : B ⟶ B') :
    cfpMap f g ≫ cfpSnd A' B' =
      cfpSnd A B ≫ g := by
  unfold cfpMap
  exact (h.product A' B').lift_snd _ _

theorem cfpMap_id (A B : C) :
    cfpMap (𝟙 A) (𝟙 B) =
      𝟙 (cfpProd A B) := by
  unfold cfpMap
  rw [Category.comp_id, Category.comp_id]
  exact ((h.product A B).lift_uniq
    (cfpFst A B) (cfpSnd A B)
    (𝟙 _)
    (Category.id_comp _)
    (Category.id_comp _)).symm

theorem cfpLift_fst
    {A B D : C}
    (f : D ⟶ A) (g : D ⟶ B) :
    cfpLift f g ≫ cfpFst A B = f :=
  (h.product A B).lift_fst f g

theorem cfpLift_snd
    {A B D : C}
    (f : D ⟶ A) (g : D ⟶ B) :
    cfpLift f g ≫ cfpSnd A B = g :=
  (h.product A B).lift_snd f g

theorem cfpLift_uniq
    {A B D : C}
    (f : D ⟶ A) (g : D ⟶ B)
    (m : D ⟶ cfpProd A B)
    (hf : m ≫ cfpFst A B = f)
    (hg : m ≫ cfpSnd A B = g) :
    m = cfpLift f g :=
  (h.product A B).lift_uniq f g m hf hg

theorem cfpMap_comp
    {A B A' B' A'' B'' : C}
    (f₁ : A ⟶ A') (g₁ : B ⟶ B')
    (f₂ : A' ⟶ A'') (g₂ : B' ⟶ B'') :
    cfpMap f₁ g₁ ≫ cfpMap f₂ g₂ =
      cfpMap (f₁ ≫ f₂) (g₁ ≫ g₂) := by
  unfold cfpMap
  apply cfpLift_uniq
  · rw [Category.assoc, cfpLift_fst,
      ← Category.assoc, cfpLift_fst,
      Category.assoc]
  · rw [Category.assoc, cfpLift_snd,
      ← Category.assoc, cfpLift_snd,
      Category.assoc]

/-! ## Terminal object -/

/-- The terminal object in the equalizer completion
is the trivially-embedded terminal of the base
category. -/
def cpTerminal :
    CoreflexivePairObj C :=
  cpEmbed cfpTerminal

/-- The unique morphism from any coreflexive pair
to the terminal object. -/
def cpTerminalFrom
    (X : CoreflexivePairObj C) :
    CPMor X cpTerminal :=
  Quotient.mk (cpPreMorSetoid X cpTerminal)
    ⟨cfpTerminalFrom X.src, by
      unfold IsCPPremorphism cpTerminal cpEmbed
      simp only [Category.comp_id]
      exact Relation.EqvGen.refl _⟩

/-- Any morphism to the terminal coreflexive pair
equals `cpTerminalFrom`. -/
theorem cpTerminalFrom_uniq
    {X : CoreflexivePairObj C}
    (f : CPMor X cpTerminal) :
    f = cpTerminalFrom X := by
  revert f
  apply Quotient.ind
  intro ⟨f_val, _⟩
  apply Quotient.sound
    (s := cpPreMorSetoid X cpTerminal)
  change CoreflexiveEqv X f_val
    (cfpTerminalFrom X.src)
  rw [h.terminal.uniq f_val]
  exact Relation.EqvGen.refl _

/-! ## Binary products -/

/-- The product of two coreflexive pairs, constructed
pointwise using products in the base category. -/
def cpProd
    (X Y : CoreflexivePairObj C) :
    CoreflexivePairObj C where
  src := cfpProd X.src Y.src
  tgt := cfpProd X.tgt Y.tgt
  left := cfpMap X.left Y.left
  right := cfpMap X.right Y.right
  retract := cfpMap X.retract Y.retract
  retract_left := by
    rw [cfpMap_comp, X.retract_left,
      Y.retract_left, cfpMap_id]
  retract_right := by
    rw [cfpMap_comp, X.retract_right,
      Y.retract_right, cfpMap_id]

/-- `cfpFst` is a premorphism from the pointwise
product to the first component. -/
theorem cpFst_isPremorphism
    (X Y : CoreflexivePairObj C) :
    IsCPPremorphism (cpProd X Y) X
      (cfpFst X.src Y.src) := by
  unfold IsCPPremorphism
  exact Relation.EqvGen.rel _ _
    ⟨cfpFst X.tgt Y.tgt,
      cfpMap_fst X.left Y.left,
      cfpMap_fst X.right Y.right⟩

/-- The first projection in the equalizer
completion. -/
def cpFst
    (X Y : CoreflexivePairObj C) :
    CPMor (cpProd X Y) X :=
  Quotient.mk (cpPreMorSetoid (cpProd X Y) X)
    ⟨cfpFst X.src Y.src,
      cpFst_isPremorphism X Y⟩

/-- `cfpSnd` is a premorphism from the pointwise
product to the second component. -/
theorem cpSnd_isPremorphism
    (X Y : CoreflexivePairObj C) :
    IsCPPremorphism (cpProd X Y) Y
      (cfpSnd X.src Y.src) := by
  unfold IsCPPremorphism
  exact Relation.EqvGen.rel _ _
    ⟨cfpSnd X.tgt Y.tgt,
      cfpMap_snd X.left Y.left,
      cfpMap_snd X.right Y.right⟩

/-- The second projection in the equalizer
completion. -/
def cpSnd
    (X Y : CoreflexivePairObj C) :
    CPMor (cpProd X Y) Y :=
  Quotient.mk (cpPreMorSetoid (cpProd X Y) Y)
    ⟨cfpSnd X.src Y.src,
      cpSnd_isPremorphism X Y⟩

/-- Composition of `cfpLift` with `cfpMap`. -/
theorem cfpLift_cfpMap
    {A B A' B' D : C}
    (f : D ⟶ A) (g : D ⟶ B)
    (p : A ⟶ A') (q : B ⟶ B') :
    cfpLift f g ≫ cfpMap p q =
      cfpLift (f ≫ p) (g ≫ q) := by
  unfold cfpMap
  apply cfpLift_uniq
  · rw [Category.assoc, cfpLift_fst,
      ← Category.assoc, cfpLift_fst]
  · rw [Category.assoc, cfpLift_snd,
      ← Category.assoc, cfpLift_snd]

/-- The one-step coreflexive relation is compatible
with `cfpLift`: if `f₀ ~₁ f₁` (w.r.t. Z) and
`g` is any morphism, then
`cfpLift f₀ g ~₁ cfpLift f₁ g`. -/
theorem CoreflexiveRelStep_cfpLift_left
    (Z : CoreflexivePairObj C)
    {A B : C}
    {f₀ f₁ : Z.src ⟶ A}
    (hf : CoreflexiveRelStep Z f₀ f₁)
    (g : Z.src ⟶ B) :
    CoreflexiveRelStep Z
      (cfpLift f₀ g) (cfpLift f₁ g) := by
  obtain ⟨w, hl, hr⟩ := hf
  refine ⟨cfpLift w (Z.retract ≫ g), ?_, ?_⟩
  · apply cfpLift_uniq
    · rw [Category.assoc, cfpLift_fst, hl]
    · rw [Category.assoc, cfpLift_snd,
        ← Category.assoc,
        Z.retract_left, Category.id_comp]
  · apply cfpLift_uniq
    · rw [Category.assoc, cfpLift_fst, hr]
    · rw [Category.assoc, cfpLift_snd,
        ← Category.assoc,
        Z.retract_right, Category.id_comp]

/-- The one-step coreflexive relation is compatible
with `cfpLift` in the second argument. -/
theorem CoreflexiveRelStep_cfpLift_right
    (Z : CoreflexivePairObj C)
    {A B : C}
    (f : Z.src ⟶ A)
    {g₀ g₁ : Z.src ⟶ B}
    (hg : CoreflexiveRelStep Z g₀ g₁) :
    CoreflexiveRelStep Z
      (cfpLift f g₀) (cfpLift f g₁) := by
  obtain ⟨w, hl, hr⟩ := hg
  refine ⟨cfpLift (Z.retract ≫ f) w, ?_, ?_⟩
  · apply cfpLift_uniq
    · rw [Category.assoc, cfpLift_fst,
        ← Category.assoc,
        Z.retract_left, Category.id_comp]
    · rw [Category.assoc, cfpLift_snd, hl]
  · apply cfpLift_uniq
    · rw [Category.assoc, cfpLift_fst,
        ← Category.assoc,
        Z.retract_right, Category.id_comp]
    · rw [Category.assoc, cfpLift_snd, hr]

/-- `CoreflexiveEqv` is compatible with `cfpLift`
in the first argument. -/
theorem CoreflexiveEqv_cfpLift_left
    (Z : CoreflexivePairObj C)
    {A B : C}
    {f₀ f₁ : Z.src ⟶ A}
    (hf : CoreflexiveEqv Z f₀ f₁)
    (g : Z.src ⟶ B) :
    CoreflexiveEqv Z
      (cfpLift f₀ g) (cfpLift f₁ g) := by
  induction hf with
  | rel _ _ hr =>
    exact Relation.EqvGen.rel _ _
      (CoreflexiveRelStep_cfpLift_left Z hr g)
  | refl _ => exact Relation.EqvGen.refl _
  | symm _ _ _ ih =>
    exact Relation.EqvGen.symm _ _ ih
  | trans _ _ _ _ _ ih1 ih2 =>
    exact Relation.EqvGen.trans _ _ _ ih1 ih2

/-- `CoreflexiveEqv` is compatible with `cfpLift`
in the second argument. -/
theorem CoreflexiveEqv_cfpLift_right
    (Z : CoreflexivePairObj C)
    {A B : C}
    (f : Z.src ⟶ A)
    {g₀ g₁ : Z.src ⟶ B}
    (hg : CoreflexiveEqv Z g₀ g₁) :
    CoreflexiveEqv Z
      (cfpLift f g₀) (cfpLift f g₁) := by
  induction hg with
  | rel _ _ hr =>
    exact Relation.EqvGen.rel _ _
      (CoreflexiveRelStep_cfpLift_right Z f hr)
  | refl _ => exact Relation.EqvGen.refl _
  | symm _ _ _ ih =>
    exact Relation.EqvGen.symm _ _ ih
  | trans _ _ _ _ _ ih1 ih2 =>
    exact Relation.EqvGen.trans _ _ _ ih1 ih2

/-- `cfpLift` of two premorphisms is a premorphism
to the pointwise product. -/
theorem cpLift_isPremorphism
    (Z X Y : CoreflexivePairObj C)
    (f : Z.src ⟶ X.src) (g : Z.src ⟶ Y.src)
    (hf : IsCPPremorphism Z X f)
    (hg : IsCPPremorphism Z Y g) :
    IsCPPremorphism Z (cpProd X Y)
      (cfpLift f g) := by
  unfold IsCPPremorphism cpProd
  simp only
  rw [cfpLift_cfpMap, cfpLift_cfpMap]
  exact Relation.EqvGen.trans _ _ _
    (CoreflexiveEqv_cfpLift_left Z hf
      (g ≫ Y.left))
    (CoreflexiveEqv_cfpLift_right Z
      (f ≫ X.right) hg)

/-- The pairing morphism in the equalizer completion,
lifted from `cfpLift` through the quotient. -/
def cpLift
    {Z X Y : CoreflexivePairObj C}
    (f : CPMor Z X) (g : CPMor Z Y) :
    CPMor Z (cpProd X Y) :=
  Quotient.lift₂
    (s₁ := cpPreMorSetoid Z X)
    (s₂ := cpPreMorSetoid Z Y)
    (fun f' g' =>
      Quotient.mk (cpPreMorSetoid Z (cpProd X Y))
        ⟨cfpLift f'.val g'.val,
         cpLift_isPremorphism Z X Y
           f'.val g'.val
           f'.property g'.property⟩)
    (fun f₁ g₁ f₂ g₂ hf hg => by
      apply Quotient.sound
        (s := cpPreMorSetoid Z (cpProd X Y))
      exact Relation.EqvGen.trans _ _ _
        (CoreflexiveEqv_cfpLift_left Z hf g₁.val)
        (CoreflexiveEqv_cfpLift_right Z
          f₂.val hg))
    f g

/-! ## Product laws -/

/-- First projection absorbs pairing. -/
theorem cpLift_fst_law
    {Z X Y : CoreflexivePairObj C}
    (f : CPMor Z X) (g : CPMor Z Y) :
    cpComp (cpLift f g) (cpFst X Y) = f := by
  revert f g
  apply Quotient.ind
  intro f_raw
  apply Quotient.ind
  intro g_raw
  apply Quotient.sound
    (s := cpPreMorSetoid Z X)
  change CoreflexiveEqv Z
    (cfpLift f_raw.val g_raw.val ≫
      cfpFst X.src Y.src) f_raw.val
  rw [cfpLift_fst]
  exact Relation.EqvGen.refl _

/-- Second projection absorbs pairing. -/
theorem cpLift_snd_law
    {Z X Y : CoreflexivePairObj C}
    (f : CPMor Z X) (g : CPMor Z Y) :
    cpComp (cpLift f g) (cpSnd X Y) = g := by
  revert f g
  apply Quotient.ind
  intro f_raw
  apply Quotient.ind
  intro g_raw
  apply Quotient.sound
    (s := cpPreMorSetoid Z Y)
  change CoreflexiveEqv Z
    (cfpLift f_raw.val g_raw.val ≫
      cfpSnd X.src Y.src) g_raw.val
  rw [cfpLift_snd]
  exact Relation.EqvGen.refl _

/-- Uniqueness of pairing in the equalizer
completion. -/
theorem cpLift_uniq_law
    {Z X Y : CoreflexivePairObj C}
    (f : CPMor Z X) (g : CPMor Z Y)
    (m : CPMor Z (cpProd X Y))
    (hf : cpComp m (cpFst X Y) = f)
    (hg : cpComp m (cpSnd X Y) = g) :
    m = cpLift f g := by
  subst hf; subst hg
  revert m
  apply Quotient.ind
  intro m_raw
  apply Quotient.sound
    (s := cpPreMorSetoid Z (cpProd X Y))
  change CoreflexiveEqv Z m_raw.val
    (cfpLift (m_raw.val ≫ cfpFst X.src Y.src)
      (m_raw.val ≫ cfpSnd X.src Y.src))
  rw [← cfpLift_uniq
    (m_raw.val ≫ cfpFst X.src Y.src)
    (m_raw.val ≫ cfpSnd X.src Y.src)
    m_raw.val rfl rfl]
  exact Relation.EqvGen.refl _

/-! ## Assembling chosen finite products -/

/-- Chosen terminal object in the equalizer
completion. -/
def cpChosenTerminal :
    ChosenTerminal (CoreflexivePairObj C) where
  obj := cpTerminal
  from_ := cpTerminalFrom
  uniq := cpTerminalFrom_uniq

/-- Chosen binary product in the equalizer
completion. -/
def cpChosenBinaryProduct
    (X Y : CoreflexivePairObj C) :
    ChosenBinaryProduct X Y where
  obj := cpProd X Y
  fst := cpFst X Y
  snd := cpSnd X Y
  lift f g := cpLift f g
  lift_fst := cpLift_fst_law
  lift_snd := cpLift_snd_law
  lift_uniq := cpLift_uniq_law

/-- The equalizer completion of a category with
chosen finite products has chosen finite
products. -/
instance cpHasChosenFiniteProducts :
    HasChosenFiniteProducts
      (CoreflexivePairObj C) where
  terminal := cpChosenTerminal
  product := cpChosenBinaryProduct

/-! ## Equalizers -/

section Equalizers

variable {X Y : CoreflexivePairObj C}
  (f g : X.src ⟶ Y.src)

/-- The equalizer object for two premorphisms
`f g : X.src ⟶ Y.src` in the free equalizer
completion. The source is `X.src`, the target is
`cfpProd X.tgt Y.tgt`, with section maps constructed
via `cfpLift`. -/
def cpEqualizerObj :
    CoreflexivePairObj C where
  src := X.src
  tgt := cfpProd X.tgt Y.tgt
  left :=
    cfpLift X.left (f ≫ Y.left)
  right :=
    cfpLift X.right (g ≫ Y.left)
  retract :=
    cfpFst X.tgt Y.tgt ≫ X.retract
  retract_left := by
    rw [← Category.assoc, cfpLift_fst,
      X.retract_left]
  retract_right := by
    rw [← Category.assoc, cfpLift_fst,
      X.retract_right]

/-- The inclusion `𝟙 X.src` is a premorphism from
the equalizer object to `X`. The witness for the
one-step relation is `cfpFst X.tgt Y.tgt`. -/
theorem cpEqualizerInclusion_isPremorphism :
    IsCPPremorphism (cpEqualizerObj f g) X
      (𝟙 X.src) := by
  unfold IsCPPremorphism cpEqualizerObj
  simp only [Category.id_comp]
  exact Relation.EqvGen.rel _ _
    ⟨cfpFst X.tgt Y.tgt,
      cfpLift_fst X.left (f ≫ Y.left),
      cfpLift_fst X.right (g ≫ Y.left)⟩

/-- The premorphisms `f` and `g` are related by
the coreflexive equivalence of the equalizer object.
The witness for the one-step relation is
`cfpSnd X.tgt Y.tgt ≫ Y.retract`. -/
theorem cpEqualizerObj_relates_f_g :
    CoreflexiveEqv (cpEqualizerObj f g) f g := by
  apply Relation.EqvGen.rel
  refine ⟨cfpSnd X.tgt Y.tgt ≫ Y.retract,
    ?_, ?_⟩
  · change cfpLift X.left (f ≫ Y.left) ≫
      cfpSnd X.tgt Y.tgt ≫ Y.retract = f
    rw [← Category.assoc, cfpLift_snd,
      Category.assoc, Y.retract_left,
      Category.comp_id]
  · change cfpLift X.right (g ≫ Y.left) ≫
      cfpSnd X.tgt Y.tgt ≫ Y.retract = g
    rw [← Category.assoc, cfpLift_snd,
      Category.assoc, Y.retract_left,
      Category.comp_id]

/-- The inclusion morphism in the quotient
category. -/
def cpEqualizerInclusion :
    CPMor (cpEqualizerObj f g) X :=
  Quotient.mk
    (cpPreMorSetoid (cpEqualizerObj f g) X)
    ⟨𝟙 X.src,
      cpEqualizerInclusion_isPremorphism f g⟩

/-- The equalizing condition: the inclusion
composed with `f` equals the inclusion composed
with `g`, as morphisms in the quotient category.
Since the inclusion is `𝟙`, composition yields `f`
and `g` which are related by one step in the
equalizer object's coreflexive equivalence. -/
theorem cpEqualizerInclusion_equalizes
    (hf : IsCPPremorphism X Y f)
    (hg : IsCPPremorphism X Y g) :
    cpComp (cpEqualizerInclusion f g)
      (Quotient.mk (cpPreMorSetoid X Y)
        ⟨f, hf⟩) =
    cpComp (cpEqualizerInclusion f g)
      (Quotient.mk (cpPreMorSetoid X Y)
        ⟨g, hg⟩) := by
  apply Quotient.sound
    (s := cpPreMorSetoid (cpEqualizerObj f g) Y)
  change CoreflexiveEqv (cpEqualizerObj f g)
    (𝟙 X.src ≫ f) (𝟙 X.src ≫ g)
  have h1 : (𝟙 X.src ≫ f : X.src ⟶ Y.src) =
    f := Category.id_comp f
  have h2 : (𝟙 X.src ≫ g : X.src ⟶ Y.src) =
    g := Category.id_comp g
  rw [h1, h2]
  exact cpEqualizerObj_relates_f_g f g

/-- Pre-composition distributes over `cfpLift` by
the universal property of the product. -/
theorem cfpLift_precomp
    {A B D E : C}
    (t : E ⟶ D) (f : D ⟶ A) (g : D ⟶ B) :
    t ≫ cfpLift f g =
      cfpLift (t ≫ f) (t ≫ g) := by
  apply cfpLift_uniq
  · rw [Category.assoc, cfpLift_fst]
  · rw [Category.assoc, cfpLift_snd]

/-- If `t : Z.src ⟶ X.src` is a premorphism from
`Z` to `X` and `t ≫ f` is equivalent to `t ≫ g`
under `Z`, then `t` is also a premorphism from `Z`
to the equalizer object.

The premorphism condition for `Z → E` requires
`CoreflexiveEqv Z (t ≫ E.left) (t ≫ E.right)`.
Since `E.left = cfpLift X.left (f ≫ Y.left)` and
`E.right = cfpLift X.right (g ≫ Y.left)`, we
decompose this using the cfpLift compatibility
lemmas. -/
theorem cpEqualizerFactorization_isPremorphism
    {Z : CoreflexivePairObj C}
    (t : Z.src ⟶ X.src)
    (ht : IsCPPremorphism Z X t)
    (heq : CoreflexiveEqv Z (t ≫ f) (t ≫ g)) :
    IsCPPremorphism Z (cpEqualizerObj f g) t := by
  unfold IsCPPremorphism cpEqualizerObj
  simp only
  rw [cfpLift_precomp, cfpLift_precomp]
  have assoc_fY :
      (t ≫ f) ≫ Y.left = t ≫ f ≫ Y.left :=
    Category.assoc t f Y.left
  have assoc_gY :
      (t ≫ g) ≫ Y.left = t ≫ g ≫ Y.left :=
    Category.assoc t g Y.left
  have postcomp_eq :
      CoreflexiveEqv Z
        (t ≫ f ≫ Y.left) (t ≫ g ≫ Y.left) := by
    rw [← assoc_fY, ← assoc_gY]
    exact CoreflexiveEqv_postcomp Z heq Y.left
  exact Relation.EqvGen.trans _ _ _
    (CoreflexiveEqv_cfpLift_left Z
      ht (t ≫ f ≫ Y.left))
    (CoreflexiveEqv_cfpLift_right Z
      (t ≫ X.right) postcomp_eq)

omit h in
/-- Extracting the coreflexive equivalence from
equality of quotient compositions. If two
compositions through the quotient are equal, the
underlying premorphism compositions are related. -/
theorem cpComp_eq_implies_eqv
    {Z : CoreflexivePairObj C}
    (t : Z.src ⟶ X.src)
    (ht : IsCPPremorphism Z X t)
    (hf : IsCPPremorphism X Y f)
    (hg : IsCPPremorphism X Y g)
    (heq :
      cpComp
        (Quotient.mk (cpPreMorSetoid Z X)
          ⟨t, ht⟩)
        (Quotient.mk (cpPreMorSetoid X Y)
          ⟨f, hf⟩) =
      cpComp
        (Quotient.mk (cpPreMorSetoid Z X)
          ⟨t, ht⟩)
        (Quotient.mk (cpPreMorSetoid X Y)
          ⟨g, hg⟩)) :
    CoreflexiveEqv Z (t ≫ f) (t ≫ g) := by
  have := Quotient.exact
    (s := cpPreMorSetoid Z Y) heq
  exact this

/-- The lift morphism for the equalizer universal
property: given a premorphism `t : Z → X` with
premorphism proof and equalizing condition, produce
the factorization `Z → E`. -/
def cpEqualizerLiftRaw
    {Z : CoreflexivePairObj C}
    (t : Z.src ⟶ X.src)
    (ht : IsCPPremorphism Z X t)
    (heq : CoreflexiveEqv Z (t ≫ f) (t ≫ g)) :
    CPMor Z (cpEqualizerObj f g) :=
  Quotient.mk
    (cpPreMorSetoid Z (cpEqualizerObj f g))
    ⟨t, cpEqualizerFactorization_isPremorphism
      f g t ht heq⟩

/-- The lift composed with inclusion gives back the
original morphism. -/
theorem cpEqualizerLiftRaw_fac
    {Z : CoreflexivePairObj C}
    (t : Z.src ⟶ X.src)
    (ht : IsCPPremorphism Z X t)
    (heq : CoreflexiveEqv Z (t ≫ f) (t ≫ g)) :
    cpComp (cpEqualizerLiftRaw f g t ht heq)
      (cpEqualizerInclusion f g) =
    Quotient.mk (cpPreMorSetoid Z X)
      ⟨t, ht⟩ := by
  apply Quotient.sound
    (s := cpPreMorSetoid Z X)
  change CoreflexiveEqv Z (t ≫ 𝟙 X.src) t
  have : (t ≫ 𝟙 X.src : Z.src ⟶ X.src) = t :=
    Category.comp_id t
  rw [this]
  exact Relation.EqvGen.refl _

/-- Uniqueness for the equalizer lift: if
`k ≫ inclusion = t`, then `k = lift t`. -/
theorem cpEqualizerLiftRaw_uniq
    {Z : CoreflexivePairObj C}
    (t : Z.src ⟶ X.src)
    (ht : IsCPPremorphism Z X t)
    (heq : CoreflexiveEqv Z (t ≫ f) (t ≫ g))
    (k : CPMor Z (cpEqualizerObj f g))
    (hk : cpComp k (cpEqualizerInclusion f g) =
      Quotient.mk (cpPreMorSetoid Z X)
        ⟨t, ht⟩) :
    k = cpEqualizerLiftRaw f g t ht heq := by
  revert hk
  apply Quotient.inductionOn
    (motive := fun (q :
      CPMor Z (cpEqualizerObj f g)) =>
      cpComp q (cpEqualizerInclusion f g) =
        Quotient.mk _ ⟨t, ht⟩ →
      q = cpEqualizerLiftRaw f g t ht heq)
    k
  intro k_raw hk_raw
  apply Quotient.sound
    (s := cpPreMorSetoid Z (cpEqualizerObj f g))
  have := Quotient.exact
    (s := cpPreMorSetoid Z X) hk_raw
  change CoreflexiveEqv Z k_raw.val t
  change CoreflexiveEqv Z (k_raw.val ≫ 𝟙 X.src) t
    at this
  have comp_id_eq :
      (k_raw.val ≫ 𝟙 X.src : Z.src ⟶ X.src) =
      k_raw.val := Category.comp_id k_raw.val
  rw [comp_id_eq] at this
  exact this

omit h in
/-- The coreflexive equivalence preserves the
equalizing condition: if `t₁ ~ t₂` and `t₁`
satisfies the equalizing condition, then `t₂` does
too. -/
theorem cpEqualizer_eqv_preserves_equalizing
    {Z : CoreflexivePairObj C}
    {t₁ t₂ : Z.src ⟶ X.src}
    (hrel : CoreflexiveEqv Z t₁ t₂)
    (heq₁ : CoreflexiveEqv Z
      (t₁ ≫ f) (t₁ ≫ g)) :
    CoreflexiveEqv Z (t₂ ≫ f) (t₂ ≫ g) :=
  Relation.EqvGen.trans _ _ _
    (CoreflexiveEqv_comp_right Z
      (Relation.EqvGen.symm _ _ hrel) f)
    (Relation.EqvGen.trans _ _ _ heq₁
      (CoreflexiveEqv_comp_right Z hrel g))

/-- The equalizer lift function on representatives.
Produces a quotient morphism `Z → E` from a
premorphism `t : Z → X` with premorphism proof and
equalizing condition. -/
def cpEqualizerLiftOfRep
    {Z : CoreflexivePairObj C}
    (t : Z.src ⟶ X.src)
    (ht : IsCPPremorphism Z X t)
    (heq : CoreflexiveEqv Z (t ≫ f) (t ≫ g)) :
    CPMor Z (cpEqualizerObj f g) :=
  Quotient.mk
    (cpPreMorSetoid Z (cpEqualizerObj f g))
    ⟨t, cpEqualizerFactorization_isPremorphism
      f g t ht heq⟩

/-- The lift on representatives respects the
coreflexive equivalence. -/
theorem cpEqualizerLiftOfRep_resp
    {Z : CoreflexivePairObj C}
    {t₁ t₂ : Z.src ⟶ X.src}
    (ht₁ : IsCPPremorphism Z X t₁)
    (ht₂ : IsCPPremorphism Z X t₂)
    (heq₁ : CoreflexiveEqv Z (t₁ ≫ f) (t₁ ≫ g))
    (heq₂ : CoreflexiveEqv Z (t₂ ≫ f) (t₂ ≫ g))
    (hrel : CoreflexiveEqv Z t₁ t₂) :
    cpEqualizerLiftOfRep f g t₁ ht₁ heq₁ =
      cpEqualizerLiftOfRep f g t₂ ht₂ heq₂ := by
  apply Quotient.sound
    (s := cpPreMorSetoid Z (cpEqualizerObj f g))
  exact hrel

/-- The Fork for the equalizer. -/
def cpEqualizerFork
    (hf : IsCPPremorphism X Y f)
    (hg : IsCPPremorphism X Y g) :
    Limits.Fork
      (show X ⟶ Y from ⟦⟨f, hf⟩⟧)
      (show X ⟶ Y from ⟦⟨g, hg⟩⟧) :=
  Limits.Fork.ofι
    (cpEqualizerInclusion f g)
    (cpEqualizerInclusion_equalizes f g hf hg)

/-- The lift function for the equalizer. Given a
quotient morphism `s.ι : Z ⟶ X` with the equalizing
condition, produce the factorization `Z ⟶ E`.

We use `Quotient.liftOn` on `s.ι` to extract a
representative, then apply `cpEqualizerLiftOfRep`.
The equalizing condition for the representative is
derived from the quotient-level condition via
`cpComp_eq_implies_eqv`. Well-definedness follows
from `cpEqualizerLiftOfRep_resp`. -/
def cpEqualizerLift
    (hf : IsCPPremorphism X Y f)
    (hg : IsCPPremorphism X Y g)
    {Z : CoreflexivePairObj C}
    (s_ι : CPMor Z X)
    (heq : cpComp s_ι
      (show X ⟶ Y from ⟦⟨f, hf⟩⟧) =
      cpComp s_ι
      (show X ⟶ Y from ⟦⟨g, hg⟩⟧)) :
    CPMor Z (cpEqualizerObj f g) :=
  let fq := (show X ⟶ Y from ⟦⟨f, hf⟩⟧)
  let gq := (show X ⟶ Y from ⟦⟨g, hg⟩⟧)
  (Quot.hrecOn
    (motive := fun (q : CPMor Z X) =>
      cpComp q fq = cpComp q gq →
      CPMor Z (cpEqualizerObj f g))
    s_ι
    (fun t_raw heq_raw =>
      cpEqualizerLiftOfRep f g t_raw.val
        t_raw.property
        (cpComp_eq_implies_eqv f g
          t_raw.val t_raw.property hf hg
          heq_raw))
    (fun t₁ t₂ hrel => by
      apply Function.hfunext
      · exact congrArg (fun q =>
          cpComp q fq = cpComp q gq)
          (Quotient.sound
            (s := cpPreMorSetoid Z X) hrel)
      · intro h₁ h₂ _
        exact heq_of_eq
          (cpEqualizerLiftOfRep_resp f g
            t₁.property t₂.property _ _ hrel)))
  heq

/-- The lift composes with inclusion to give the
original morphism. -/
theorem cpEqualizerLift_fac
    (hf : IsCPPremorphism X Y f)
    (hg : IsCPPremorphism X Y g)
    {Z : CoreflexivePairObj C}
    (s_ι : CPMor Z X)
    (heq : cpComp s_ι
      (show X ⟶ Y from ⟦⟨f, hf⟩⟧) =
      cpComp s_ι
      (show X ⟶ Y from ⟦⟨g, hg⟩⟧)) :
    cpComp
      (cpEqualizerLift f g hf hg s_ι heq)
      (cpEqualizerInclusion f g) = s_ι := by
  revert heq
  apply Quotient.inductionOn
    (motive := fun (q : CPMor Z X) =>
      (heq : cpComp q _ = cpComp q _) →
      cpComp
        (cpEqualizerLift f g hf hg q heq)
        (cpEqualizerInclusion f g) = q)
    s_ι
  intro t_raw heq_raw
  change cpComp
    (cpEqualizerLiftOfRep f g t_raw.val
      t_raw.property
      (cpComp_eq_implies_eqv f g
        t_raw.val t_raw.property hf hg
        heq_raw))
    (cpEqualizerInclusion f g) = ⟦t_raw⟧
  exact cpEqualizerLiftRaw_fac f g t_raw.val
    t_raw.property
    (cpComp_eq_implies_eqv f g
      t_raw.val t_raw.property hf hg
      heq_raw)

/-- Uniqueness of the lift: if `m ≫ inclusion = s_ι`,
then `m = lift s_ι`. -/
theorem cpEqualizerLift_uniq
    (hf : IsCPPremorphism X Y f)
    (hg : IsCPPremorphism X Y g)
    {Z : CoreflexivePairObj C}
    (s_ι : CPMor Z X)
    (heq : cpComp s_ι
      (show X ⟶ Y from ⟦⟨f, hf⟩⟧) =
      cpComp s_ι
      (show X ⟶ Y from ⟦⟨g, hg⟩⟧))
    (m : CPMor Z (cpEqualizerObj f g))
    (hm : cpComp m
      (cpEqualizerInclusion f g) = s_ι) :
    m = cpEqualizerLift f g hf hg s_ι heq := by
  revert heq hm
  apply Quotient.inductionOn
    (motive := fun (q : CPMor Z X) =>
      (heq : cpComp q _ = cpComp q _) →
      cpComp m (cpEqualizerInclusion f g) = q →
      m = cpEqualizerLift f g hf hg q heq)
    s_ι
  intro t_raw heq_raw hm_raw
  have heq_rep := cpComp_eq_implies_eqv f g
    t_raw.val t_raw.property hf hg heq_raw
  change m = cpEqualizerLiftOfRep f g
    t_raw.val t_raw.property heq_rep
  exact cpEqualizerLiftRaw_uniq f g t_raw.val
    t_raw.property heq_rep m hm_raw

/-- The IsLimit witness for the equalizer fork. -/
def cpEqualizerForkIsLimit
    (hf : IsCPPremorphism X Y f)
    (hg : IsCPPremorphism X Y g) :
    Limits.IsLimit
      (cpEqualizerFork f g hf hg) :=
  Limits.Fork.IsLimit.mk _
    (fun s =>
      cpEqualizerLift f g hf hg s.ι s.condition)
    (fun s =>
      cpEqualizerLift_fac f g hf hg
        s.ι s.condition)
    (fun s m hm =>
      cpEqualizerLift_uniq f g hf hg
        s.ι s.condition m hm)

/-- Existence of the equalizer for a specific pair
of premorphism representatives. -/
theorem cpHasEqualizer_of_reps
    (hf : IsCPPremorphism X Y f)
    (hg : IsCPPremorphism X Y g) :
    Limits.HasEqualizer
      (show X ⟶ Y from ⟦⟨f, hf⟩⟧)
      (show X ⟶ Y from ⟦⟨g, hg⟩⟧) :=
  Limits.HasLimit.mk
    ⟨cpEqualizerFork f g hf hg,
      cpEqualizerForkIsLimit f g hf hg⟩

end Equalizers

/-- Every parallel pair in the free equalizer
completion has an equalizer. -/
instance cpHasEqualizer
    {X Y : CoreflexivePairObj C}
    (f_q g_q : X ⟶ Y) :
    Limits.HasEqualizer f_q g_q := by
  revert f_q g_q
  apply Quotient.ind
  intro f_raw
  apply Quotient.ind
  intro g_raw
  exact cpHasEqualizer_of_reps _ _
    f_raw.property g_raw.property

/-- The free equalizer completion has all
equalizers. -/
instance cpHasEqualizers :
    Limits.HasEqualizers
      (CoreflexivePairObj C) :=
  Limits.hasEqualizers_of_hasLimit_parallelPair
    (CoreflexivePairObj C)

/-- The free equalizer completion of a category
with chosen finite products has all finite
limits. -/
instance cpHasFiniteLimits :
    Limits.HasFiniteLimits
      (CoreflexivePairObj C) :=
  Limits.hasFiniteLimits_of_hasEqualizers_and_finite_products

end GebLean
