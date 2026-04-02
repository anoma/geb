import GebLean.EqualizerCompletionLimits
import GebLean.LawvereBT

/-!
# PBTO Preservation in the Equalizer Completion

Generic lemmas showing that a parameterized binary
tree object (PBTO) in a category with finite products
is preserved by the free equalizer completion.
-/

namespace GebLean

open CategoryTheory

universe v u

variable {C : Type u} [Category.{v} C]
  [h : HasChosenFiniteProducts C]
  [p : HasPBTO C]

theorem cfpInsertSnd_cfpMap
    {A B : C} (k : B ⟶ A)
    (c : cfpTerminal ⟶ p.T) :
    cfpInsertSnd c B ≫
      cfpMap k (𝟙 p.T) =
    k ≫ cfpInsertSnd c A := by
  unfold cfpInsertSnd
  rw [cfpLift_cfpMap, cfpLift_precomp]
  congr 1
  · rw [Category.id_comp, Category.comp_id]
  · rw [Category.comp_id]
    have : k ≫ cfpTerminalFrom A =
        cfpTerminalFrom B :=
      h.terminal.uniq _
    rw [← this, Category.assoc]

omit p in
theorem cfpLiftAssoc_postcomp
    {A B D E E' : C}
    (f : cfpProd A B ⟶ E)
    (g : cfpProd A D ⟶ E)
    (q : E ⟶ E') :
    cfpLiftAssoc f g ≫ cfpMap q q =
    cfpLiftAssoc (f ≫ q) (g ≫ q) := by
  unfold cfpLiftAssoc
  rw [cfpLift_cfpMap]
  congr 1 <;> rw [Category.assoc]

theorem cfpMap_β_naturality
    {A B : C} (k : B ⟶ A) :
    cfpMap (𝟙 B) p.β ≫
      cfpMap k (𝟙 p.T) =
    cfpMap k (𝟙 (cfpProd p.T p.T)) ≫
      cfpMap (𝟙 A) p.β := by
  rw [cfpMap_comp, cfpMap_comp,
    Category.id_comp, Category.comp_id,
    Category.comp_id, Category.id_comp]

omit p in
theorem cfpMap_cfpAssocFst
    {A A' B D : C} (k : A' ⟶ A) :
    cfpMap k (𝟙 (cfpProd B D)) ≫
      cfpAssocFst A B D =
    cfpAssocFst A' B D ≫
      cfpMap k (𝟙 B) := by
  unfold cfpAssocFst
  rw [cfpLift_precomp, cfpLift_cfpMap]
  congr 1
  · rw [cfpMap_fst]
  · rw [← Category.assoc, cfpMap_snd,
      Category.comp_id, Category.comp_id]

omit p in
theorem cfpMap_cfpAssocSnd
    {A A' B D : C} (k : A' ⟶ A) :
    cfpMap k (𝟙 (cfpProd B D)) ≫
      cfpAssocSnd A B D =
    cfpAssocSnd A' B D ≫
      cfpMap k (𝟙 D) := by
  unfold cfpAssocSnd
  rw [cfpLift_precomp, cfpLift_cfpMap]
  congr 1
  · rw [cfpMap_fst]
  · rw [← Category.assoc, cfpMap_snd,
      Category.comp_id, Category.comp_id]

omit p in
theorem cfpLiftAssoc_precomp
    {A A' B D E : C}
    (k : A' ⟶ A)
    (f : cfpProd A B ⟶ E)
    (g : cfpProd A D ⟶ E) :
    cfpMap k (𝟙 (cfpProd B D)) ≫
      cfpLiftAssoc f g =
    cfpLiftAssoc
      (cfpMap k (𝟙 B) ≫ f)
      (cfpMap k (𝟙 D) ≫ g) := by
  unfold cfpLiftAssoc
  rw [cfpLift_precomp]
  congr 1 <;>
    rw [← Category.assoc]
  · rw [cfpMap_cfpAssocFst, Category.assoc]
  · rw [cfpMap_cfpAssocSnd, Category.assoc]

theorem elim_naturality
    {A B X : C}
    (k : B ⟶ A)
    (f : A ⟶ X) (g : cfpProd X X ⟶ X) :
    cfpMap k (𝟙 p.T) ≫ p.elim f g =
    p.elim (k ≫ f) g := by
  exact p.elim_uniq (k ≫ f) g
    (cfpMap k (𝟙 p.T) ≫ p.elim f g)
    (by
      rw [← Category.assoc,
        cfpInsertSnd_cfpMap,
        Category.assoc, p.elim_ℓ])
    (by
      rw [← Category.assoc,
        cfpMap_β_naturality,
        Category.assoc, p.elim_β,
        ← Category.assoc,
        cfpLiftAssoc_precomp])

theorem elim_algebra_morphism
    {A X X' : C}
    (f : A ⟶ X) (g : cfpProd X X ⟶ X)
    (q : X ⟶ X')
    (w : cfpProd X' X' ⟶ X')
    (hw : cfpMap q q ≫ w = g ≫ q) :
    p.elim f g ≫ q = p.elim (f ≫ q) w := by
  exact p.elim_uniq (f ≫ q) w
    (p.elim f g ≫ q)
    (by
      rw [← Category.assoc, p.elim_ℓ])
    (by
      rw [← Category.assoc, p.elim_β,
        Category.assoc, ← hw,
        ← Category.assoc,
        cfpLiftAssoc_postcomp])

theorem elim_base_relStep
    (A : CoreflexivePairObj C)
    {X : C}
    {a b : A.src ⟶ X}
    (s : cfpProd X X ⟶ X)
    (hab : CoreflexiveRelStep A a b) :
    CoreflexiveRelStep
      (cpProd A (cpEmbed p.T))
      (p.elim a s) (p.elim b s) := by
  obtain ⟨w, hw_left, hw_right⟩ := hab
  exact ⟨p.elim w s, by
    rw [show (cpProd A (cpEmbed p.T)).left
      = cfpMap A.left (𝟙 p.T) from rfl,
      elim_naturality, hw_left],
    by rw [show (cpProd A (cpEmbed p.T)).right
      = cfpMap A.right (𝟙 p.T) from rfl,
      elim_naturality, hw_right]⟩

theorem elim_base_eqvGen
    (A : CoreflexivePairObj C)
    {X : C}
    {a b : A.src ⟶ X}
    (s : cfpProd X X ⟶ X)
    (hab : CoreflexiveEqv A a b) :
    CoreflexiveEqv
      (cpProd A (cpEmbed p.T))
      (p.elim a s) (p.elim b s) := by
  unfold CoreflexiveEqv at hab ⊢
  induction hab with
  | rel _ _ hr =>
    exact Relation.EqvGen.rel _ _
      (elim_base_relStep A s hr)
  | refl _ => exact Relation.EqvGen.refl _
  | symm _ _ _ ih =>
    exact Relation.EqvGen.symm _ _ ih
  | trans _ _ _ _ _ ih1 ih2 =>
    exact Relation.EqvGen.trans _ _ _ ih1 ih2

theorem elim_isPremorphism_oneStep
    (A X : CoreflexivePairObj C)
    {f : A.src ⟶ X.src}
    {g : cfpProd X.src X.src ⟶ X.src}
    (w_f : A.tgt ⟶ X.tgt)
    (hw_f_left :
      A.left ≫ w_f = f ≫ X.left)
    (hw_f_right :
      A.right ≫ w_f = f ≫ X.right)
    (w_g : cfpProd X.tgt X.tgt ⟶ X.tgt)
    (hw_g_left :
      cfpMap X.left X.left ≫ w_g =
      g ≫ X.left)
    (hw_g_right :
      cfpMap X.right X.right ≫ w_g =
      g ≫ X.right) :
    CoreflexiveRelStep
      (cpProd A (cpEmbed p.T))
      (p.elim f g ≫ X.left)
      (p.elim f g ≫ X.right) := by
  exact ⟨p.elim w_f w_g, by
    rw [show (cpProd A (cpEmbed p.T)).left
      = cfpMap A.left (𝟙 p.T) from rfl,
      elim_naturality, hw_f_left,
      elim_algebra_morphism f g X.left w_g
        hw_g_left],
    by rw [show (cpProd A (cpEmbed p.T)).right
      = cfpMap A.right (𝟙 p.T) from rfl,
      elim_naturality, hw_f_right,
      elim_algebra_morphism f g X.right w_g
        hw_g_right]⟩

/--
The reflexivity witness for a section `q` of a
coreflexive pair `X`, applied to a step function
`g : cfpProd X.src X.src ⟶ X.src`.  This is
`cfpMap X.retract X.retract ≫ g ≫ q`, which maps
`cfpProd X.tgt X.tgt ⟶ X.tgt`.
-/
def cpReflWitness
    (X : CoreflexivePairObj C)
    (g : cfpProd X.src X.src ⟶ X.src)
    (q : X.src ⟶ X.tgt) :
    cfpProd X.tgt X.tgt ⟶ X.tgt :=
  cfpMap X.retract X.retract ≫ g ≫ q

omit p in
theorem cpReflWitness_spec
    (X : CoreflexivePairObj C)
    (g : cfpProd X.src X.src ⟶ X.src)
    (q : X.src ⟶ X.tgt)
    (hq : q ≫ X.retract = 𝟙 X.src) :
    cfpMap q q ≫ cpReflWitness X g q =
      g ≫ q := by
  unfold cpReflWitness
  have hqr : cfpMap q q ≫
      cfpMap X.retract X.retract =
      cfpMap (q ≫ X.retract) (q ≫ X.retract) :=
    cfpMap_comp q q X.retract X.retract
  have hid : cfpMap (q ≫ X.retract)
      (q ≫ X.retract) =
      𝟙 (cfpProd X.src X.src) := by
    rw [hq]; exact cfpMap_id X.src X.src
  rw [← Category.assoc, hqr, hid,
    Category.id_comp]

omit p in
theorem cpReflWitness_left_spec
    (X : CoreflexivePairObj C)
    (g : cfpProd X.src X.src ⟶ X.src) :
    cfpMap X.left X.left ≫
      cpReflWitness X g X.left = g ≫ X.left :=
  cpReflWitness_spec X g X.left X.retract_left

omit p in
theorem cpReflWitness_right_spec
    (X : CoreflexivePairObj C)
    (g : cfpProd X.src X.src ⟶ X.src) :
    cfpMap X.right X.right ≫
      cpReflWitness X g X.right = g ≫ X.right :=
  cpReflWitness_spec X g X.right X.retract_right

theorem elim_left_via_refl
    {A : C}
    (X : CoreflexivePairObj C)
    (f : A ⟶ X.src)
    (g : cfpProd X.src X.src ⟶ X.src) :
    p.elim f g ≫ X.left =
    p.elim (f ≫ X.left)
      (cpReflWitness X g X.left) :=
  elim_algebra_morphism f g X.left
    (cpReflWitness X g X.left)
    (cpReflWitness_left_spec X g)

theorem elim_right_via_refl
    {A : C}
    (X : CoreflexivePairObj C)
    (f : A ⟶ X.src)
    (g : cfpProd X.src X.src ⟶ X.src) :
    p.elim f g ≫ X.right =
    p.elim (f ≫ X.right)
      (cpReflWitness X g X.right) :=
  elim_algebra_morphism f g X.right
    (cpReflWitness X g X.right)
    (cpReflWitness_right_spec X g)

theorem elim_base_change
    (A X : CoreflexivePairObj C)
    {f : A.src ⟶ X.src}
    (hf : IsCPPremorphism A X f)
    (w : cfpProd X.tgt X.tgt ⟶ X.tgt) :
    CoreflexiveEqv
      (cpProd A (cpEmbed p.T))
      (p.elim (f ≫ X.left) w)
      (p.elim (f ≫ X.right) w) :=
  elim_base_eqvGen A w hf

/--
If the step function `g` has a one-step premorphism
witness (a single `w_g` satisfying both projection
equations), then the fold `p.elim f g` satisfies
the premorphism condition using `w_g` as the common
step function for both reductions.
-/
theorem elim_isPremorphism_of_oneStep_step
    (A X : CoreflexivePairObj C)
    {f : A.src ⟶ X.src}
    (hf : IsCPPremorphism A X f)
    {g : cfpProd X.src X.src ⟶ X.src}
    (w_g : cfpProd X.tgt X.tgt ⟶ X.tgt)
    (hw_g_left :
      cfpMap X.left X.left ≫ w_g =
      g ≫ X.left)
    (hw_g_right :
      cfpMap X.right X.right ≫ w_g =
      g ≫ X.right) :
    IsCPPremorphism
      (cpProd A (cpEmbed p.T)) X
      (p.elim f g) := by
  unfold IsCPPremorphism
  rw [elim_algebra_morphism f g X.left
      w_g hw_g_left,
    elim_algebra_morphism f g X.right
      w_g hw_g_right]
  exact elim_base_eqvGen A w_g hf

/--
If the step function `g` has a one-step premorphism
witness (as a `CoreflexiveRelStep`), the fold
`p.elim f g` is a premorphism.  The one-step
witness is exactly the `w_g` needed by
`elim_isPremorphism_of_oneStep_step`.
-/
theorem elim_isPremorphism_of_relStep_step
    (A X : CoreflexivePairObj C)
    {f : A.src ⟶ X.src}
    (hf : IsCPPremorphism A X f)
    {g : cfpProd X.src X.src ⟶ X.src}
    (hg_step :
      CoreflexiveRelStep (cpProd X X)
        (g ≫ X.left) (g ≫ X.right)) :
    IsCPPremorphism
      (cpProd A (cpEmbed p.T)) X
      (p.elim f g) := by
  obtain ⟨w_g, hw_left, hw_right⟩ := hg_step
  exact elim_isPremorphism_of_oneStep_step
    A X hf w_g
    (show cfpMap X.left X.left ≫ w_g =
      g ≫ X.left from hw_left)
    (show cfpMap X.right X.right ≫ w_g =
      g ≫ X.right from hw_right)

omit p in
theorem cpReflWitness_retract_left
    (X : CoreflexivePairObj C)
    (g : cfpProd X.src X.src ⟶ X.src) :
    cpReflWitness X g X.left ≫ X.retract ≫
      X.left =
    cpReflWitness X g X.left := by
  unfold cpReflWitness
  rw [Category.assoc, Category.assoc,
    ← Category.assoc X.left X.retract _,
    X.retract_left, Category.id_comp]

omit p in
theorem cpReflWitness_retract_right
    (X : CoreflexivePairObj C)
    (g : cfpProd X.src X.src ⟶ X.src) :
    cpReflWitness X g X.right ≫ X.retract ≫
      X.right =
    cpReflWitness X g X.right := by
  unfold cpReflWitness
  rw [Category.assoc, Category.assoc,
    ← Category.assoc X.right X.retract _,
    X.retract_right, Category.id_comp]

omit p in
theorem cpReflWitness_cross_left_right
    (X : CoreflexivePairObj C)
    (g : cfpProd X.src X.src ⟶ X.src) :
    cpReflWitness X g X.left ≫ X.retract ≫
      X.right =
    cpReflWitness X g X.right := by
  unfold cpReflWitness
  rw [Category.assoc, Category.assoc,
    ← Category.assoc X.left X.retract _,
    X.retract_left, Category.id_comp]

omit p in
theorem cpReflWitness_cross_right_left
    (X : CoreflexivePairObj C)
    (g : cfpProd X.src X.src ⟶ X.src) :
    cpReflWitness X g X.right ≫ X.retract ≫
      X.left =
    cpReflWitness X g X.left := by
  unfold cpReflWitness
  rw [Category.assoc, Category.assoc,
    ← Category.assoc X.right X.retract _,
    X.retract_right, Category.id_comp]

omit p in
theorem cpReflWitness_retract
    (X : CoreflexivePairObj C)
    (g : cfpProd X.src X.src ⟶ X.src)
    (q : X.src ⟶ X.tgt)
    (hq : q ≫ X.retract = 𝟙 X.src) :
    (cpReflWitness X g q) ≫ X.retract =
    cfpMap X.retract X.retract ≫ g := by
  unfold cpReflWitness
  rw [Category.assoc, Category.assoc,
    show q ≫ X.retract = 𝟙 X.src from hq,
    Category.comp_id]

/--
The fold via a reflexivity witness retracts back
to the original fold: for any section `q` of `X`,
`p.elim (f ≫ q) (cpReflWitness X g q) ≫ X.retract
= p.elim f g`.
-/
theorem elim_refl_retract
    {A : C}
    (X : CoreflexivePairObj C)
    (f : A ⟶ X.src)
    (g : cfpProd X.src X.src ⟶ X.src)
    (q : X.src ⟶ X.tgt)
    (hq : q ≫ X.retract = 𝟙 X.src) :
    p.elim (f ≫ q)
      (cpReflWitness X g q) ≫ X.retract =
    p.elim f g := by
  rw [elim_algebra_morphism
    (f ≫ q) (cpReflWitness X g q)
    X.retract
    g
    (by
      rw [cpReflWitness_retract X g q hq])]
  congr 1
  rw [Category.assoc, hq, Category.comp_id]

omit p in
theorem cpReflWitness_cross_alg_morphism
    (X : CoreflexivePairObj C)
    (g : cfpProd X.src X.src ⟶ X.src)
    (q₁ q₂ : X.src ⟶ X.tgt)
    (hq₁ : q₁ ≫ X.retract = 𝟙 X.src)
    (hq₂ : q₂ ≫ X.retract = 𝟙 X.src) :
    cfpMap (X.retract ≫ q₂)
      (X.retract ≫ q₂) ≫
      cpReflWitness X g q₂ =
    cpReflWitness X g q₁ ≫
      (X.retract ≫ q₂) := by
  unfold cpReflWitness
  have lhs_eq :
      cfpMap (X.retract ≫ q₂)
        (X.retract ≫ q₂) ≫
        cfpMap X.retract X.retract ≫
        g ≫ q₂ =
      cfpMap X.retract X.retract ≫
        g ≫ q₂ := by
    rw [← Category.assoc
      (cfpMap (X.retract ≫ q₂)
        (X.retract ≫ q₂))
      (cfpMap X.retract X.retract)
      (g ≫ q₂),
      cfpMap_comp]
    congr 2 <;>
      rw [Category.assoc, hq₂,
        Category.comp_id]
  have rhs_eq :
      (cfpMap X.retract X.retract ≫
        g ≫ q₁) ≫
        (X.retract ≫ q₂) =
      cfpMap X.retract X.retract ≫
        g ≫ q₂ := by
    rw [Category.assoc, Category.assoc,
      ← Category.assoc q₁ X.retract q₂,
      hq₁, Category.id_comp]
  rw [lhs_eq, rhs_eq]

/--
The fold via a reflexivity witness, post-composed
with `X.retract ≫ q₂`, equals the fold via the
reflexivity witness for `q₂`.
-/
theorem elim_cross_retract
    {A : C}
    (X : CoreflexivePairObj C)
    (f : A ⟶ X.src)
    (g : cfpProd X.src X.src ⟶ X.src)
    (q₁ q₂ : X.src ⟶ X.tgt)
    (hq₁ : q₁ ≫ X.retract = 𝟙 X.src)
    (hq₂ : q₂ ≫ X.retract = 𝟙 X.src) :
    p.elim (f ≫ q₁)
      (cpReflWitness X g q₁) ≫
      (X.retract ≫ q₂) =
    p.elim (f ≫ q₂)
      (cpReflWitness X g q₂) := by
  rw [elim_algebra_morphism
    (f ≫ q₁) (cpReflWitness X g q₁)
    (X.retract ≫ q₂)
    (cpReflWitness X g q₂)
    (cpReflWitness_cross_alg_morphism
      X g q₁ q₂ hq₁ hq₂)]
  congr 1
  rw [Category.assoc,
    ← Category.assoc q₁ X.retract q₂,
    hq₁, Category.id_comp]

end GebLean
