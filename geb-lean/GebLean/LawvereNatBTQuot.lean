import GebLean.LawvereNatBT
import GebLean.Utilities.ComputableLimits
import Mathlib.CategoryTheory.Category.Basic

/-!
# Quotient Category for `LawvereNatBT`

`NatBTMorN` tuples quotiented by extensional equality of
interpretations.  Subsequent tasks build the `NatBTMorNQuo`
quotient type, identity and composition, the category instance
`LawvereNatBTCat`, and the `HasChosenFiniteProducts`
structure.

**Version note**: this file operates on the *bounded* variant of
the two-sort theory. The quotient construction uses morphisms with
bounded `foldBTNat` and `foldBTBT` operations. The two-stage
equivalence `LawvereERCat ≃ LawvereNatBT_bounded ≃
LawvereNatBT_ramified` is documented in
`docs/superpowers/specs/2026-04-18-lawvere-natbt-two-stage-design.md`.
-/

namespace GebLean

/-- Extensional equality of `NatBTMorN` tuples: two tuples are
related iff their interpretations agree on every domain context. -/
def natBTMorNRel (nm nm' : ℕ × ℕ) :
    NatBTMorN nm nm' → NatBTMorN nm nm' → Prop :=
  fun f g => ∀ (ctxN : Fin nm.1 → ℕ) (ctxB : Fin nm.2 → BTL),
    f.interp ctxN ctxB = g.interp ctxN ctxB

instance natBTMorNSetoid (nm nm' : ℕ × ℕ) :
    Setoid (NatBTMorN nm nm') where
  r := natBTMorNRel nm nm'
  iseqv :=
    ⟨ fun _ _ _ => rfl,
      fun h c d => (h c d).symm,
      fun h₁ h₂ c d => (h₁ c d).trans (h₂ c d) ⟩

/-- `NatBTMorN` tuples modulo extensional equivalence. -/
def NatBTMorNQuo (nm nm' : ℕ × ℕ) : Type :=
  Quotient (natBTMorNSetoid nm nm')

/-- Identity class: `NatBTMorN.id` packaged into the quotient. -/
def NatBTMorNQuo.id (nm : ℕ × ℕ) : NatBTMorNQuo nm nm :=
  Quotient.mk _ (NatBTMorN.id nm)

/-- Composition lifted through the quotient: extensional
equivalence is preserved by substitution. -/
def NatBTMorNQuo.comp {nm nm' nm'' : ℕ × ℕ}
    (f : NatBTMorNQuo nm nm') (g : NatBTMorNQuo nm' nm'') :
    NatBTMorNQuo nm nm'' :=
  Quotient.liftOn₂ f g
    (fun a b => Quotient.mk _ (NatBTMorN.comp a b))
    (fun a₁ b₁ a₂ b₂ h₁ h₂ => by
      apply Quotient.sound
      intro ctxN ctxB
      simp only [NatBTMorN.interp_comp]
      rw [h₁ ctxN ctxB]
      exact h₂ _ _)

theorem NatBTMorNQuo.id_comp {nm nm' : ℕ × ℕ}
    (f : NatBTMorNQuo nm nm') :
    NatBTMorNQuo.comp (NatBTMorNQuo.id nm) f = f := by
  refine Quotient.inductionOn f ?_
  intro a
  apply Quotient.sound
  intro ctxN ctxB
  simp

theorem NatBTMorNQuo.comp_id {nm nm' : ℕ × ℕ}
    (f : NatBTMorNQuo nm nm') :
    NatBTMorNQuo.comp f (NatBTMorNQuo.id nm') = f := by
  refine Quotient.inductionOn f ?_
  intro a
  apply Quotient.sound
  intro ctxN ctxB
  simp

theorem NatBTMorNQuo.assoc
    {nm nm' nm'' nm''' : ℕ × ℕ}
    (f : NatBTMorNQuo nm nm')
    (g : NatBTMorNQuo nm' nm'')
    (h : NatBTMorNQuo nm'' nm''') :
    NatBTMorNQuo.comp (NatBTMorNQuo.comp f g) h =
      NatBTMorNQuo.comp f (NatBTMorNQuo.comp g h) := by
  refine Quotient.inductionOn₃ f g h ?_
  intro a b c
  apply Quotient.sound
  intro ctxN ctxB
  simp

open CategoryTheory

/-- Carrier type for the two-sort base category: pairs
`(n, m) : ℕ × ℕ` interpreted as `ℕⁿ × BTᵐ`. -/
def LawvereNatBTCat : Type := ℕ × ℕ

instance : CategoryStruct LawvereNatBTCat where
  Hom nm nm' := NatBTMorNQuo nm nm'
  id := NatBTMorNQuo.id
  comp := NatBTMorNQuo.comp

instance : Category LawvereNatBTCat where
  id_comp := NatBTMorNQuo.id_comp
  comp_id := NatBTMorNQuo.comp_id
  assoc := fun f g h => NatBTMorNQuo.assoc f g h

/-- Terminal class: `NatBTMorN.terminal` in the quotient. -/
def NatBTMorNQuo.terminal (nm : ℕ × ℕ) :
    NatBTMorNQuo nm (0, 0) :=
  Quotient.mk _ (NatBTMorN.terminal nm)

/-- First projection class in the quotient. -/
def NatBTMorNQuo.fst {nm₁ nm₂ : ℕ × ℕ} :
    NatBTMorNQuo (nm₁.1 + nm₂.1, nm₁.2 + nm₂.2) nm₁ :=
  Quotient.mk _ (NatBTMorN.fst (nm₁ := nm₁) (nm₂ := nm₂))

/-- Second projection class in the quotient. -/
def NatBTMorNQuo.snd {nm₁ nm₂ : ℕ × ℕ} :
    NatBTMorNQuo (nm₁.1 + nm₂.1, nm₁.2 + nm₂.2) nm₂ :=
  Quotient.mk _ (NatBTMorN.snd (nm₁ := nm₁) (nm₂ := nm₂))

/-- Pairing in the quotient, lifted via `Quotient.lift₂`. -/
def NatBTMorNQuo.pair {nm nm₁ nm₂ : ℕ × ℕ}
    (f : NatBTMorNQuo nm nm₁) (g : NatBTMorNQuo nm nm₂) :
    NatBTMorNQuo nm (nm₁.1 + nm₂.1, nm₁.2 + nm₂.2) :=
  Quotient.liftOn₂ f g
    (fun a b => Quotient.mk _ (NatBTMorN.pair a b))
    (fun a₁ b₁ a₂ b₂ h₁ h₂ => by
      apply Quotient.sound
      intro ctxN ctxB
      simp only [NatBTMorN.interp_pair]
      apply Prod.ext
      · funext i
        refine Fin.addCases (fun j => ?_) (fun j => ?_) i
        · simp only [Fin.addCases_left]
          exact congrFun
            (congrArg Prod.fst (h₁ ctxN ctxB)) j
        · simp only [Fin.addCases_right]
          exact congrFun
            (congrArg Prod.fst (h₂ ctxN ctxB)) j
      · funext i
        refine Fin.addCases (fun j => ?_) (fun j => ?_) i
        · simp only [Fin.addCases_left]
          exact congrFun
            (congrArg Prod.snd (h₁ ctxN ctxB)) j
        · simp only [Fin.addCases_right]
          exact congrFun
            (congrArg Prod.snd (h₂ ctxN ctxB)) j)

/-- Any morphism into `(0, 0)` equals `terminal`. -/
theorem NatBTMorNQuo.terminal_uniq {nm : ℕ × ℕ}
    (f : NatBTMorNQuo nm (0, 0)) :
    f = NatBTMorNQuo.terminal nm := by
  refine Quotient.inductionOn f ?_
  intro a
  apply Quotient.sound
  intro _ _
  apply Prod.ext
  · exact funext (fun i => i.elim0)
  · exact funext (fun i => i.elim0)

/-- Composition of pair with fst recovers the first factor. -/
theorem NatBTMorNQuo.pair_fst {nm nm₁ nm₂ : ℕ × ℕ}
    (f : NatBTMorNQuo nm nm₁) (g : NatBTMorNQuo nm nm₂) :
    NatBTMorNQuo.comp (NatBTMorNQuo.pair f g)
        (NatBTMorNQuo.fst (nm₁ := nm₁) (nm₂ := nm₂)) = f := by
  refine Quotient.inductionOn₂ f g ?_
  intro a b
  apply Quotient.sound
  intro ctxN ctxB
  apply Prod.ext
  · funext i
    change
      ((a.pair b).natComps (Fin.castAdd nm₂.1 i)).interp
        ctxN ctxB = (a.natComps i).interp ctxN ctxB
    have h :
        (a.pair b).natComps (Fin.castAdd nm₂.1 i) =
          a.natComps i :=
      Fin.addCases_left (motive := fun _ =>
        NatBTMor1 nm .nat) i
    rw [h]
  · funext i
    change
      ((a.pair b).btComps (Fin.castAdd nm₂.2 i)).interp
        ctxN ctxB = (a.btComps i).interp ctxN ctxB
    have h :
        (a.pair b).btComps (Fin.castAdd nm₂.2 i) =
          a.btComps i :=
      Fin.addCases_left (motive := fun _ =>
        NatBTMor1 nm .bt) i
    rw [h]

/-- Composition of pair with snd recovers the second factor. -/
theorem NatBTMorNQuo.pair_snd {nm nm₁ nm₂ : ℕ × ℕ}
    (f : NatBTMorNQuo nm nm₁) (g : NatBTMorNQuo nm nm₂) :
    NatBTMorNQuo.comp (NatBTMorNQuo.pair f g)
        (NatBTMorNQuo.snd (nm₁ := nm₁) (nm₂ := nm₂)) = g := by
  refine Quotient.inductionOn₂ f g ?_
  intro a b
  apply Quotient.sound
  intro ctxN ctxB
  apply Prod.ext
  · funext i
    change
      ((a.pair b).natComps (Fin.natAdd nm₁.1 i)).interp
        ctxN ctxB = (b.natComps i).interp ctxN ctxB
    have h :
        (a.pair b).natComps (Fin.natAdd nm₁.1 i) =
          b.natComps i :=
      Fin.addCases_right (motive := fun _ =>
        NatBTMor1 nm .nat) i
    rw [h]
  · funext i
    change
      ((a.pair b).btComps (Fin.natAdd nm₁.2 i)).interp
        ctxN ctxB = (b.btComps i).interp ctxN ctxB
    have h :
        (a.pair b).btComps (Fin.natAdd nm₁.2 i) =
          b.btComps i :=
      Fin.addCases_right (motive := fun _ =>
        NatBTMor1 nm .bt) i
    rw [h]

/-- Uniqueness of pairing. -/
theorem NatBTMorNQuo.pair_uniq {nm nm₁ nm₂ : ℕ × ℕ}
    (f : NatBTMorNQuo nm nm₁)
    (g : NatBTMorNQuo nm nm₂)
    (h : NatBTMorNQuo nm (nm₁.1 + nm₂.1, nm₁.2 + nm₂.2))
    (hfst : NatBTMorNQuo.comp h
      (NatBTMorNQuo.fst (nm₁ := nm₁) (nm₂ := nm₂)) = f)
    (hsnd : NatBTMorNQuo.comp h
      (NatBTMorNQuo.snd (nm₁ := nm₁) (nm₂ := nm₂)) = g) :
    h = NatBTMorNQuo.pair f g := by
  revert hfst hsnd
  refine Quotient.inductionOn h ?_
  intro hr
  refine Quotient.inductionOn f ?_
  intro fr
  refine Quotient.inductionOn g ?_
  intro gr hfst hsnd
  have hf_rel := Quotient.exact hfst
  have hs_rel := Quotient.exact hsnd
  apply Quotient.sound
  intro ctxN ctxB
  simp only [NatBTMorN.interp_pair]
  apply Prod.ext
  · funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp only [Fin.addCases_left]
      have step := congrFun
        (congrArg Prod.fst (hf_rel ctxN ctxB)) j
      simp only [NatBTMorN.interp] at step
      exact step
    · simp only [Fin.addCases_right]
      have step := congrFun
        (congrArg Prod.fst (hs_rel ctxN ctxB)) j
      simp only [NatBTMorN.interp] at step
      exact step
  · funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp only [Fin.addCases_left]
      have step := congrFun
        (congrArg Prod.snd (hf_rel ctxN ctxB)) j
      simp only [NatBTMorN.interp] at step
      exact step
    · simp only [Fin.addCases_right]
      have step := congrFun
        (congrArg Prod.snd (hs_rel ctxN ctxB)) j
      simp only [NatBTMorN.interp] at step
      exact step

/-- Chosen binary product for `LawvereNatBTCat`. -/
def lawvereNatBTProduct (nm₁ nm₂ : LawvereNatBTCat) :
    ChosenBinaryProduct nm₁ nm₂ where
  obj := (nm₁.1 + nm₂.1, nm₁.2 + nm₂.2)
  fst := NatBTMorNQuo.fst
  snd := NatBTMorNQuo.snd
  lift f g := NatBTMorNQuo.pair f g
  lift_fst := NatBTMorNQuo.pair_fst
  lift_snd := NatBTMorNQuo.pair_snd
  lift_uniq f g h hf hs :=
    NatBTMorNQuo.pair_uniq f g h hf hs

/-- Chosen terminal object for `LawvereNatBTCat`. -/
def lawvereNatBTTerminal : ChosenTerminal LawvereNatBTCat where
  obj := (0, 0)
  from_ nm := NatBTMorNQuo.terminal nm
  uniq f := NatBTMorNQuo.terminal_uniq f

instance : HasChosenFiniteProducts LawvereNatBTCat where
  terminal := lawvereNatBTTerminal
  product := lawvereNatBTProduct

end GebLean
