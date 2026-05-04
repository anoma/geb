import GebLean.LawvereNatBTV2
import GebLean.Utilities.ComputableLimits
import Mathlib.CategoryTheory.Category.Basic

/-!
# Quotient Category for `LawvereNatBTV2`

Bottom-up V2 variant of `LawvereNatBTQuot`.  Defines the tuple
type `NatBTMorNV2`, its extensional-equality setoid and quotient
`NatBTMorNV2Quo`, identity and composition, the category
`LawvereNatBTV2Cat`, and the `HasChosenFiniteProducts` structure.

The bottom-up design is documented in
`docs/superpowers/specs/2026-04-19-bottom-up-natbt-design.md`.
-/

namespace GebLean

/-- A morphism `(n, m) → (n', m')` in the V2 two-sort theory:
`n'` ℕ-valued components and `m'` BT-valued components, each a
`NatBTMor1V2` with domain arity `(n, m)`. -/
@[ext]
structure NatBTMorNV2 (nm nm' : ℕ × ℕ) where
  natComps : Fin nm'.1 → NatBTMor1V2 nm .nat
  btComps  : Fin nm'.2 → NatBTMor1V2 nm .bt

/-- Identity morphism `(n, m) → (n, m)`: tuple of projections at
each sort. -/
def NatBTMorNV2.id (nm : ℕ × ℕ) : NatBTMorNV2 nm nm where
  natComps i := NatBTMor1V2.natProj i
  btComps i := NatBTMor1V2.btProj i

/-- Composition of V2 two-sort tuples via `compNat` / `compBT` at
each component. -/
def NatBTMorNV2.comp {nm nm' nm'' : ℕ × ℕ}
    (f : NatBTMorNV2 nm nm') (g : NatBTMorNV2 nm' nm'') :
    NatBTMorNV2 nm nm'' where
  natComps i :=
    NatBTMor1V2.compNat (g.natComps i) f.natComps f.btComps
  btComps i :=
    NatBTMor1V2.compBT (g.btComps i) f.natComps f.btComps

/-- Tuple interpretation: apply `NatBTMor1V2.interp` at each
component. -/
def NatBTMorNV2.interp {nm nm' : ℕ × ℕ}
    (f : NatBTMorNV2 nm nm')
    (ctxN : Fin nm.1 → ℕ) (ctxB : Fin nm.2 → BTL) :
    (Fin nm'.1 → ℕ) × (Fin nm'.2 → BTL) :=
  (fun i => (f.natComps i).interp ctxN ctxB,
   fun i => (f.btComps i).interp ctxN ctxB)

@[simp] theorem NatBTMorNV2.interp_id (nm : ℕ × ℕ)
    (ctxN : Fin nm.1 → ℕ) (ctxB : Fin nm.2 → BTL) :
    (NatBTMorNV2.id nm).interp ctxN ctxB = (ctxN, ctxB) := by
  simp [NatBTMorNV2.id, NatBTMorNV2.interp]

@[simp] theorem NatBTMorNV2.interp_comp
    {nm nm' nm'' : ℕ × ℕ}
    (f : NatBTMorNV2 nm nm') (g : NatBTMorNV2 nm' nm'')
    (ctxN : Fin nm.1 → ℕ) (ctxB : Fin nm.2 → BTL) :
    (NatBTMorNV2.comp f g).interp ctxN ctxB =
      let ctxN' := (f.interp ctxN ctxB).1
      let ctxB' := (f.interp ctxN ctxB).2
      g.interp ctxN' ctxB' := by
  simp [NatBTMorNV2.comp, NatBTMorNV2.interp]

/-- Terminal morphism into arity `(0, 0)`: the empty tuple. -/
def NatBTMorNV2.terminal (nm : ℕ × ℕ) : NatBTMorNV2 nm (0, 0) where
  natComps i := i.elim0
  btComps i := i.elim0

/-- First projection from the product arity
`(nm₁.1 + nm₂.1, nm₁.2 + nm₂.2)`. -/
def NatBTMorNV2.fst {nm₁ nm₂ : ℕ × ℕ} :
    NatBTMorNV2 (nm₁.1 + nm₂.1, nm₁.2 + nm₂.2) nm₁ where
  natComps i := NatBTMor1V2.natProj (Fin.castAdd nm₂.1 i)
  btComps i := NatBTMor1V2.btProj (Fin.castAdd nm₂.2 i)

/-- Second projection from the product arity
`(nm₁.1 + nm₂.1, nm₁.2 + nm₂.2)`. -/
def NatBTMorNV2.snd {nm₁ nm₂ : ℕ × ℕ} :
    NatBTMorNV2 (nm₁.1 + nm₂.1, nm₁.2 + nm₂.2) nm₂ where
  natComps i := NatBTMor1V2.natProj (Fin.natAdd nm₁.1 i)
  btComps i := NatBTMor1V2.btProj (Fin.natAdd nm₁.2 i)

/-- Pairing: given morphisms into `nm₁` and `nm₂`, build one into
`(nm₁.1 + nm₂.1, nm₁.2 + nm₂.2)` via `Fin.addCases`. -/
def NatBTMorNV2.pair {nm nm₁ nm₂ : ℕ × ℕ}
    (f : NatBTMorNV2 nm nm₁) (g : NatBTMorNV2 nm nm₂) :
    NatBTMorNV2 nm (nm₁.1 + nm₂.1, nm₁.2 + nm₂.2) where
  natComps := Fin.addCases f.natComps g.natComps
  btComps := Fin.addCases f.btComps g.btComps

@[simp] theorem NatBTMorNV2.interp_terminal
    {nm : ℕ × ℕ} (ctxN : Fin nm.1 → ℕ) (ctxB : Fin nm.2 → BTL) :
    (NatBTMorNV2.terminal nm).interp ctxN ctxB =
      ((fun i => i.elim0), (fun i => i.elim0)) := by
  apply Prod.ext
  · exact funext (fun i => i.elim0)
  · exact funext (fun i => i.elim0)

@[simp] theorem NatBTMorNV2.interp_fst
    {nm₁ nm₂ : ℕ × ℕ}
    (ctxN : Fin (nm₁.1 + nm₂.1) → ℕ)
    (ctxB : Fin (nm₁.2 + nm₂.2) → BTL) :
    (NatBTMorNV2.fst (nm₁ := nm₁) (nm₂ := nm₂)).interp
        ctxN ctxB =
      ((fun i => ctxN (Fin.castAdd nm₂.1 i)),
       (fun i => ctxB (Fin.castAdd nm₂.2 i))) := by
  apply Prod.ext
  · funext i
    simp [NatBTMorNV2.fst, NatBTMorNV2.interp]
  · funext i
    simp [NatBTMorNV2.fst, NatBTMorNV2.interp]

@[simp] theorem NatBTMorNV2.interp_snd
    {nm₁ nm₂ : ℕ × ℕ}
    (ctxN : Fin (nm₁.1 + nm₂.1) → ℕ)
    (ctxB : Fin (nm₁.2 + nm₂.2) → BTL) :
    (NatBTMorNV2.snd (nm₁ := nm₁) (nm₂ := nm₂)).interp
        ctxN ctxB =
      ((fun i => ctxN (Fin.natAdd nm₁.1 i)),
       (fun i => ctxB (Fin.natAdd nm₁.2 i))) := by
  apply Prod.ext
  · funext i
    simp [NatBTMorNV2.snd, NatBTMorNV2.interp]
  · funext i
    simp [NatBTMorNV2.snd, NatBTMorNV2.interp]

@[simp] theorem NatBTMorNV2.interp_pair
    {nm nm₁ nm₂ : ℕ × ℕ}
    (f : NatBTMorNV2 nm nm₁) (g : NatBTMorNV2 nm nm₂)
    (ctxN : Fin nm.1 → ℕ) (ctxB : Fin nm.2 → BTL) :
    (NatBTMorNV2.pair f g).interp ctxN ctxB =
      ((fun i => Fin.addCases
          (fun j => (f.natComps j).interp ctxN ctxB)
          (fun j => (g.natComps j).interp ctxN ctxB) i),
       (fun i => Fin.addCases
          (fun j => (f.btComps j).interp ctxN ctxB)
          (fun j => (g.btComps j).interp ctxN ctxB) i)) := by
  apply Prod.ext
  · funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp [NatBTMorNV2.interp, NatBTMorNV2.pair]
    · simp [NatBTMorNV2.interp, NatBTMorNV2.pair]
  · funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp [NatBTMorNV2.interp, NatBTMorNV2.pair]
    · simp [NatBTMorNV2.interp, NatBTMorNV2.pair]

/-- Extensional equality of `NatBTMorNV2` tuples: two tuples are
related iff their interpretations agree on every domain context. -/
def natBTMorNV2Rel (nm nm' : ℕ × ℕ) :
    NatBTMorNV2 nm nm' → NatBTMorNV2 nm nm' → Prop :=
  fun f g => ∀ (ctxN : Fin nm.1 → ℕ) (ctxB : Fin nm.2 → BTL),
    f.interp ctxN ctxB = g.interp ctxN ctxB

instance natBTMorNV2Setoid (nm nm' : ℕ × ℕ) :
    Setoid (NatBTMorNV2 nm nm') where
  r := natBTMorNV2Rel nm nm'
  iseqv :=
    ⟨ fun _ _ _ => rfl,
      fun h c d => (h c d).symm,
      fun h₁ h₂ c d => (h₁ c d).trans (h₂ c d) ⟩

/-- `NatBTMorNV2` tuples modulo extensional equivalence. -/
def NatBTMorNV2Quo (nm nm' : ℕ × ℕ) : Type :=
  Quotient (natBTMorNV2Setoid nm nm')

/-- Identity class: `NatBTMorNV2.id` packaged into the quotient. -/
def NatBTMorNV2Quo.id (nm : ℕ × ℕ) : NatBTMorNV2Quo nm nm :=
  Quotient.mk _ (NatBTMorNV2.id nm)

/-- Composition lifted through the quotient: extensional
equivalence is preserved by substitution. -/
def NatBTMorNV2Quo.comp {nm nm' nm'' : ℕ × ℕ}
    (f : NatBTMorNV2Quo nm nm') (g : NatBTMorNV2Quo nm' nm'') :
    NatBTMorNV2Quo nm nm'' :=
  Quotient.liftOn₂ f g
    (fun a b => Quotient.mk _ (NatBTMorNV2.comp a b))
    (fun a₁ b₁ a₂ b₂ h₁ h₂ => by
      apply Quotient.sound
      intro ctxN ctxB
      simp only [NatBTMorNV2.interp_comp]
      rw [h₁ ctxN ctxB]
      exact h₂ _ _)

theorem NatBTMorNV2Quo.id_comp {nm nm' : ℕ × ℕ}
    (f : NatBTMorNV2Quo nm nm') :
    NatBTMorNV2Quo.comp (NatBTMorNV2Quo.id nm) f = f := by
  refine Quotient.inductionOn f ?_
  intro a
  apply Quotient.sound
  intro ctxN ctxB
  simp

theorem NatBTMorNV2Quo.comp_id {nm nm' : ℕ × ℕ}
    (f : NatBTMorNV2Quo nm nm') :
    NatBTMorNV2Quo.comp f (NatBTMorNV2Quo.id nm') = f := by
  refine Quotient.inductionOn f ?_
  intro a
  apply Quotient.sound
  intro ctxN ctxB
  simp

theorem NatBTMorNV2Quo.assoc
    {nm nm' nm'' nm''' : ℕ × ℕ}
    (f : NatBTMorNV2Quo nm nm')
    (g : NatBTMorNV2Quo nm' nm'')
    (h : NatBTMorNV2Quo nm'' nm''') :
    NatBTMorNV2Quo.comp (NatBTMorNV2Quo.comp f g) h =
      NatBTMorNV2Quo.comp f (NatBTMorNV2Quo.comp g h) := by
  refine Quotient.inductionOn₃ f g h ?_
  intro a b c
  apply Quotient.sound
  intro ctxN ctxB
  simp

open CategoryTheory

/-- Carrier type for the V2 two-sort base category: pairs
`(n, m) : ℕ × ℕ` interpreted as `ℕⁿ × BTᵐ`. -/
def LawvereNatBTV2Cat : Type := ℕ × ℕ

instance : CategoryStruct LawvereNatBTV2Cat where
  Hom nm nm' := NatBTMorNV2Quo nm nm'
  id := NatBTMorNV2Quo.id
  comp := NatBTMorNV2Quo.comp

instance : Category LawvereNatBTV2Cat where
  id_comp := NatBTMorNV2Quo.id_comp
  comp_id := NatBTMorNV2Quo.comp_id
  assoc := fun f g h => NatBTMorNV2Quo.assoc f g h

/-- Terminal class: `NatBTMorNV2.terminal` in the quotient. -/
def NatBTMorNV2Quo.terminal (nm : ℕ × ℕ) :
    NatBTMorNV2Quo nm (0, 0) :=
  Quotient.mk _ (NatBTMorNV2.terminal nm)

/-- First projection class in the quotient. -/
def NatBTMorNV2Quo.fst {nm₁ nm₂ : ℕ × ℕ} :
    NatBTMorNV2Quo (nm₁.1 + nm₂.1, nm₁.2 + nm₂.2) nm₁ :=
  Quotient.mk _ (NatBTMorNV2.fst (nm₁ := nm₁) (nm₂ := nm₂))

/-- Second projection class in the quotient. -/
def NatBTMorNV2Quo.snd {nm₁ nm₂ : ℕ × ℕ} :
    NatBTMorNV2Quo (nm₁.1 + nm₂.1, nm₁.2 + nm₂.2) nm₂ :=
  Quotient.mk _ (NatBTMorNV2.snd (nm₁ := nm₁) (nm₂ := nm₂))

/-- Pairing in the quotient, lifted via `Quotient.lift₂`. -/
def NatBTMorNV2Quo.pair {nm nm₁ nm₂ : ℕ × ℕ}
    (f : NatBTMorNV2Quo nm nm₁) (g : NatBTMorNV2Quo nm nm₂) :
    NatBTMorNV2Quo nm (nm₁.1 + nm₂.1, nm₁.2 + nm₂.2) :=
  Quotient.liftOn₂ f g
    (fun a b => Quotient.mk _ (NatBTMorNV2.pair a b))
    (fun a₁ b₁ a₂ b₂ h₁ h₂ => by
      apply Quotient.sound
      intro ctxN ctxB
      simp only [NatBTMorNV2.interp_pair]
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
theorem NatBTMorNV2Quo.terminal_uniq {nm : ℕ × ℕ}
    (f : NatBTMorNV2Quo nm (0, 0)) :
    f = NatBTMorNV2Quo.terminal nm := by
  refine Quotient.inductionOn f ?_
  intro a
  apply Quotient.sound
  intro _ _
  apply Prod.ext
  · exact funext (fun i => i.elim0)
  · exact funext (fun i => i.elim0)

/-- Composition of pair with fst recovers the first factor. -/
theorem NatBTMorNV2Quo.pair_fst {nm nm₁ nm₂ : ℕ × ℕ}
    (f : NatBTMorNV2Quo nm nm₁) (g : NatBTMorNV2Quo nm nm₂) :
    NatBTMorNV2Quo.comp (NatBTMorNV2Quo.pair f g)
        (NatBTMorNV2Quo.fst (nm₁ := nm₁) (nm₂ := nm₂)) = f := by
  refine Quotient.inductionOn₂ f g ?_
  intro a b
  apply Quotient.sound
  intro ctxN ctxB
  simp only [NatBTMorNV2.interp_comp, NatBTMorNV2.interp_pair,
    NatBTMorNV2.interp_fst, Fin.addCases_left]
  rfl

/-- Composition of pair with snd recovers the second factor. -/
theorem NatBTMorNV2Quo.pair_snd {nm nm₁ nm₂ : ℕ × ℕ}
    (f : NatBTMorNV2Quo nm nm₁) (g : NatBTMorNV2Quo nm nm₂) :
    NatBTMorNV2Quo.comp (NatBTMorNV2Quo.pair f g)
        (NatBTMorNV2Quo.snd (nm₁ := nm₁) (nm₂ := nm₂)) = g := by
  refine Quotient.inductionOn₂ f g ?_
  intro a b
  apply Quotient.sound
  intro ctxN ctxB
  simp only [NatBTMorNV2.interp_comp, NatBTMorNV2.interp_pair,
    NatBTMorNV2.interp_snd, Fin.addCases_right]
  rfl

/-- Uniqueness of pairing. -/
theorem NatBTMorNV2Quo.pair_uniq {nm nm₁ nm₂ : ℕ × ℕ}
    (f : NatBTMorNV2Quo nm nm₁)
    (g : NatBTMorNV2Quo nm nm₂)
    (h : NatBTMorNV2Quo nm (nm₁.1 + nm₂.1, nm₁.2 + nm₂.2))
    (hfst : NatBTMorNV2Quo.comp h
      (NatBTMorNV2Quo.fst (nm₁ := nm₁) (nm₂ := nm₂)) = f)
    (hsnd : NatBTMorNV2Quo.comp h
      (NatBTMorNV2Quo.snd (nm₁ := nm₁) (nm₂ := nm₂)) = g) :
    h = NatBTMorNV2Quo.pair f g := by
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
  simp only [NatBTMorNV2.interp_pair]
  have hf_step := hf_rel ctxN ctxB
  have hs_step := hs_rel ctxN ctxB
  rw [NatBTMorNV2.interp_comp, NatBTMorNV2.interp_fst] at hf_step
  rw [NatBTMorNV2.interp_comp, NatBTMorNV2.interp_snd] at hs_step
  apply Prod.ext
  · funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp only [Fin.addCases_left]
      exact congrFun (congrArg Prod.fst hf_step) j
    · simp only [Fin.addCases_right]
      exact congrFun (congrArg Prod.fst hs_step) j
  · funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp only [Fin.addCases_left]
      exact congrFun (congrArg Prod.snd hf_step) j
    · simp only [Fin.addCases_right]
      exact congrFun (congrArg Prod.snd hs_step) j

/-- Chosen binary product for `LawvereNatBTV2Cat`. -/
def lawvereNatBTV2Product (nm₁ nm₂ : LawvereNatBTV2Cat) :
    ChosenBinaryProduct nm₁ nm₂ where
  obj := (nm₁.1 + nm₂.1, nm₁.2 + nm₂.2)
  fst := NatBTMorNV2Quo.fst
  snd := NatBTMorNV2Quo.snd
  lift f g := NatBTMorNV2Quo.pair f g
  lift_fst := NatBTMorNV2Quo.pair_fst
  lift_snd := NatBTMorNV2Quo.pair_snd
  lift_uniq f g h hf hs :=
    NatBTMorNV2Quo.pair_uniq f g h hf hs

/-- Chosen terminal object for `LawvereNatBTV2Cat`. -/
def lawvereNatBTV2Terminal :
    ChosenTerminal LawvereNatBTV2Cat where
  obj := (0, 0)
  from_ nm := NatBTMorNV2Quo.terminal nm
  uniq f := NatBTMorNV2Quo.terminal_uniq f

instance : HasChosenFiniteProducts LawvereNatBTV2Cat where
  terminal := lawvereNatBTV2Terminal
  product := lawvereNatBTV2Product

end GebLean
