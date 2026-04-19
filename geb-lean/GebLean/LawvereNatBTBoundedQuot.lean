import GebLean.LawvereNatBTBounded
import GebLean.Utilities.ComputableLimits
import Mathlib.CategoryTheory.Category.Basic

/-!
# Quotient Category for `LawvereNatBTBounded`

Bounded variant of `LawvereNatBTQuot`.  `NatBTMorNBounded` tuples
quotiented by extensional equality of interpretations, with the
resulting `Category LawvereNatBTBoundedCat` and chosen finite
products.

The two-stage architecture is documented in
`docs/superpowers/specs/2026-04-18-option-e-bounded-natbt-design.md`.
-/

namespace GebLean

/-- A morphism `(n, m) → (n', m')` in the bounded two-sort theory:
`n'` ℕ-valued components and `m'` BT-valued components, each a
`NatBTMor1Bounded` with domain arity `(n, m)`. -/
@[ext]
structure NatBTMorNBounded (nm nm' : ℕ × ℕ) where
  natComps : Fin nm'.1 → NatBTMor1Bounded nm .nat
  btComps  : Fin nm'.2 → NatBTMor1Bounded nm .bt

/-- Identity morphism `(n, m) → (n, m)`: tuple of projections at
each sort. -/
def NatBTMorNBounded.id (nm : ℕ × ℕ) : NatBTMorNBounded nm nm where
  natComps i := NatBTMor1Bounded.natProj i
  btComps i := NatBTMor1Bounded.btProj i

/-- Composition of two-sort tuples via `compNat` / `compBT` at
each component. -/
def NatBTMorNBounded.comp {nm nm' nm'' : ℕ × ℕ}
    (f : NatBTMorNBounded nm nm') (g : NatBTMorNBounded nm' nm'') :
    NatBTMorNBounded nm nm'' where
  natComps i :=
    NatBTMor1Bounded.compNat (g.natComps i) f.natComps f.btComps
  btComps i :=
    NatBTMor1Bounded.compBT (g.btComps i) f.natComps f.btComps

/-- Tuple interpretation: apply `NatBTMor1Bounded.interp` at each
component. -/
def NatBTMorNBounded.interp {nm nm' : ℕ × ℕ}
    (f : NatBTMorNBounded nm nm')
    (ctxN : Fin nm.1 → ℕ) (ctxB : Fin nm.2 → BTL) :
    (Fin nm'.1 → ℕ) × (Fin nm'.2 → BTL) :=
  (fun i => (f.natComps i).interp ctxN ctxB,
   fun i => (f.btComps i).interp ctxN ctxB)

@[simp] theorem NatBTMorNBounded.interp_id (nm : ℕ × ℕ)
    (ctxN : Fin nm.1 → ℕ) (ctxB : Fin nm.2 → BTL) :
    (NatBTMorNBounded.id nm).interp ctxN ctxB = (ctxN, ctxB) := by
  simp [NatBTMorNBounded.id, NatBTMorNBounded.interp]

@[simp] theorem NatBTMorNBounded.interp_comp
    {nm nm' nm'' : ℕ × ℕ}
    (f : NatBTMorNBounded nm nm') (g : NatBTMorNBounded nm' nm'')
    (ctxN : Fin nm.1 → ℕ) (ctxB : Fin nm.2 → BTL) :
    (NatBTMorNBounded.comp f g).interp ctxN ctxB =
      let ctxN' := (f.interp ctxN ctxB).1
      let ctxB' := (f.interp ctxN ctxB).2
      g.interp ctxN' ctxB' := by
  simp [NatBTMorNBounded.comp, NatBTMorNBounded.interp]

/-- Terminal morphism into arity `(0, 0)`: the empty tuple. -/
def NatBTMorNBounded.terminal (nm : ℕ × ℕ) :
    NatBTMorNBounded nm (0, 0) where
  natComps i := i.elim0
  btComps i := i.elim0

/-- First projection from the product arity
`(nm₁.1 + nm₂.1, nm₁.2 + nm₂.2)`. -/
def NatBTMorNBounded.fst {nm₁ nm₂ : ℕ × ℕ} :
    NatBTMorNBounded (nm₁.1 + nm₂.1, nm₁.2 + nm₂.2) nm₁ where
  natComps i := NatBTMor1Bounded.natProj (Fin.castAdd nm₂.1 i)
  btComps i := NatBTMor1Bounded.btProj (Fin.castAdd nm₂.2 i)

/-- Second projection from the product arity
`(nm₁.1 + nm₂.1, nm₁.2 + nm₂.2)`. -/
def NatBTMorNBounded.snd {nm₁ nm₂ : ℕ × ℕ} :
    NatBTMorNBounded (nm₁.1 + nm₂.1, nm₁.2 + nm₂.2) nm₂ where
  natComps i := NatBTMor1Bounded.natProj (Fin.natAdd nm₁.1 i)
  btComps i := NatBTMor1Bounded.btProj (Fin.natAdd nm₁.2 i)

/-- Pairing: given morphisms into `nm₁` and `nm₂`, build one into
`(nm₁.1 + nm₂.1, nm₁.2 + nm₂.2)` via `Fin.addCases`. -/
def NatBTMorNBounded.pair {nm nm₁ nm₂ : ℕ × ℕ}
    (f : NatBTMorNBounded nm nm₁) (g : NatBTMorNBounded nm nm₂) :
    NatBTMorNBounded nm (nm₁.1 + nm₂.1, nm₁.2 + nm₂.2) where
  natComps := Fin.addCases f.natComps g.natComps
  btComps := Fin.addCases f.btComps g.btComps

@[simp] theorem NatBTMorNBounded.interp_terminal
    {nm : ℕ × ℕ} (ctxN : Fin nm.1 → ℕ) (ctxB : Fin nm.2 → BTL) :
    (NatBTMorNBounded.terminal nm).interp ctxN ctxB =
      ((fun i => i.elim0), (fun i => i.elim0)) := by
  apply Prod.ext
  · exact funext (fun i => i.elim0)
  · exact funext (fun i => i.elim0)

@[simp] theorem NatBTMorNBounded.interp_fst
    {nm₁ nm₂ : ℕ × ℕ}
    (ctxN : Fin (nm₁.1 + nm₂.1) → ℕ)
    (ctxB : Fin (nm₁.2 + nm₂.2) → BTL) :
    (NatBTMorNBounded.fst (nm₁ := nm₁) (nm₂ := nm₂)).interp
        ctxN ctxB =
      ((fun i => ctxN (Fin.castAdd nm₂.1 i)),
       (fun i => ctxB (Fin.castAdd nm₂.2 i))) := rfl

@[simp] theorem NatBTMorNBounded.interp_snd
    {nm₁ nm₂ : ℕ × ℕ}
    (ctxN : Fin (nm₁.1 + nm₂.1) → ℕ)
    (ctxB : Fin (nm₁.2 + nm₂.2) → BTL) :
    (NatBTMorNBounded.snd (nm₁ := nm₁) (nm₂ := nm₂)).interp
        ctxN ctxB =
      ((fun i => ctxN (Fin.natAdd nm₁.1 i)),
       (fun i => ctxB (Fin.natAdd nm₁.2 i))) := rfl

@[simp] theorem NatBTMorNBounded.interp_pair
    {nm nm₁ nm₂ : ℕ × ℕ}
    (f : NatBTMorNBounded nm nm₁) (g : NatBTMorNBounded nm nm₂)
    (ctxN : Fin nm.1 → ℕ) (ctxB : Fin nm.2 → BTL) :
    (NatBTMorNBounded.pair f g).interp ctxN ctxB =
      ((fun i => Fin.addCases
          (fun j => (f.natComps j).interp ctxN ctxB)
          (fun j => (g.natComps j).interp ctxN ctxB) i),
       (fun i => Fin.addCases
          (fun j => (f.btComps j).interp ctxN ctxB)
          (fun j => (g.btComps j).interp ctxN ctxB) i)) := by
  apply Prod.ext
  · funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp [NatBTMorNBounded.interp, NatBTMorNBounded.pair]
    · simp [NatBTMorNBounded.interp, NatBTMorNBounded.pair]
  · funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp [NatBTMorNBounded.interp, NatBTMorNBounded.pair]
    · simp [NatBTMorNBounded.interp, NatBTMorNBounded.pair]

/-- Extensional equality of `NatBTMorNBounded` tuples: two tuples
are related iff their interpretations agree on every domain
context. -/
def natBTMorNBoundedRel (nm nm' : ℕ × ℕ) :
    NatBTMorNBounded nm nm' → NatBTMorNBounded nm nm' → Prop :=
  fun f g => ∀ (ctxN : Fin nm.1 → ℕ) (ctxB : Fin nm.2 → BTL),
    f.interp ctxN ctxB = g.interp ctxN ctxB

instance natBTMorNBoundedSetoid (nm nm' : ℕ × ℕ) :
    Setoid (NatBTMorNBounded nm nm') where
  r := natBTMorNBoundedRel nm nm'
  iseqv :=
    ⟨ fun _ _ _ => rfl,
      fun h c d => (h c d).symm,
      fun h₁ h₂ c d => (h₁ c d).trans (h₂ c d) ⟩

/-- `NatBTMorNBounded` tuples modulo extensional equivalence. -/
def NatBTMorNBoundedQuo (nm nm' : ℕ × ℕ) : Type :=
  Quotient (natBTMorNBoundedSetoid nm nm')

/-- Identity class: `NatBTMorNBounded.id` packaged into the
quotient. -/
def NatBTMorNBoundedQuo.id (nm : ℕ × ℕ) : NatBTMorNBoundedQuo nm nm :=
  Quotient.mk _ (NatBTMorNBounded.id nm)

/-- Composition lifted through the quotient: extensional
equivalence is preserved by substitution. -/
def NatBTMorNBoundedQuo.comp {nm nm' nm'' : ℕ × ℕ}
    (f : NatBTMorNBoundedQuo nm nm')
    (g : NatBTMorNBoundedQuo nm' nm'') :
    NatBTMorNBoundedQuo nm nm'' :=
  Quotient.liftOn₂ f g
    (fun a b => Quotient.mk _ (NatBTMorNBounded.comp a b))
    (fun a₁ b₁ a₂ b₂ h₁ h₂ => by
      apply Quotient.sound
      intro ctxN ctxB
      simp only [NatBTMorNBounded.interp_comp]
      rw [h₁ ctxN ctxB]
      exact h₂ _ _)

theorem NatBTMorNBoundedQuo.id_comp {nm nm' : ℕ × ℕ}
    (f : NatBTMorNBoundedQuo nm nm') :
    NatBTMorNBoundedQuo.comp (NatBTMorNBoundedQuo.id nm) f = f := by
  refine Quotient.inductionOn f ?_
  intro a
  apply Quotient.sound
  intro ctxN ctxB
  simp

theorem NatBTMorNBoundedQuo.comp_id {nm nm' : ℕ × ℕ}
    (f : NatBTMorNBoundedQuo nm nm') :
    NatBTMorNBoundedQuo.comp f (NatBTMorNBoundedQuo.id nm') = f := by
  refine Quotient.inductionOn f ?_
  intro a
  apply Quotient.sound
  intro ctxN ctxB
  simp

theorem NatBTMorNBoundedQuo.assoc
    {nm nm' nm'' nm''' : ℕ × ℕ}
    (f : NatBTMorNBoundedQuo nm nm')
    (g : NatBTMorNBoundedQuo nm' nm'')
    (h : NatBTMorNBoundedQuo nm'' nm''') :
    NatBTMorNBoundedQuo.comp (NatBTMorNBoundedQuo.comp f g) h =
      NatBTMorNBoundedQuo.comp f
        (NatBTMorNBoundedQuo.comp g h) := by
  refine Quotient.inductionOn₃ f g h ?_
  intro a b c
  apply Quotient.sound
  intro ctxN ctxB
  simp

open CategoryTheory

/-- Carrier type for the bounded two-sort base category: pairs
`(n, m) : ℕ × ℕ` interpreted as `ℕⁿ × BTᵐ`. -/
def LawvereNatBTBoundedCat : Type := ℕ × ℕ

instance : CategoryStruct LawvereNatBTBoundedCat where
  Hom nm nm' := NatBTMorNBoundedQuo nm nm'
  id := NatBTMorNBoundedQuo.id
  comp := NatBTMorNBoundedQuo.comp

instance : Category LawvereNatBTBoundedCat where
  id_comp := NatBTMorNBoundedQuo.id_comp
  comp_id := NatBTMorNBoundedQuo.comp_id
  assoc := fun f g h => NatBTMorNBoundedQuo.assoc f g h

/-- Terminal class: `NatBTMorNBounded.terminal` in the quotient. -/
def NatBTMorNBoundedQuo.terminal (nm : ℕ × ℕ) :
    NatBTMorNBoundedQuo nm (0, 0) :=
  Quotient.mk _ (NatBTMorNBounded.terminal nm)

/-- First projection class in the quotient. -/
def NatBTMorNBoundedQuo.fst {nm₁ nm₂ : ℕ × ℕ} :
    NatBTMorNBoundedQuo (nm₁.1 + nm₂.1, nm₁.2 + nm₂.2) nm₁ :=
  Quotient.mk _ (NatBTMorNBounded.fst (nm₁ := nm₁) (nm₂ := nm₂))

/-- Second projection class in the quotient. -/
def NatBTMorNBoundedQuo.snd {nm₁ nm₂ : ℕ × ℕ} :
    NatBTMorNBoundedQuo (nm₁.1 + nm₂.1, nm₁.2 + nm₂.2) nm₂ :=
  Quotient.mk _ (NatBTMorNBounded.snd (nm₁ := nm₁) (nm₂ := nm₂))

/-- Pairing in the quotient, lifted via `Quotient.lift₂`. -/
def NatBTMorNBoundedQuo.pair {nm nm₁ nm₂ : ℕ × ℕ}
    (f : NatBTMorNBoundedQuo nm nm₁)
    (g : NatBTMorNBoundedQuo nm nm₂) :
    NatBTMorNBoundedQuo nm (nm₁.1 + nm₂.1, nm₁.2 + nm₂.2) :=
  Quotient.liftOn₂ f g
    (fun a b => Quotient.mk _ (NatBTMorNBounded.pair a b))
    (fun a₁ b₁ a₂ b₂ h₁ h₂ => by
      apply Quotient.sound
      intro ctxN ctxB
      simp only [NatBTMorNBounded.interp_pair]
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
theorem NatBTMorNBoundedQuo.terminal_uniq {nm : ℕ × ℕ}
    (f : NatBTMorNBoundedQuo nm (0, 0)) :
    f = NatBTMorNBoundedQuo.terminal nm := by
  refine Quotient.inductionOn f ?_
  intro a
  apply Quotient.sound
  intro _ _
  apply Prod.ext
  · exact funext (fun i => i.elim0)
  · exact funext (fun i => i.elim0)

/-- Composition of pair with fst recovers the first factor. -/
theorem NatBTMorNBoundedQuo.pair_fst {nm nm₁ nm₂ : ℕ × ℕ}
    (f : NatBTMorNBoundedQuo nm nm₁)
    (g : NatBTMorNBoundedQuo nm nm₂) :
    NatBTMorNBoundedQuo.comp (NatBTMorNBoundedQuo.pair f g)
        (NatBTMorNBoundedQuo.fst (nm₁ := nm₁) (nm₂ := nm₂)) = f := by
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
        NatBTMor1Bounded nm .nat) i
    rw [h]
  · funext i
    change
      ((a.pair b).btComps (Fin.castAdd nm₂.2 i)).interp
        ctxN ctxB = (a.btComps i).interp ctxN ctxB
    have h :
        (a.pair b).btComps (Fin.castAdd nm₂.2 i) =
          a.btComps i :=
      Fin.addCases_left (motive := fun _ =>
        NatBTMor1Bounded nm .bt) i
    rw [h]

/-- Composition of pair with snd recovers the second factor. -/
theorem NatBTMorNBoundedQuo.pair_snd {nm nm₁ nm₂ : ℕ × ℕ}
    (f : NatBTMorNBoundedQuo nm nm₁)
    (g : NatBTMorNBoundedQuo nm nm₂) :
    NatBTMorNBoundedQuo.comp (NatBTMorNBoundedQuo.pair f g)
        (NatBTMorNBoundedQuo.snd (nm₁ := nm₁) (nm₂ := nm₂)) = g := by
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
        NatBTMor1Bounded nm .nat) i
    rw [h]
  · funext i
    change
      ((a.pair b).btComps (Fin.natAdd nm₁.2 i)).interp
        ctxN ctxB = (b.btComps i).interp ctxN ctxB
    have h :
        (a.pair b).btComps (Fin.natAdd nm₁.2 i) =
          b.btComps i :=
      Fin.addCases_right (motive := fun _ =>
        NatBTMor1Bounded nm .bt) i
    rw [h]

/-- Uniqueness of pairing. -/
theorem NatBTMorNBoundedQuo.pair_uniq {nm nm₁ nm₂ : ℕ × ℕ}
    (f : NatBTMorNBoundedQuo nm nm₁)
    (g : NatBTMorNBoundedQuo nm nm₂)
    (h : NatBTMorNBoundedQuo nm
      (nm₁.1 + nm₂.1, nm₁.2 + nm₂.2))
    (hfst : NatBTMorNBoundedQuo.comp h
      (NatBTMorNBoundedQuo.fst (nm₁ := nm₁) (nm₂ := nm₂)) = f)
    (hsnd : NatBTMorNBoundedQuo.comp h
      (NatBTMorNBoundedQuo.snd (nm₁ := nm₁) (nm₂ := nm₂)) = g) :
    h = NatBTMorNBoundedQuo.pair f g := by
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
  simp only [NatBTMorNBounded.interp_pair]
  apply Prod.ext
  · funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp only [Fin.addCases_left]
      have step := congrFun
        (congrArg Prod.fst (hf_rel ctxN ctxB)) j
      simp only [NatBTMorNBounded.interp] at step
      exact step
    · simp only [Fin.addCases_right]
      have step := congrFun
        (congrArg Prod.fst (hs_rel ctxN ctxB)) j
      simp only [NatBTMorNBounded.interp] at step
      exact step
  · funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp only [Fin.addCases_left]
      have step := congrFun
        (congrArg Prod.snd (hf_rel ctxN ctxB)) j
      simp only [NatBTMorNBounded.interp] at step
      exact step
    · simp only [Fin.addCases_right]
      have step := congrFun
        (congrArg Prod.snd (hs_rel ctxN ctxB)) j
      simp only [NatBTMorNBounded.interp] at step
      exact step

/-- Chosen binary product for `LawvereNatBTBoundedCat`. -/
def lawvereNatBTBoundedProduct (nm₁ nm₂ : LawvereNatBTBoundedCat) :
    ChosenBinaryProduct nm₁ nm₂ where
  obj := (nm₁.1 + nm₂.1, nm₁.2 + nm₂.2)
  fst := NatBTMorNBoundedQuo.fst
  snd := NatBTMorNBoundedQuo.snd
  lift f g := NatBTMorNBoundedQuo.pair f g
  lift_fst := NatBTMorNBoundedQuo.pair_fst
  lift_snd := NatBTMorNBoundedQuo.pair_snd
  lift_uniq f g h hf hs :=
    NatBTMorNBoundedQuo.pair_uniq f g h hf hs

/-- Chosen terminal object for `LawvereNatBTBoundedCat`. -/
def lawvereNatBTBoundedTerminal :
    ChosenTerminal LawvereNatBTBoundedCat where
  obj := (0, 0)
  from_ nm := NatBTMorNBoundedQuo.terminal nm
  uniq f := NatBTMorNBoundedQuo.terminal_uniq f

instance : HasChosenFiniteProducts LawvereNatBTBoundedCat where
  terminal := lawvereNatBTBoundedTerminal
  product := lawvereNatBTBoundedProduct

end GebLean
