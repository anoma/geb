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

end GebLean
