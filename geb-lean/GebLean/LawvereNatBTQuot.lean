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

end GebLean
