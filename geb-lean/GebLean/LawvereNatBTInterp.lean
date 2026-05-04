import GebLean.LawvereNatBTQuot
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Functor.FullyFaithful

/-!
# Interpretation Functor for `LawvereNatBTCat`

Sends an object `(n, m)` to the set `(Fin n → ℕ) × (Fin m → BTL)`
and each morphism class to its componentwise interpretation.
Faithfulness witnesses that extensionally distinct morphism
classes produce distinct interpretations.
-/

namespace GebLean

open CategoryTheory

/-- Interpretation functor: `(n, m) ↦ (Fin n → ℕ) × (Fin m → BTL)`
on objects; on morphism classes, apply `NatBTMorN.interp`
(well-definedness comes from the extensional-equality setoid). -/
def natBTInterpFunctor : LawvereNatBTCat ⥤ Type where
  obj nm := (Fin nm.1 → ℕ) × (Fin nm.2 → BTL)
  map {_ _} f := fun ctx =>
    Quotient.liftOn f
      (fun f' => f'.interp ctx.1 ctx.2)
      (fun _ _ h => h ctx.1 ctx.2)
  map_id nm := by
    funext ctx
    change (NatBTMorN.id nm).interp ctx.1 ctx.2 = ctx
    simp
  map_comp {_ _ _} f g := by
    funext ctx
    refine Quotient.inductionOn₂ f g ?_
    intro a b
    change (NatBTMorN.comp a b).interp ctx.1 ctx.2 =
      b.interp (a.interp ctx.1 ctx.2).1 (a.interp ctx.1 ctx.2).2
    simp

instance : natBTInterpFunctor.Faithful where
  map_injective {_ _} {f g} h := by
    revert h
    refine Quotient.inductionOn₂ f g ?_
    intro a b hab
    apply Quotient.sound
    intro ctxN ctxB
    exact congrFun hab ⟨ctxN, ctxB⟩

end GebLean
