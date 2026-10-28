/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.InteractionNet.GraphReadback

set_option doc.verso true in
/-!
# Boundary renaming preserves constructor traversal

Renaming a net's external boundary leaves all cells and their ordered ports unchanged.
Reading at the corresponding endpoint therefore produces the same constructor tree and
the same list of visited cells, at every traversal bound.

## Main statements

* {lit}`PortNet.readTree_reboundary` — boundary renaming preserves bounded traversal.

## Tags

interaction net, graph, read-back, boundary, renaming
-/

set_option doc.verso true

@[expose] public section

namespace Geb.InteractionNet.PortNet

variable {α C Γ Δ : Type} {arity : α → ℕ} {label : C → α}

/-- External boundary renaming preserves every observed constructor and visited cell. -/
theorem readTree_reboundary (tag : α → Option ℕ) (n : PortNet arity label Γ)
    (e : Γ ≃ Δ) (fuel : ℕ) (p : Endpoint arity label Γ) :
    (n.reboundary e).readTree tag fuel
      (endpointEquiv arity e (Equiv.refl C) (fun _ ↦ rfl) p) = n.readTree tag fuel p := by
  let ep := endpointEquiv (label := label) (label' := label)
    arity e (Equiv.refl C) (fun _ ↦ rfl)
  refine Nat.rec (motive := fun fuel ↦ ∀ p : Endpoint arity label Γ,
    (n.reboundary e).readTree tag fuel (ep p) = n.readTree tag fuel p)
    (fun _ ↦ rfl) (fun fuel ih p ↦ ?_) fuel p
  have he := Wiring.map_partner ep n.wiring p
  change (n.reboundary e).wiring.partner (ep p) = ep (n.wiring.partner p) at he
  simp only [PortNet.readTree]
  rw [he]
  cases hp : n.wiring.partner p with
  | inl b => rfl
  | inr cp =>
    rcases cp with ⟨c, q⟩
    change (if q.val = 0 then PortNet.readNode tag (label c) c
      (fun i ↦ (n.reboundary e).readTree tag fuel (.inr ⟨c, i.succ⟩)) else none) =
        if q.val = 0 then PortNet.readNode tag (label c) c
          (fun i ↦ n.readTree tag fuel (.inr ⟨c, i.succ⟩)) else none
    by_cases hq : q.val = 0
    · simp only [hq, ↓reduceIte]
      exact congrArg (PortNet.readNode tag (label c) c)
        (funext fun i ↦ ih (.inr ⟨c, i.succ⟩))
    · simp only [hq, ↓reduceIte]

end Geb.InteractionNet.PortNet

end
