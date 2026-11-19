/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.FreeTopos.Represent

set_option doc.verso true in
/-!
# The representation of the natural numbers

In the topos of types and functional relations the natural numbers object is Lean's type of
natural numbers, zero and the successor the graphs of Lean's, and recursion with a start and a
step the fold that relates a number to the value of the step iterated from the start. The
numbers are represented by themselves; zero, the successor and recursion then represent Lean's:
recursion with a start and a step that represent functions represents the recursor of the
natural numbers at them.

## Main definitions

* {lit}`Rep.nat` — the representation of the natural numbers, by themselves.

## Main statements

* {lit}`eval_zeroN`, {lit}`eval_succ`, {lit}`eval_natRec` — the values of zero, the successor
  and recursion.
* {lit}`represents_zeroN`, {lit}`represents_succ`, {lit}`represents_natRec` — they represent
  Lean's.

## Tags

functional relation, logical relation, representation, natural numbers object
-/

set_option doc.verso true

@[expose] public section

namespace Geb.FreeTopos

open PartialHorn Sorts SetRel

variable {ρ : List relTopos.model.Val} {S T C : Type}

/-- The representation of the natural numbers, by themselves. -/
def Rep.nat : ℕ → ℕ → Prop := fun m n ↦ m = n

/-- The value of zero. -/
theorem eval_zeroN : ArrVal ρ zeroN (FunRel.ofFun fun _ : Unit ↦ 0) := by
  simp only [ArrVal]
  simp only [zeroN, eval_op, List.mapM_nil, Part.bind_some, Part.pure_eq_some]
  rfl

/-- The value of the successor. -/
theorem eval_succ : ArrVal ρ succ (FunRel.ofFun Nat.succ) := by
  simp only [ArrVal]
  simp only [succ, eval_op, List.mapM_nil, Part.bind_some, Part.pure_eq_some]
  rfl

/-- The value of the recursion of the natural numbers with a start and a step. -/
theorem eval_natRec {z s : Tree} {φ : FunRel Unit C} {ψ : FunRel C C} (hz : ArrVal ρ z φ)
    (hs : ArrVal ρ s ψ) : ArrVal ρ (natRec z s) (FunRel.natRec φ ψ) := by
  simp only [ArrVal] at *
  simp only [natRec, eval_op, List.mapM_cons, List.mapM_nil, hz, hs, Part.bind_eq_bind,
    Part.bind_some, Part.pure_eq_some]
  exact ChosenTopos.mk_eq_some ⟨rfl, rfl, rfl⟩

/-- Zero represents zero. -/
theorem represents_zeroN : Represents ρ zeroN Rep.unit Rep.nat fun _ ↦ 0 :=
  ⟨_, eval_zeroN, fun _ _ _ _ hb ↦ FunRel.mem_ofFun.mp hb⟩

/-- The successor represents the successor. -/
theorem represents_succ : Represents ρ succ Rep.nat Rep.nat Nat.succ :=
  ⟨_, eval_succ, fun _ _ h _ hb ↦ by
    obtain rfl : _ = _ := h
    exact FunRel.mem_ofFun.mp hb⟩

/-- The recursion of the natural numbers with a start and a step that represent functions
represents the recursor of the natural numbers at them. -/
theorem represents_natRec {z s : Tree} {R' : T → C → Prop} {Z : Unit → T} {St : T → T}
    (hz : Represents ρ z Rep.unit R' Z) (hs : Represents ρ s R' R' St) :
    Represents ρ (natRec z s) Rep.nat R'
      fun n ↦ Nat.rec (motive := fun _ ↦ T) (Z ()) (fun _ ↦ St) n :=
  let ⟨φ, hφ, hZ⟩ := hz
  let ⟨ψ, hψ, hS⟩ := hs
  ⟨_, eval_natRec hφ hψ, fun n n' hn ↦ by
    obtain rfl : n = n' := hn
    exact Nat.rec
      (motive := fun n ↦ ∀ c, FunRel.natRel φ ψ n c →
        R' (Nat.rec (motive := fun _ ↦ T) (Z ()) (fun _ ↦ St) n) c)
      (fun c hc ↦ hZ () () trivial c hc)
      (fun _ ih c ⟨c', hc', hc⟩ ↦ hS _ _ (ih c' hc') c hc) n⟩

end Geb.FreeTopos

end
