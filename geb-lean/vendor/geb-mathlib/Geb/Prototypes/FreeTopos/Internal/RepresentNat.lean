/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.FreeTopos.Internal.Represent
public import Geb.Prototypes.FreeTopos.RepresentNat

set_option doc.verso true in
/-!
# The natural numbers of the internal language represent Lean's

A term of the internal language's natural numbers represents a function into Lean's
({name}`Geb.FreeTopos.Rep.nat`): zero and the successor, the primitive arrows of the natural
numbers object a program's constants name ({name}`Geb.FreeTopos.Internal.zeroPrim`,
{name}`Geb.FreeTopos.Internal.succPrim`), represent Lean's, and the fold of a number from a
closed start by a step in its bound variable alone represents the recursor of the natural
numbers at the functions they represent.

## Main statements

* {lit}`repC_zeroN`, {lit}`repC_succ` — zero and a successor represent Lean's.
* {lit}`repC_natRec` — the fold of a number represents the recursor of the natural numbers.

## Tags

internal language, logical relation, representation, natural numbers object
-/

set_option doc.verso true

@[expose] public section

namespace Geb.FreeTopos.Internal

open PartialHorn (Tree op)
open Sorts

variable {G : Globals} {n : ℕ} {ds : List PartialHorn.Defn} {ρ : List relTopos.model.Val}
  {S A T C : Type}

/-- The value of the natural numbers object, unfolded. -/
theorem objVal_nat : ObjVal ρ (unfoldTerm sig ds nat) ℕ := by
  simp (disch := decide) only [nat, unfold_op', List.map_nil]
  exact eval_nat

/-- Zero, the primitive arrow of the natural numbers object at the element of the terminal
object, represents the function to zero. -/
theorem repC_zeroN {k : ℕ} (hk : G.prims[k]? = some zeroPrim) {X : Tree}
    {e : List (Tree × Tree)} (hX : ObjVal ρ (unfoldTerm sig ds X) A) (R : S → A → Prop) :
    RepC G n ds ρ (Term.arr k [] Term.star) X e nat R Rep.nat fun _ ↦ 0 :=
  ⟨comp zeroN (bang X), compile_arr_iff.mpr ⟨Term.star, rfl, zeroPrim, hk, bang X,
    compile_star_iff.mpr ⟨rfl, by simp [zeroPrim, one, subst_op]⟩, rfl, rfl,
    by simp [zeroPrim, zeroN, nat, subst_op]⟩, by
    simp (disch := decide) only [comp, bang, zeroN, unfold_op', List.map_cons, List.map_nil]
    exact represents_comp (F := fun _ ↦ ()) (G := fun _ ↦ 0) (represents_bang hX R)
      represents_zeroN⟩

/-- A successor, the primitive arrow of the natural numbers object at a number, represents the
successor of the function the number represents. -/
theorem repC_succ {k : ℕ} (hk : G.prims[k]? = some succPrim) {X : Tree}
    {e : List (Tree × Tree)} {t : Term} {R : S → A → Prop} {F : S → ℕ}
    (ht : RepC G n ds ρ t X e nat R Rep.nat F) :
    RepC G n ds ρ (Term.arr k [] t) X e nat R Rep.nat fun s ↦ (F s).succ :=
  let ⟨g, hg, hG⟩ := ht
  ⟨comp succ g, compile_arr_iff.mpr ⟨t, rfl, succPrim, hk, g,
    by simpa [succPrim, nat, subst_op] using hg, rfl, rfl,
    by simp [succPrim, succ, nat, subst_op]⟩, by
    simp (disch := decide) only [comp, succ, unfold_op', List.map_cons, List.map_nil]
    exact represents_comp hG represents_succ⟩

/-- The fold of a natural number, from a closed start by a step in its bound variable alone,
represents the recursor of the natural numbers at the functions the start and the step
represent. -/
theorem repC_natRec {X : Tree} {e : List (Tree × Tree)} {z s m : Term} {c : Tree}
    {R : S → A → Prop} {Rc : T → C → Prop} {M : S → ℕ} {Z : Unit → T} {St : T → T}
    (hm : RepC G n ds ρ m X e nat R Rep.nat M) (hz : RepC G n ds ρ z one [] c Rep.unit Rc Z)
    (hs : RepC G n ds ρ s c (stdEnv [c]) c Rc Rc St) :
    RepC G n ds ρ (Term.natRec z s m) X e c R Rc
      fun x ↦ Nat.rec (motive := fun _ ↦ T) (Z ()) (fun _ ↦ St) (M x) := by
  obtain ⟨m', hm', hM⟩ := hm
  obtain ⟨z', hz', hZ⟩ := hz
  obtain ⟨s', hs', hS⟩ := hs
  -- a start in the empty environment and a step in the bound variable's make a fold without
  -- parameters
  have hq : ∀ i, (Term.occurs z i || Term.occurs s (i + 1)) = false := fun i ↦ by
    have h₁ : Term.occurs z i = false := Bool.eq_false_iff.mpr fun h ↦
      Nat.not_lt_zero _ (compile_occurs_lt z one [] _ hz' i h)
    have h₂ : Term.occurs s (i + 1) = false := Bool.eq_false_iff.mpr fun h ↦
      Nat.lt_irrefl 1 (Nat.lt_of_le_of_lt (Nat.le_add_left 1 i) (compile_occurs_lt s _ _ _ hs' _ h))
    rw [h₁, h₂]
    rfl
  have hp : foldParams 1 e.length z s = [] := by
    unfold foldParams
    generalize List.range e.length = l
    exact l.rec rfl fun i l ih ↦ by
      simp only [List.filter_cons, hq i, Bool.false_eq_true, ↓reduceIte]
      exact ih
  refine ⟨comp (natRec z' s') m', compile_natRec_iff.mpr ⟨z, s, m, rfl, z', c,
    by rw [foldEnvIn_closed hp]; exact hz', s', by rw [foldEnvIn_closed hp]; exact hs', m', hm',
    by rw [foldPs_closed hp]; rfl⟩, ?_⟩
  simp (disch := decide) only [comp, natRec, unfold_op', List.map_cons, List.map_nil]
  exact represents_comp hM (represents_natRec hZ hS)

end Geb.FreeTopos.Internal

end
