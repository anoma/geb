/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
-- Modified from geb-mathlib by scripts/geb-mathlib-backport.patch.
module

public import Geb.Prototypes.FreeTopos.Represent

set_option doc.verso true in
/-!
# The value of an arrow term with a domain and a codomain

In the topos of types and functional relations, a term whose domain and codomain are defined
and are the values of two object terms, types, has a value, a functional relation between those
types: the operations are strict, so the term is defined where its domain is, and the domain
and the codomain of an arrow's value are the types it relates. The typing of a term of the
internal language gives the hypotheses, as equations valid in every model of the theory
({lit}`Geb.FreeTopos.Internal.hom_unfoldAll_of_compile`).

## Main statements

* {lit}`exists_arrVal_of_dom_cod` — a term with a domain and a codomain has a functional
  relation between them as its value.

## Tags

functional relation, model, elementary topos, partial Horn logic
-/

set_option doc.verso true

@[expose] public section

namespace Geb.FreeTopos

open PartialHorn Sorts

variable {ρ : List relTopos.model.Val} {A B : Type}

/-- A term whose domain and codomain are defined, and are the values of object terms whose
values are types, has a functional relation between those types as its value. -/
theorem exists_arrVal_of_dom_cod {g X Y : Tree}
    (hd : ∃ w, eval relTopos.model ρ (dom g) = Part.some w ∧
      eval relTopos.model ρ X = Part.some w)
    (hc : ∃ w, eval relTopos.model ρ (cod g) = Part.some w ∧
      eval relTopos.model ρ Y = Part.some w)
    (hX : ObjVal ρ X A) (hY : ObjVal ρ Y B) : ∃ φ : FunRel A B, ArrVal ρ g φ := by
  obtain ⟨w, hw, hXw⟩ := hd
  obtain ⟨w', hw', hYw⟩ := hc
  unfold ObjVal at hX hY
  obtain rfl := Part.some_injective (hXw.symm.trans hX)
  obtain rfl := Part.some_injective (hYw.symm.trans hY)
  rw [dom, eval_op] at hw
  rw [cod, eval_op] at hw'
  obtain ⟨vs, hvs, hop⟩ := part_bind_eq_some_iff.mp hw
  obtain ⟨vs', hvs', hop'⟩ := part_bind_eq_some_iff.mp hw'
  rw [mapM_part_eq_some_iff] at hvs hvs'
  obtain ⟨v, rfl⟩ : ∃ v, vs = [v] := by
    rcases vs with _ | ⟨v, _ | ⟨u, vs⟩⟩
    · simp at hvs
    · exact ⟨v, rfl⟩
    · simp at hvs
  obtain ⟨v', rfl⟩ : ∃ v, vs' = [v] := by
    rcases vs' with _ | ⟨v, _ | ⟨u, vs⟩⟩
    · simp at hvs'
    · exact ⟨v, rfl⟩
    · simp at hvs'
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hvs hvs'
  obtain rfl := Part.some_injective (hvs.symm.trans hvs')
  obtain ⟨s, c⟩ := v
  rcases s with _ | _ | s
  · exact (Part.some_ne_none _
      (hop.symm.trans (show relTopos.model.op 0 [⟨0, c⟩] = Part.none from rfl))).elim
  · obtain ⟨A', B', φ⟩ := c
    have e₁ := Part.some_injective
      ((show relTopos.model.op 0 [⟨1, ⟨A', B', φ⟩⟩] = Part.some ⟨obj, ⟨A'⟩⟩ from rfl).symm.trans
        hop)
    have e₂ := Part.some_injective
      ((show relTopos.model.op 1 [⟨1, ⟨A', B', φ⟩⟩] = Part.some ⟨obj, ⟨B'⟩⟩ from rfl).symm.trans
        hop')
    obtain rfl : A' = A := congrArg ULift.down.{0} (by simpa using e₁)
    obtain rfl : B' = B := congrArg ULift.down.{0} (by simpa using e₂)
    exact ⟨φ, by delta ArrVal; exact hvs⟩
  · exact (Part.some_ne_none _
      (hop.symm.trans (show relTopos.model.op 0 [⟨s + 1 + 1, c⟩] = Part.none from rfl))).elim

end Geb.FreeTopos

end
