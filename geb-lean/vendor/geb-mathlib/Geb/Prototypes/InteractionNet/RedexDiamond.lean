/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
-- Modified from geb-mathlib by scripts/geb-mathlib-backport.patch.
module

public import Geb.Prototypes.InteractionNet.PortSystem
public import Geb.Prototypes.InteractionNet.ContractionCommute

set_option doc.verso true in
/-!
# The active-pair diamond

Two selected redexes either coincide or occupy disjoint cells. Unique rule lookup
identifies coincident contractions. The rule table's orientation excludes opposite
orientations of one pair. Disjoint contractions have residual redexes whose results are
isomorphic by the graph commutation theorem.

## Main definitions

* {lit}`PortSystem.Redex.residual` — a disjoint redex after another contraction.

## Main statements

* {lit}`PortSystem.Redex.diamond` — every fork closes in at most one contraction per branch.

## References

* \[DeFalco2010\], Proposition 5.3 and Corollary 5.4.

## Tags

interaction net, active pair, residual, diamond, confluence
-/

set_option doc.verso true

@[expose] public section

namespace Geb.InteractionNet.PortSystem.Redex

open scoped FinEnum

universe u v w

variable {α : Type u} {C : Type v} {Γ : Type w}
variable {arity : α → ℕ} {label : C → α} {s : PortSystem arity} {n : PortNet arity label Γ}

/-- Two redexes beginning at the same principal port are the same selected rule application. -/
theorem eq_of_left_eq (r q : s.Redex n) (h : r.left = q.left) : r = q := by
  rcases r with ⟨a, b, hab, rhs, hr⟩
  rcases q with ⟨c, d, hcd, rhs', hq⟩
  dsimp only at h
  subst c
  have hbd := PortNet.active_right_unique hab hcd
  subst d
  have he := Option.some.inj (hr.symm.trans hq)
  subst rhs'
  rfl

/-- The orientation condition excludes two redexes that select the same pair in reverse. -/
theorem left_ne_right (r q : s.Redex n) : r.left ≠ q.right := by
  intro h
  have hb := PortNet.active_right_unique r.active
    (show n.Active r.left q.left by simpa only [h] using PortNet.active_symm q.active)
  have ho := s.oriented (label r.left) (label r.right) r.rhs r.rule_eq
  have he := congrArg₂ (fun a b ↦ (s.rule (label a) (label b)).isSome) hb h
  beta_reduce at he
  rw [ho, q.rule_eq] at he
  cases he

variable [DecidableEq C] [DecidableEq Γ]

/-- A disjoint selected redex survives contraction with the same rule body. -/
def residual (r q : s.Redex n) (hll : r.left ≠ q.left) (hlr : r.left ≠ q.right)
    (hrl : r.right ≠ q.left) (hrr : r.right ≠ q.right) : s.Redex r.result where
  left := .inl ⟨q.left, hll.symm, hrl.symm⟩
  right := .inl ⟨q.right, hlr.symm, hrr.symm⟩
  active := n.contract_active r.active r.rhs.2.2 _ _ q.active
  rhs := q.rhs
  rule_eq := q.rule_eq

/-- The two residual contractions of disjoint redexes have isomorphic results. -/
def residualIso (r q : s.Redex n) (hll : r.left ≠ q.left) (hlr : r.left ≠ q.right)
    (hrl : r.right ≠ q.left) (hrr : r.right ≠ q.right) :
    (r.residual q hll hlr hrl hrr).result.Iso
      (q.residual r hll.symm hrl.symm hlr.symm hrr.symm).result :=
  n.contractCommute r.active q.active hll hlr hrl hrr r.rhs.2.2 q.rhs.2.2

/-- Any two selected contractions coincide or have one-step residuals with isomorphic results. -/
theorem diamond (r q : s.Redex n) :
    Nonempty (r.result.Iso q.result) ∨
      ∃ r' : s.Redex r.result, ∃ q' : s.Redex q.result,
        Nonempty (r'.result.Iso q'.result) := by
  by_cases h : r.left = q.left
  · have he := r.eq_of_left_eq q h
    subst q
    exact Or.inl ⟨PortNet.Iso.refl _⟩
  · have hlr := r.left_ne_right q
    have hd := PortNet.active_disjoint r.active q.active h hlr
    exact Or.inr ⟨r.residual q h hlr hd.1 hd.2,
      q.residual r (Ne.symm h) hd.1.symm hlr.symm hd.2.symm,
      ⟨r.residualIso q h hlr hd.1 hd.2⟩⟩

end Geb.InteractionNet.PortSystem.Redex

end
