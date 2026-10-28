/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
-- Modified from geb-mathlib by scripts/geb-mathlib-backport.patch.
module

public import Geb.Prototypes.InteractionNet.Wiring
import Mathlib.Data.List.Basic

set_option doc.verso true in
/-!
# Wires specified by paired names

A finite list enumerates the endpoints without repetitions. When every name attached to
an endpoint appears exactly twice, searching for the other endpoint with the same name
constructs a fixed-point-free involution. The enumeration is explicit, so the construction
can use the occurrence order of a textual net without choosing a finite enumeration.

## Main definitions

* {lit}`Wiring.ofNames` — the matching specified by endpoint names of multiplicity two.

## Main statements

* {lit}`Wiring.ofNames_partner_name` — partners carry the same wire name.
* {lit}`Wiring.ofNames_partner_eq` — distinct endpoints with the same name are partners.

## Tags

interaction net, wire, name, occurrence, matching
-/

set_option doc.verso true

@[expose] public section

namespace Geb.InteractionNet.Wiring

universe u v

variable {P : Type u} {ν : Type v} [DecidableEq P] [BEq ν] [LawfulBEq ν]

attribute [local implicit_reducible] instDecidableEqOfLawfulBEq
attribute [local instance 5] instDecidableEqOfLawfulBEq

omit [DecidableEq P] in
private theorem two_endpoints (all : List P) (unique : all.Nodup)
    (cover : ∀ p, p ∈ all)
    (name : P → ν) (two : ∀ p, (all.map name).count (name p) = 2) (p : P) :
    ∃ q, q ≠ p ∧ name q = name p ∧ ∀ r, name r = name p → r = p ∨ r = q := by
  let ends := all.filter fun q ↦ decide (name q = name p)
  have hlen : ends.length = 2 := by
    have hm : (all.map name).count (name p) = ends.length := by
      simp only [List.count, List.countP_eq_length_filter, List.filter_map, List.length_map]
      simp only [Function.comp_def, Bool.beq_eq_decide_eq]
      rfl
    exact hm.symm.trans (two p)
  obtain ⟨a, b, hab⟩ := List.length_eq_two.mp hlen
  have hn : a ≠ b := by
    have h := unique.filter (fun q ↦ decide (name q = name p))
    change ends.Nodup at h
    rw [hab] at h
    exact fun he ↦ (List.nodup_cons.mp h).1 (by simp only [List.mem_singleton]; exact he)
  have hmem (r : P) : name r = name p ↔ r = a ∨ r = b := by
    have h : r ∈ ends ↔ name r = name p := by
      simp only [ends, List.mem_filter, cover r, decide_eq_true_eq, true_and]
    rw [hab, List.mem_cons, List.mem_singleton] at h
    exact h.symm
  rcases (hmem p).mp rfl with rfl | rfl
  · exact ⟨b, Ne.symm hn, (hmem b).mpr (Or.inr rfl), fun r hr ↦ (hmem r).mp hr⟩
  · exact ⟨a, hn, (hmem a).mpr (Or.inl rfl), fun r hr ↦ ((hmem r).mp hr).symm⟩

/-- Search the explicit endpoint enumeration for the other end with the same wire name. -/
def namedPartner? (all : List P) (name : P → ν) (p : P) : Option P :=
  all.find? fun q ↦ decide (q ≠ p ∧ name q = name p)

/-- A twice-occurring name makes the search for its other endpoint succeed. -/
theorem namedPartner?_isSome (all : List P) (unique : all.Nodup) (cover : ∀ p, p ∈ all)
    (name : P → ν) (two : ∀ p, (all.map name).count (name p) = 2) (p : P) :
    (namedPartner? all name p).isSome := by
  obtain ⟨q, hq, hn, _⟩ := two_endpoints all unique cover name two p
  exact List.find?_isSome.mpr ⟨q, cover q, by simp only [decide_eq_true_eq]; exact ⟨hq, hn⟩⟩

/-- Decode a named partner, using multiplicity only as a totality proof. -/
def namedPartner (all : List P) (unique : all.Nodup) (cover : ∀ p, p ∈ all)
    (name : P → ν) (two : ∀ p, (all.map name).count (name p) = 2) (p : P) : P :=
  (namedPartner? all name p).get (namedPartner?_isSome all unique cover name two p)

/-- The decoded partner is distinct and has the same name. -/
theorem namedPartner_spec (all : List P) (unique : all.Nodup) (cover : ∀ p, p ∈ all)
    (name : P → ν) (two : ∀ p, (all.map name).count (name p) = 2) (p : P) :
    namedPartner all unique cover name two p ≠ p ∧
      name (namedPartner all unique cover name two p) = name p := by
  have h := List.find?_some
    (Option.eq_some_of_isSome (namedPartner?_isSome all unique cover name two p))
  exact of_decide_eq_true h

/-- No second distinct endpoint with the same name can differ from the computed partner. -/
theorem namedPartner_eq (all : List P) (unique : all.Nodup) (cover : ∀ p, p ∈ all)
    (name : P → ν) (two : ∀ p, (all.map name).count (name p) = 2)
    {p q : P} (hne : q ≠ p) (hn : name q = name p) :
    namedPartner all unique cover name two p = q := by
  obtain ⟨r, _, _, hr⟩ := two_endpoints all unique cover name two p
  have hs := namedPartner_spec all unique cover name two p
  exact ((hr _ hs.2).resolve_left hs.1).trans ((hr q hn).resolve_left hne).symm

/-- Names of multiplicity two specify a computable fixed-point-free endpoint matching. -/
def ofNames (all : List P) (unique : all.Nodup) (cover : ∀ p, p ∈ all)
    (name : P → ν) (two : ∀ p, (all.map name).count (name p) = 2) : Wiring P where
  partner := namedPartner all unique cover name two
  involutive p :=
    let hs := namedPartner_spec all unique cover name two p
    namedPartner_eq all unique cover name two (Ne.symm hs.1) hs.2.symm
  fixedPointFree p := (namedPartner_spec all unique cover name two p).1

/-- Matching endpoints carry the same wire name. -/
theorem ofNames_partner_name (all : List P) (unique : all.Nodup) (cover : ∀ p, p ∈ all)
    (name : P → ν) (two : ∀ p, (all.map name).count (name p) = 2) (p : P) :
    name ((ofNames all unique cover name two).partner p) = name p :=
  (namedPartner_spec all unique cover name two p).2

/-- The matching joins any two distinct endpoints with the same name. -/
theorem ofNames_partner_eq (all : List P) (unique : all.Nodup) (cover : ∀ p, p ∈ all)
    (name : P → ν) (two : ∀ p, (all.map name).count (name p) = 2)
    {p q : P} (hne : q ≠ p) (hn : name q = name p) :
    (ofNames all unique cover name two).partner p = q :=
  namedPartner_eq all unique cover name two hne hn

end Geb.InteractionNet.Wiring

end
