/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
-- Modified from geb-mathlib by scripts/geb-mathlib-backport.patch.
module

public import Geb.Prototypes.InteractionNet.NamedWiring
public import Geb.Prototypes.InteractionNet.WiringEmbedding

set_option doc.verso true in
/-!
# Joining named wires

A splice joins the remaining ends of two wires and detaches the selected ends. If the two
wire names are identified, every resulting wire still joins equal names. Removing the
selected ends therefore produces the matching specified by the remaining name occurrences,
provided every remaining name has two occurrences. Joining distinct original name classes
creates no closed wire.

## Main statements

* {lit}`Wiring.ofNames_splice_respects` — merging two wire names agrees with a graph splice.
* {lit}`Wiring.loopDelta_eq_zero_of_names_ne` — distinct named wires create no closed component.

## Tags

interaction net, graph, wire, name, substitution, splice
-/

set_option doc.verso true

@[expose] public section

namespace Geb.InteractionNet.Wiring

variable {P Q ν μ : Type} [DecidableEq P] [DecidableEq Q]

omit [DecidableEq Q] in
/-- A splice preserves name classes after identifying the names of its selected endpoints. -/
theorem force_preserves_name (w : Wiring P) (name : P → ν)
    (names : ∀ p, name (w.partner p) = name p) {a b : P} (hab : a ≠ b)
    (same : name a = name b) (p : P) : name ((w.force a b).partner p) = name p := by
  rw [force_apply w hab]
  split_ifs with hpa hpb hwa hwb
  · subst p
    exact same.symm
  · subst p
    exact same
  · have hp := names p
    rw [hwa] at hp
    exact (names b).trans (same.symm.trans hp)
  · have hp := names p
    rw [hwb] at hp
    exact (names a).trans (same.trans hp)
  · exact names p

omit [DecidableEq Q] in
/-- Splicing different original name classes cannot close an existing wire. -/
theorem loopDelta_eq_zero_of_names_ne (w : Wiring P) (name : P → ν)
    (names : ∀ p, name (w.partner p) = name p) {a b : P} (different : name a ≠ name b) :
    w.loopDelta a b = 0 := by
  apply if_neg
  intro h
  exact different ((names a).symm.trans (congrArg name h))

variable [BEq μ] [LawfulBEq μ]

/-- A matching with equal names at both ends is determined by a two-occurrence name list. -/
theorem eq_ofNames (all : List Q) (unique : all.Nodup) (cover : ∀ q, q ∈ all)
    (name : Q → μ) (two : ∀ q, (all.map name).count (name q) = 2)
    (w : Wiring Q) (names : ∀ q, name (w.partner q) = name q) :
    w = ofNames all unique cover name two := by
  ext q
  exact (ofNames_partner_eq all unique cover name two (w.fixedPointFree q) (names q)).symm

/-- After a name merge, the remaining two-ended names describe the spliced matching. -/
theorem ofNames_splice_respects (w : Wiring P) (name : P → ν)
    (names : ∀ p, name (w.partner p) = name p) (rename : ν → μ)
    {a b : P} (hab : a ≠ b) (same : rename (name a) = rename (name b))
    (e : Q ≃ {p : P // p ≠ a ∧ p ≠ b})
    (all : List Q) (unique : all.Nodup) (cover : ∀ q, q ∈ all)
    (two : ∀ q, (all.map (fun p ↦ rename (name (e p).val))).count
      (rename (name (e q).val)) = 2) :
    Respects (e.toEmbedding.trans (.subtype _))
      (ofNames all unique cover (fun p ↦ rename (name (e p).val)) two) (w.force a b) := by
  let keep (p : P) := p ≠ a ∧ p ≠ b
  have closed : ∀ p, keep p → keep ((w.force a b).partner p) :=
    fun p hp ↦ force_closed w hab p hp
  let r := (w.force a b).restrict keep closed
  have hr : r.map e.symm = ofNames all unique cover
      (fun p ↦ rename (name (e p).val)) two := by
    apply eq_ofNames
    intro q
    change rename (name ((e (e.symm ⟨(w.force a b).partner (e q).val, _⟩)).val)) =
      rename (name (e q).val)
    rw [Equiv.apply_symm_apply]
    exact force_preserves_name w (fun p ↦ rename (name p))
      (fun p ↦ congrArg rename (names p)) hab same (e q).val
  have h := (respects_map_symm e.symm r).trans (respects_restrict (w.force a b) keep closed)
  rw [hr] at h
  exact h

end Geb.InteractionNet.Wiring

end
