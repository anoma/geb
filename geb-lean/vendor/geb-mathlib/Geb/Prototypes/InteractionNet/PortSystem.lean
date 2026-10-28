/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.InteractionNet.ContractionIso
public import Geb.Prototypes.InteractionNet.FiniteCells

set_option doc.verso true in
/-!
# Oriented finite graph rules

A rule table chooses at most one replacement for each ordered symbol pair and uses
only one orientation of any interacting pair. This is the orientation used by control/data
systems. A redex records a selected active pair and the rule returned by the table.
Renaming cells transports redexes and preserves their results up to isomorphism.

## Main definitions

* {lit}`PortSystem` — a rule table with one permitted orientation per interacting pair.
* {lit}`PortSystem.Redex` — an active pair with its selected rule.
* {lit}`PortSystem.Redex.result` — contraction of the selected pair.

## References

* \[DeFalco2010\], Corollary 5.4.

## Tags

interaction net, rule, active pair, orientation, renaming
-/

set_option doc.verso true

@[expose] public section

namespace Geb.InteractionNet

open scoped FinEnum

universe u v w x

variable {α : Type u} {arity : α → ℕ}

namespace PortRule

/-- Transport a rule body along equalities of its two interacting symbols. -/
def cast {a b a' b' : α} (r : PortRule arity a b) (ha : a' = a) (hb : b' = b) :
    PortRule arity a' b' :=
  ⟨r.1, r.2.1, r.2.2.reboundary
    (Equiv.sumCongr (finCongr (congrArg arity ha.symm)) (finCongr (congrArg arity hb.symm)))⟩

/-- Transport along reflexive symbol equalities does not change a rule body. -/
@[simp] theorem cast_refl {a b : α} (r : PortRule arity a b) : r.cast rfl rfl = r := by
  rcases r with ⟨k, label, n⟩
  apply congrArg (Sigma.mk k)
  apply congrArg (Sigma.mk label)
  apply PortNet.ext
  · change n.wiring.map _ = n.wiring
    have he : Equiv.sumCongr (finCongr (congrArg arity (Eq.refl a)))
        (finCongr (congrArg arity (Eq.refl b))) = Equiv.refl _ := by
      ext p
      cases p <;> rfl
    rw [he, endpointEquiv_refl, Wiring.map_refl]
  · rfl

end PortRule

/-- A finite-body rule table with a unique permitted orientation for each interacting pair. -/
structure PortSystem (arity : α → ℕ) where
  /-- The replacement selected for an ordered symbol pair. -/
  rule : (a b : α) → Option (PortRule arity a b)
  /-- A pair with a rule has no rule in the reverse orientation. -/
  oriented : ∀ a b r, rule a b = some r → rule b a = none

namespace PortSystem

variable {C : Type v} {D : Type w} {Γ : Type x}
variable {label : C → α} {label' : D → α}

/-- A selected active pair together with the rule that contracts it. -/
structure Redex (s : PortSystem arity) (n : PortNet arity label Γ) where
  /-- The first cell, in the rule's permitted orientation. -/
  left : C
  /-- The second cell. -/
  right : C
  /-- Their principal ports are connected. -/
  active : n.Active left right
  /-- The finite replacement graph. -/
  rhs : PortRule arity (label left) (label right)
  /-- The rule table selects this replacement. -/
  rule_eq : s.rule (label left) (label right) = some rhs

/-- Rule lookup transports along equalities of the interacting symbols. -/
theorem rule_cast (s : PortSystem arity) {a b a' b' : α} {r : PortRule arity a b}
    (h : s.rule a b = some r) (ha : a' = a) (hb : b' = b) :
    s.rule a' b' = some (r.cast ha hb) := by
  subst a'
  subst b'
  simpa only [PortRule.cast_refl] using h

namespace Redex

variable {s : PortSystem arity} {n : PortNet arity label Γ} {m : PortNet arity label' Γ}

/-- Transport a selected redex along a boundary-preserving cell renaming. -/
def map (r : s.Redex n) (i : n.Iso m) : s.Redex m where
  left := i.cells r.left
  right := i.cells r.right
  active := i.active r.active
  rhs := r.rhs.cast (i.label_eq r.left) (i.label_eq r.right)
  rule_eq := s.rule_cast r.rule_eq _ _

/-- The surviving input cells and newly allocated replacement cells. -/
abbrev ResultCell (r : s.Redex n) := PortNet.RemainingCell r.left r.right ⊕ Fin r.rhs.1

/-- Symbols on the surviving input cells and inserted replacement cells. -/
def resultLabel (r : s.Redex n) : r.ResultCell → α :=
  Sum.elim (fun c ↦ label c.val) r.rhs.2.1

variable [DecidableEq C] [DecidableEq Γ]

/-- Contract the selected active pair. -/
def result (r : s.Redex n) : PortNet arity r.resultLabel Γ := n.contract r.active r.rhs.2.2

/-- The result's cells can be enumerated whenever the input's cells can be enumerated. -/
@[instance_reducible] def resultEnum [FinEnum C] (r : s.Redex n) : FinEnum r.ResultCell :=
  letI := PortNet.subtypeEnum (fun c ↦ c ≠ r.left ∧ c ≠ r.right)
  inferInstance

/-- Transporting a redex preserves its contracted graph up to cell renaming. -/
def mapIso [DecidableEq D] (r : s.Redex n) (i : n.Iso m) :
    r.result.Iso (r.map i).result := i.contract r.active r.rhs.2.2

end Redex

end PortSystem

end Geb.InteractionNet

end
