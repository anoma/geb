/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.InteractionNet.WiringEmbedding

set_option doc.verso true in
/-!
# Restricting a gluing schedule to an embedded component

A component observes exactly the cuts whose endpoints lie in its image. Cuts outside
the component leave it unchanged. Filtering the global schedule therefore gives the
component's own schedule and preserves its matching embedding throughout execution.

## Main statements

* {lit}`Wiring.Respects.force_outside` — a disjoint splice leaves an embedded matching intact.
* {lit}`Wiring.Respects.glue_select` — selecting the internal cuts preserves the embedding.

## Tags

interaction net, gluing, embedding, component, schedule, locality
-/

set_option doc.verso true

@[expose] public section

namespace Geb.InteractionNet.Wiring

variable {P Q I J : Type*} [DecidableEq P] [DecidableEq Q]

omit [DecidableEq P] in
/-- Splicing two endpoints outside a matching leaves its embedding unchanged. -/
theorem Respects.force_outside {e : P ↪ Q} {s : Wiring P} {t : Wiring Q}
    (h : Respects e s t) {a b : Q} (hab : a ≠ b)
    (ha : ∀ p, e p ≠ a) (hb : ∀ p, e p ≠ b) : Respects e s (t.force a b) :=
  fun p ↦ force_keeps t hab (ha p) (hb p) (ha (s.partner p)) (hb (s.partner p)) (h p)

/-- A component follows the subsequence of cuts that lie inside its endpoint image. -/
theorem Respects.glue_select {e : P ↪ Q} (ports : I × Bool ↪ P) (ports' : J × Bool ↪ Q)
    (select : J → Option I)
    (inside : ∀ j i, select j = some i → ∀ b, ports' (j, b) = e (ports (i, b)))
    (outside : ∀ j, select j = none → ∀ p b, e p ≠ ports' (j, b))
    (order : List J) (s : Wiring P × ℕ) (t : Wiring Q × ℕ) (h : Respects e s.1 t.1) :
    Respects e (Wiring.glue ports (order.filterMap select) s).1
      (Wiring.glue ports' order t).1 := by
  revert s t
  refine List.rec (fun _ _ h ↦ h) (fun j order ih s t h ↦ ?_) order
  cases hs : select j with
  | none =>
    simp only [List.filterMap_cons, hs]
    apply ih s (glueAt ports' t j)
    exact h.force_outside (pair_ne ports' j)
      (fun p ↦ outside j hs p false) (fun p ↦ outside j hs p true)
  | some i =>
    simp only [List.filterMap_cons, hs]
    apply ih (glueAt ports s i) (glueAt ports' t j)
    change Respects e (s.1.force (ports (i, false)) (ports (i, true)))
      (t.1.force (ports' (j, false)) (ports' (j, true)))
    rw [inside j i hs false, inside j i hs true]
    exact h.force (pair_ne ports i)

end Geb.InteractionNet.Wiring

end
