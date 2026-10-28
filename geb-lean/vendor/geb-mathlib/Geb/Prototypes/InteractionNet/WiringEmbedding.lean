/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.InteractionNet.WiringGlue

set_option doc.verso true in
/-!
# Matching embeddings and local graph operations

A matching embeds in a larger matching when the endpoint injection preserves partners.
The extra endpoints then form separate components. Splicing endpoints in the image
preserves this correspondence, including the number of closed wires created. This allows
contractions to be compared in one common graph containing both fresh replacements.

## Main definitions

* {lit}`Wiring.Respects` — an endpoint injection preserves the wire matching.

## Main statements

* {lit}`Wiring.Respects.force` — corresponding splices preserve a matching embedding.
* {lit}`Wiring.Respects.glue` — finite gluing preserves the embedding and closed-wire counts.

## Tags

interaction net, graph embedding, matching, gluing, locality
-/

set_option doc.verso true

@[expose] public section

namespace Geb.InteractionNet.Wiring

universe u v w x y

variable {P : Type u} {Q : Type v} {R : Type w}

/-- An endpoint injection preserves each wire's partner. -/
def Respects (e : P ↪ Q) (s : Wiring P) (t : Wiring Q) : Prop :=
  ∀ p, t.partner (e p) = e (s.partner p)

/-- The identity injection preserves a matching. -/
theorem respects_refl (s : Wiring P) : Respects (.refl P) s s := fun _ ↦ rfl

/-- Matching-preserving injections compose. -/
theorem Respects.trans {e : P ↪ Q} {f : Q ↪ R} {s : Wiring P} {t : Wiring Q} {v : Wiring R}
    (h : Respects e s t) (h' : Respects f t v) : Respects (e.trans f) s v := by
  intro p
  exact (h' (e p)).trans (congrArg f (h p))

/-- Inclusion of a closed collection of endpoints preserves partners. -/
theorem respects_restrict (s : Wiring P) (p : P → Prop)
    (h : ∀ x, p x → p (s.partner x)) :
    Respects (.subtype p) (s.restrict p h) s := fun _ ↦ rfl

/-- Renaming gives a matching-preserving endpoint injection. -/
theorem respects_map (e : P ≃ Q) (s : Wiring P) :
    Respects e.toEmbedding s (s.map e) := map_partner e s

/-- Undoing a renaming gives a matching-preserving endpoint injection. -/
theorem respects_map_symm (e : P ≃ Q) (s : Wiring P) :
    Respects e.symm.toEmbedding (s.map e) s := by
  intro q
  simp only [map, Equiv.symm_apply_apply, Equiv.toEmbedding_apply]

/-- Disjoint union preserves matching embeddings on both sides. -/
theorem Respects.sum {P' : Type x} {Q' : Type y}
    {e : P ↪ Q} {e' : P' ↪ Q'} {s : Wiring P} {t : Wiring Q}
    {s' : Wiring P'} {t' : Wiring Q'} (h : Respects e s t) (h' : Respects e' s' t') :
    Respects (e.sumMap e') (s.sum s') (t.sum t') := by
  intro p
  cases p with
  | inl p => exact congrArg Sum.inl (h p)
  | inr p => exact congrArg Sum.inr (h' p)

/-- A matching embeds in a disjoint union as its left component. -/
theorem respects_inl (s : Wiring P) (t : Wiring Q) :
    Respects .inl s (s.sum t) := fun _ ↦ rfl

/-- A matching embeds in a disjoint union as its right component. -/
theorem respects_inr (s : Wiring P) (t : Wiring Q) :
    Respects .inr t (s.sum t) := fun _ ↦ rfl

/-- Two embedded matchings agree under a bijection when their ambient endpoints agree. -/
theorem Respects.map_eq {e : P ↪ R} {f : Q ↪ R} {s : Wiring P} {t : Wiring Q} {v : Wiring R}
    (h : Respects e s v) (h' : Respects f t v) (k : P ≃ Q) (hk : ∀ p, e p = f (k p)) :
    s.map k = t := by
  ext q
  obtain ⟨p, rfl⟩ := k.surjective q
  rw [map_partner]
  apply f.injective
  calc
    f (k (s.partner p)) = e (s.partner p) := (hk _).symm
    _ = v.partner (e p) := (h p).symm
    _ = v.partner (f (k p)) := congrArg v.partner (hk p)
    _ = f (t.partner (k p)) := h' (k p)

variable [DecidableEq P] [DecidableEq Q]

/-- Splicing endpoints in an embedding's image preserves that embedding. -/
theorem Respects.force {e : P ↪ Q} {s : Wiring P} {t : Wiring Q}
    (h : Respects e s t) {a b : P} (hab : a ≠ b) :
    Respects e (s.force a b) (t.force (e a) (e b)) := by
  intro p
  rw [force_apply _ (fun he ↦ hab (e.injective he)), force_apply _ hab, h p, h a, h b]
  simp only [e.injective.eq_iff]
  split_ifs <;> rfl

/-- Corresponding splices create the same number of closed wires. -/
theorem Respects.loopDelta {e : P ↪ Q} {s : Wiring P} {t : Wiring Q}
    (h : Respects e s t) (a b : P) : s.loopDelta a b = t.loopDelta (e a) (e b) := by
  simp only [Wiring.loopDelta, h a, e.injective.eq_iff]

/-- Corresponding finite gluings preserve the matching embedding and the closed-wire count. -/
theorem Respects.glue {I : Type*} {e : P ↪ Q} (ports : I × Bool ↪ P) (order : List I)
    (s : Wiring P × ℕ) (t : Wiring Q × ℕ) (h : Respects e s.1 t.1) (hl : s.2 = t.2) :
    Respects e (Wiring.glue ports order s).1
      (Wiring.glue (ports.trans e) order t).1 ∧
      (Wiring.glue ports order s).2 = (Wiring.glue (ports.trans e) order t).2 := by
  revert s t
  refine List.rec (fun _ _ h hl ↦ ⟨h, hl⟩) ?_ order
  intro i order ih s t h hl
  apply ih (glueAt ports s i) (glueAt (ports.trans e) t i)
  · exact h.force (pair_ne ports i)
  · exact congrArg₂ Nat.add hl (h.loopDelta _ _)

/-- The surviving matching embeds in the ambient matching after all gluing operations. -/
theorem respects_glued {I : Type*} (ports : I × Bool ↪ P) (order : List I)
    (unique : order.Nodup) (cover : ∀ i, i ∈ order) (s : Wiring P × ℕ) :
    Respects (.subtype _) (glued ports order unique cover s).1 (Wiring.glue ports order s).1 :=
  respects_restrict _ _ (glue_closed ports order cover s)

/-- Matching embeddings preserve gluing with a fixed offset in the closed-wire count. -/
theorem Respects.glue_offset {I : Type*} {e : P ↪ Q} (ports : I × Bool ↪ P) (order : List I)
    (s : Wiring P × ℕ) (t : Wiring Q × ℕ) (h : Respects e s.1 t.1)
    (extra : ℕ) (hl : s.2 + extra = t.2) :
    Respects e (Wiring.glue ports order s).1
      (Wiring.glue (ports.trans e) order t).1 ∧
      (Wiring.glue ports order s).2 + extra = (Wiring.glue (ports.trans e) order t).2 := by
  revert s t
  refine List.rec (fun _ _ h hl ↦ ⟨h, hl⟩) ?_ order
  intro i order ih s t h hl
  apply ih (glueAt ports s i) (glueAt (ports.trans e) t i)
  · exact h.force (pair_ne ports i)
  · have hd := h.loopDelta (ports (i, false)) (ports (i, true))
    dsimp only [glueAt]
    change (s.2 + s.1.loopDelta (ports (i, false)) (ports (i, true))) + extra =
      t.2 + t.1.loopDelta (e (ports (i, false))) (e (ports (i, true)))
    rw [hd]
    omega

omit [DecidableEq P] in
/-- Gluing outside a matching's image preserves that embedded matching. -/
theorem Respects.glue_outside {I : Type*} {e : P ↪ Q} {s : Wiring P} {t : Wiring Q}
    (h : Respects e s t) (ports : I × Bool ↪ Q) (order : List I) (loops : ℕ)
    (outside : ∀ i b p, e p ≠ ports (i, b)) :
    Respects e s (Wiring.glue ports order (t, loops)).1 := by
  intro p
  exact glue_keeps ports order (t, loops) (fun i b ↦ outside i b p)
    (fun i b ↦ outside i b (s.partner p)) (h p)

end Geb.InteractionNet.Wiring

end
