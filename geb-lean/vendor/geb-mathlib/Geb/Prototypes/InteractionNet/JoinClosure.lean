/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.InteractionNet.BoundaryJoin
public import Geb.Prototypes.InteractionNet.PlugEmbedding
public import Geb.Prototypes.InteractionNet.PartialClosure
public import Geb.Prototypes.InteractionNet.WiringCompose

set_option doc.verso true in
/-!
# Joining before closing a replacement graph

The shared argument boundary and the replacement's internal boundary occupy disjoint
positions. Closing the internal boundary before insertion therefore gives the same graph
as joining the open replacement first and closing its internal positions afterwards.

## Main statements

* {lit}`PortNet.plug_close` — insertion commutes with closing the replacement's other boundary.

## Tags

interaction net, insertion, join, partial closure, interchange
-/

set_option doc.verso true

@[expose] public section

namespace Geb.InteractionNet.PortNet

open scoped FinEnum

variable {α C D Γ I B : Type} {arity : α → ℕ} {label : C → α} {label' : D → α}
variable [FinEnum C] [FinEnum D] [FinEnum Γ] [FinEnum I] [FinEnum B]
variable [DecidableEq C] [DecidableEq D] [DecidableEq Γ] [DecidableEq I] [DecidableEq B]

private abbrev Ambient (arity : α → ℕ) (label : C → α) (label' : D → α) (Γ I B : Type) :=
  B ⊕ JoinEndpoint arity label label' Γ I B

private def ambientDecidableEq : DecidableEq (Ambient arity label label' Γ I B) :=
  let := sigmaEnum (C := fun c ↦ Fin (arity (label c) + 1))
  let := sigmaEnum (C := fun c ↦ Fin (arity (label' c) + 1))
  inferInstance

private local instance : DecidableEq (Ambient arity label label' Γ I B) := ambientDecidableEq

private def sharedPorts : I × Bool ↪ Ambient arity label label' Γ I B :=
  (joinPorts arity label label' Γ I B).trans .inr

private def rightEmbedding : ClosureEndpoint arity label' I B ↪
    Ambient arity label label' Γ I B :=
  Function.Embedding.sumMap (.refl _) .inr

private def closedPorts : B × Bool ↪ Ambient arity label label' Γ I B :=
  (closePorts arity label' I B).trans rightEmbedding

private def joinedEmbedding : ClosureEndpoint arity (Sum.elim label label') Γ B ↪
    Ambient arity label label' Γ I B :=
  Function.Embedding.sumMap (.refl _) (joinEmbedding arity label label' Γ I B)

private def insertedEmbedding : PlugEndpoint arity label label' Γ I ↪
    Ambient arity label label' Γ I B :=
  (Function.Embedding.sumMap (.refl _) (closeEmbedding arity label' I B)).trans
    (((Equiv.sumAssoc _ _ _).symm.trans
      (Equiv.sumCongr (Equiv.sumComm _ _) (Equiv.refl _))).trans
        (Equiv.sumAssoc _ _ _)).toEmbedding

private def finalEmbedding : Endpoint arity (Sum.elim label label') Γ ↪
    Ambient arity label label' Γ I B :=
  (closeEmbedding arity (Sum.elim label label') Γ B).trans joinedEmbedding

private def start (n : PortNet arity label (Γ ⊕ I)) (m : PortNet arity label' (I ⊕ B))
    (w : Wiring B) : Wiring (Ambient arity label label' Γ I B) × ℕ :=
  (w.sum (n.wiring.sum m.wiring), n.loops + m.loops)

private theorem joinFirst_spec (n : PortNet arity label (Γ ⊕ I))
    (m : PortNet arity label' (I ⊕ B)) (w : Wiring B) :
    let g := Wiring.glue closedPorts (FinEnum.toList B)
      (Wiring.glue sharedPorts (FinEnum.toList I) (start n m w))
    Wiring.Respects finalEmbedding
      ((n.join m (FinEnum.toList I) FinEnum.nodup_toList FinEnum.mem_toList).close w).wiring g.1 ∧
        ((n.join m (FinEnum.toList I) FinEnum.nodup_toList FinEnum.mem_toList).close w).loops =
          g.2 := by
  dsimp only
  let j := n.join m (FinEnum.toList I) FinEnum.nodup_toList FinEnum.mem_toList
  let s := Wiring.glue sharedPorts (FinEnum.toList I) (start n m w)
  have hi := n.join_in m (FinEnum.toList I) FinEnum.nodup_toList FinEnum.mem_toList
    Function.Embedding.inr (start n m w) (Wiring.respects_inr w _) 0 (Nat.add_zero _)
  have he : Wiring.Respects joinedEmbedding (w.sum j.wiring) s.1 := by
    rintro (p | p)
    · apply Wiring.glue_keeps
      · intro i b h; cases h
      · intro i b h; cases h
      · rfl
    · exact hi.1 p
  have h := j.close_in w joinedEmbedding s he 0 hi.2
  have hp : (closePorts arity (Sum.elim label label') Γ B).trans (joinedEmbedding (I := I)) =
      closedPorts := by
    ext p
    rcases p with ⟨p, b⟩
    cases b <;> rfl
  rw [hp] at h
  exact ⟨h.1, (Nat.add_zero _).symm.trans h.2⟩

omit [DecidableEq B] in
private theorem closeFirst_spec (n : PortNet arity label (Γ ⊕ I))
    (m : PortNet arity label' (I ⊕ B)) (w : Wiring B) :
    let g := Wiring.glue sharedPorts (FinEnum.toList I)
      (Wiring.glue closedPorts (FinEnum.toList B) (start n m w))
    Wiring.Respects finalEmbedding
      (n.plug (m.close w) (FinEnum.toList I) FinEnum.nodup_toList FinEnum.mem_toList).wiring g.1 ∧
        (n.plug (m.close w) (FinEnum.toList I) FinEnum.nodup_toList FinEnum.mem_toList).loops =
          g.2 := by
  dsimp only
  let s := Wiring.glue closedPorts (FinEnum.toList B) (start n m w)
  have he : Wiring.Respects rightEmbedding (w.sum m.wiring) (start n m w).1 := by
    rintro (p | p) <;> rfl
  have hi := m.close_in w rightEmbedding (start n m w) he n.loops (Nat.add_comm _ _)
  have hn : Wiring.Respects insertedEmbedding (n.wiring.sum (m.close w).wiring) s.1 := by
    rintro (p | p)
    · apply Wiring.glue_keeps
      · intro i b h; cases b <;> cases h
      · intro i b h; cases b <;> cases h
      · rfl
    · have hc (q : Endpoint arity label' I) :
          insertedEmbedding (label := label) (Γ := Γ) (.inr q) =
            rightEmbedding (closeEmbedding arity label' I B q) := by
        cases q <;> rfl
      change s.1.partner (insertedEmbedding (.inr p)) =
        insertedEmbedding (.inr ((m.close w).wiring.partner p))
      rw [hc, hc]
      exact hi.1 p
  have h := n.plug_in (m.close w) (FinEnum.toList I) FinEnum.nodup_toList FinEnum.mem_toList
    insertedEmbedding s hn 0 (by
      rw [Nat.add_zero]
      exact (Nat.add_comm _ _).trans hi.2)
  have hp : (plugPorts (I := I) arity label label' Γ).trans (insertedEmbedding (B := B)) =
      sharedPorts := by
    ext p
    rcases p with ⟨p, b⟩
    cases b <;> rfl
  have hf : (plugEmbedding arity label label' Γ I).trans (insertedEmbedding (B := B)) =
      finalEmbedding := by
    ext p
    rcases p with p | ⟨c | c, p⟩ <;> rfl
  rw [hp, hf] at h
  exact ⟨h.1, (Nat.add_zero _).symm.trans h.2⟩

/-- Close the replacement's internal boundary before insertion or after joining its arguments. -/
theorem plug_close (n : PortNet arity label (Γ ⊕ I))
    (m : PortNet arity label' (I ⊕ B)) (w : Wiring B) :
    n.plug (m.close w) (FinEnum.toList I) FinEnum.nodup_toList FinEnum.mem_toList =
      (n.join m (FinEnum.toList I) FinEnum.nodup_toList FinEnum.mem_toList).close w := by
  have hs := closeFirst_spec n m w
  have ht := joinFirst_spec n m w
  have hd (i : I) (b : Bool) (j : B) (c : Bool) :
      sharedPorts (arity := arity) (label := label) (label' := label') (Γ := Γ) (i, b) ≠
        closedPorts (j, c) := by
    cases b <;> cases c <;> intro h <;> cases h
  dsimp only at hs ht
  rw [Wiring.glue_glue sharedPorts closedPorts hd] at ht
  apply PortNet.ext
  · have h := hs.1.map_eq ht.1 (Equiv.refl _) (fun _ ↦ rfl)
    simpa only [Wiring.map_refl] using h
  · exact hs.2.trans ht.2.symm

end Geb.InteractionNet.PortNet

end
