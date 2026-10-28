/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.InteractionNet.RedexDiamond
public import Geb.Prototypes.InteractionNet.Schedule

set_option doc.verso true in
/-!
# Confluence of finite graph schedules

Finite nets are identified by boundary-preserving cell isomorphisms. A graph step may
select any redex permitted by the rule table. Cell renaming transports such a selection,
and the active-pair diamond therefore gives a strict diamond on isomorphism classes.
Finite schedules are confluent. If one schedule reaches a normal form, every reduction
sequence terminates and every reached normal form is that same isomorphism class.

These statements concern the graph reduction relation. Transferring a compiler's
normalization theorem additionally requires a simulation into this relation.

## Main definitions

* {lit}`FiniteNet.pack` — assign finite ordinal indices to an explicitly enumerable net.
* {lit}`FiniteNet.Step` — contract any selected redex, permitting result cell renaming.
* {lit}`Graph` — finite nets modulo boundary-preserving cell renaming.
* {lit}`Graph.Step` — graph reduction on those equivalence classes.

## Main statements

* {lit}`Graph.diamond` — the strict one-step diamond for graph reduction.
* {lit}`Graph.confluent` — arbitrary finite schedules can be joined.
* {lit}`Graph.terminates_of_normalizes` — one normalizing schedule implies termination of all.

## References

* \[DeFalco2010\], Definition 5.2 and Corollary 5.4.

## Tags

interaction net, graph, schedule, confluence, termination, normal form
-/

set_option doc.verso true

@[expose] public section

namespace Geb.InteractionNet

open scoped FinEnum

universe u v

variable {α : Type u} {arity : α → ℕ} {boundary : ℕ}

namespace FiniteNet

/-- Assign finite ordinal cell indices while preserving the ordered external boundary. -/
def pack {C : Type v} [FinEnum C] {label : C → α} (n : PortNet arity label (Fin boundary)) :
    FiniteNet arity boundary :=
  ⟨FinEnum.card C, fun i ↦ label (FinEnum.equiv.symm i), n.indexed⟩

/-- The graph component of a finite net. -/
abbrev net (n : FiniteNet arity boundary) : PortNet arity n.2.1 (Fin boundary) := n.2.2

/-- Two finite presentations represent the same graph when their cells can be renamed. -/
def Isomorphic (n m : FiniteNet arity boundary) : Prop := Nonempty (n.net.Iso m.net)

/-- Boundary-preserving cell renaming is an equivalence relation on finite presentations. -/
instance isoSetoid : Setoid (FiniteNet arity boundary) where
  r := Isomorphic
  iseqv := ⟨fun n ↦ ⟨PortNet.Iso.refl n.net⟩,
    fun ⟨i⟩ ↦ ⟨i.symm⟩, fun ⟨i⟩ ⟨j⟩ ↦ ⟨i.trans j⟩⟩

/-- Contract any selected redex, allowing any isomorphic finite presentation of the result. -/
def Step (s : PortSystem arity) (n m : FiniteNet arity boundary) : Prop :=
  ∃ r : s.Redex n.net, Nonempty (r.result.Iso m.net)

/-- Renaming the input and output preserves a selected graph step. -/
theorem Step.transport {s : PortSystem arity} {n m n' m' : FiniteNet arity boundary}
    (h : Step s n m) (i : n.net.Iso n'.net) (j : m.net.Iso m'.net) : Step s n' m' := by
  obtain ⟨r, ⟨hr⟩⟩ := h
  exact ⟨r.map i, ⟨(r.mapIso i).symm.trans (hr.trans j)⟩⟩

/-- A fork in finite presentations closes by cell renaming or by one step on each branch. -/
theorem Step.diamond {s : PortSystem arity} {n m k : FiniteNet arity boundary}
    (h : Step s n m) (h' : Step s n k) :
    Isomorphic m k ∨ ∃ p, Step s m p ∧ Step s k p := by
  obtain ⟨r, ⟨i⟩⟩ := h
  obtain ⟨q, ⟨j⟩⟩ := h'
  rcases r.diamond q with he | ⟨r', q', he⟩
  · obtain ⟨he⟩ := he
    exact Or.inl ⟨i.symm.trans (he.trans j)⟩
  · obtain ⟨he⟩ := he
    let := r.resultEnum
    let := r'.resultEnum
    let p := pack r'.result
    have hp : r'.result.Iso p.net := PortNet.indexedIso r'.result
    exact Or.inr ⟨p,
      ⟨r'.map i, ⟨(r'.mapIso i).symm.trans hp⟩⟩,
      ⟨q'.map j, ⟨(q'.mapIso j).symm.trans (he.symm.trans hp)⟩⟩⟩

end FiniteNet

/-- Finite graphs with ordered external boundary, modulo internal cell renaming. -/
abbrev Graph (arity : α → ℕ) (boundary : ℕ) :=
  Quotient (FiniteNet.isoSetoid (arity := arity) (boundary := boundary))

namespace Graph

/-- Forget a finite net's particular allocation of cell indices. -/
def ofNet (n : FiniteNet arity boundary) : Graph arity boundary := Quotient.mk _ n

/-- Select any graph contraction on representatives of the two isomorphism classes. -/
def Step (s : PortSystem arity) (n m : Graph arity boundary) : Prop :=
  ∃ a b : FiniteNet arity boundary, ofNet a = n ∧ ofNet b = m ∧ FiniteNet.Step s a b

/-- A step on concrete finite presentations induces a step of their graph classes. -/
theorem step_of_net {s : PortSystem arity} {n m : FiniteNet arity boundary}
    (h : FiniteNet.Step s n m) : Step s (ofNet n) (ofNet m) := ⟨n, m, rfl, rfl, h⟩

/-- Every fork of graph contractions closes in one step, unless the two results already agree. -/
theorem diamond (s : PortSystem arity) :
    Schedule.StrongDiamond (Step (boundary := boundary) s) := by
  intro n m k h h'
  obtain ⟨a, b, ha, hb, h⟩ := h
  obtain ⟨a', c, ha', hc, h'⟩ := h'
  have he : ofNet a = ofNet a' := ha.trans ha'.symm
  obtain ⟨i⟩ := Quotient.exact he
  have ht := h'.transport i.symm (PortNet.Iso.refl c.net)
  rcases h.diamond ht with hj | ⟨p, hp, hp'⟩
  · have he : ofNet b = ofNet c := Quotient.sound hj
    exact Or.inl (hb.symm.trans (he.trans hc))
  · exact Or.inr ⟨ofNet p, ⟨b, p, hb, rfl, hp⟩, ⟨c, p, hc, rfl, hp'⟩⟩

/-- Arbitrary finite graph schedules from the same graph can be joined. -/
theorem confluent {s : PortSystem arity} {n a b : Graph arity boundary}
    (ha : Relation.ReflTransGen (Step s) n a) (hb : Relation.ReflTransGen (Step s) n b) :
    Relation.Join (Relation.ReflTransGen (Step s)) a b :=
  Schedule.confluent (diamond s) hb a ha

/-- Any two reached graph normal forms are the same boundary-preserving isomorphism class. -/
theorem normal_unique {s : PortSystem arity} {n a b : Graph arity boundary}
    (ha : Relation.ReflTransGen (Step s) n a) (hb : Relation.ReflTransGen (Step s) n b)
    (hna : Schedule.Normal (Step s) a) (hnb : Schedule.Normal (Step s) b) : a = b :=
  Schedule.normal_unique (diamond s) ha hb hna hnb

/-- One normalizing graph schedule makes every sequence of permitted contractions terminate. -/
theorem terminates_of_normalizes {s : PortSystem arity} {n a : Graph arity boundary}
    (h : Relation.ReflTransGen (Step s) n a) (hn : Schedule.Normal (Step s) a) :
    Acc (Function.swap (Step s)) n := Schedule.acc_of_reaches_normal (diamond s) h hn

end Graph

end Geb.InteractionNet

end
