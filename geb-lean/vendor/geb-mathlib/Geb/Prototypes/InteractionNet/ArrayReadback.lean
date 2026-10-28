/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.InteractionNet.ArrayWiring
public import Geb.Prototypes.InteractionNet.WiringEmbedding

set_option doc.verso true in
/-!
# Compacting the live endpoints of a partner array

After a graph contraction, discarded endpoints are isolated from all live endpoints.
A finite injection lists the live endpoints in their new order. An inverse table decodes
each live endpoint's partner, yielding a compact partner array. The closed-image invariant
makes every lookup succeed. The executable table agrees with the direct finite-search
specification and preserves every live wire.

## Main definitions

* {lit}`ArrayWiring.Closed` — partners of live endpoints are live.
* {lit}`ArrayWiring.pullback` — compact a closed set of live endpoints into a new array.

## Main statements

* {lit}`ArrayWiring.pullback_respects` — compaction preserves partners under the live injection.
* {lit}`ArrayWiring.pullback_eq` — compaction reads back any matching represented by that injection.

## Tags

interaction net, runtime, compaction, array, read-back, refinement
-/

set_option doc.verso true

@[expose] public section

namespace Geb.InteractionNet.ArrayWiring

variable {size live : ℕ}

/-- The listed live endpoints are closed under the array's partner operation. -/
def Closed (w : ArrayWiring size) (e : Fin live ↪ Fin size) : Prop :=
  ∀ p, ∃ q, w.links[e p] = e q

/-- Every represented matching has a closed image in its ambient array. -/
theorem closed_of_respects {w : ArrayWiring size} {e : Fin live ↪ Fin size}
    {v : Wiring (Fin live)} (h : Wiring.Respects e v w.read) : w.Closed e :=
  fun p ↦ ⟨v.partner p, h p⟩

/-- Locate a live endpoint's partner in the new compact enumeration. -/
def partner? (w : ArrayWiring size) (e : Fin live ↪ Fin size) (p : Fin live) : Option (Fin live) :=
  let target := w.links[e p]
  (List.finRange live).find? (fun q ↦ decide (target = e q))

/-- A closed live image makes partner decoding succeed. -/
theorem partner?_isSome (w : ArrayWiring size) (e : Fin live ↪ Fin size)
    (h : w.Closed e) (p : Fin live) : (w.partner? e p).isSome := by
  obtain ⟨q, hq⟩ := h p
  exact List.find?_isSome.mpr ⟨q, List.mem_finRange q, by simpa only [decide_eq_true_eq] using hq⟩

/-- Decode the partner of a live endpoint, using the closed-image proof only for totality. -/
def partner (w : ArrayWiring size) (e : Fin live ↪ Fin size) (h : w.Closed e) (p : Fin live) :
    Fin live := (w.partner? e p).get (w.partner?_isSome e h p)

/-- The decoded endpoint is exactly the array's original partner. -/
theorem partner_spec (w : ArrayWiring size) (e : Fin live ↪ Fin size) (h : w.Closed e)
    (p : Fin live) : e (w.partner e h p) = w.links[e p] := by
  have hf := List.find?_some (Option.eq_some_of_isSome (w.partner?_isSome e h p))
  exact (of_decide_eq_true hf).symm

/-- Decode and materialize a matching along a closed endpoint injection. -/
def pullbackCore (w : ArrayWiring size) (e : Fin live ↪ Fin size) (h : w.Closed e) :
    ArrayWiring live :=
  encode
    { partner := w.partner e h
      involutive p := by
        apply e.injective
        exact (w.partner_spec e h (w.partner e h p)).trans
          ((congrArg w.read.partner (w.partner_spec e h p)).trans (w.involutive (e p)))
      fixedPointFree p hp := by
        have he := w.partner_spec e h p
        rw [hp] at he
        exact w.fixedPointFree (e p) he.symm }

/-- Materialize the live-to-ambient indices once before searching for their partners. -/
def endpointTable (e : Fin live ↪ Fin size) : Vector (Fin size) live :=
  ⟨(List.ofFn e).toArray, by simp only [List.size_toArray, List.length_ofFn]⟩

/-- The cached endpoint table retains each injection value. -/
theorem endpointTable_get (e : Fin live ↪ Fin size) (p : Fin live) :
    (endpointTable e)[p] = e p := by
  change (List.ofFn e).toArray[p.val]'(by
    simpa only [List.size_toArray, List.length_ofFn] using p.isLt) = e p
  simp only [List.getElem_toArray, List.getElem_ofFn]

/-- Read an injection from an already materialized table. -/
def tableEmbedding (table : Vector (Fin size) live) (e : Fin live ↪ Fin size)
    (h : ∀ p : Fin live, table[p] = e p) : Fin live ↪ Fin size where
  toFun p := table[p]
  inj' p q hpq := e.injective ((h p).symm.trans (hpq.trans (h q)))

/-- Materialized injection lookup is extensionally the original injection. -/
theorem tableEmbedding_eq (table : Vector (Fin size) live) (e : Fin live ↪ Fin size)
    (h : ∀ p : Fin live, table[p] = e p) : tableEmbedding table e h = e :=
  Function.Embedding.ext h

/-- Write the compact index at the ambient position of each listed live endpoint. -/
def inverseEntries (e : Fin live ↪ Fin size) (ps : List (Fin live))
    (table : Vector (Option (Fin live)) size) : Vector (Option (Fin live)) size :=
  ps.foldl (fun table p ↦ table.set (e p) (some p)) table

/-- Filling inverse entries records every listed endpoint and retains all unlisted entries. -/
theorem inverseEntries_get (e : Fin live ↪ Fin size) (ps : List (Fin live))
    (table : Vector (Option (Fin live)) size) (p : Fin live) :
    (inverseEntries e ps table)[e p] = if p ∈ ps then some p else table[e p] := by
  revert table
  refine List.rec (fun _ ↦ rfl) (fun q qs ih table ↦ ?_) ps
  change (inverseEntries e qs (table.set (e q) (some q)))[e p] = _
  rw [ih]
  simp only [Fin.getElem_fin, Vector.getElem_set, Fin.val_inj, e.injective.eq_iff,
    List.mem_cons]
  by_cases hpq : p = q
  · subst q
    simp
  · simp only [hpq, Ne.symm hpq, false_or, ↓reduceIte]

/-- Build an ambient-to-live index table in the explicit live enumeration. -/
def inverseTable (e : Fin live ↪ Fin size) : Vector (Option (Fin live)) size :=
  inverseEntries e (List.finRange live) (Vector.replicate size none)

/-- The inverse table decodes every endpoint in the live injection's image. -/
theorem inverseTable_get (e : Fin live ↪ Fin size) (p : Fin live) :
    (inverseTable e)[e p] = some p := by
  simp only [inverseTable, inverseEntries_get, List.mem_finRange, ↓reduceIte]

/-- Decode a partner using a precomputed inverse table. -/
def tablePartner (w : ArrayWiring size) (e : Fin live ↪ Fin size) (h : w.Closed e)
    (table : Vector (Option (Fin live)) size) (ht : ∀ p, table[e p] = some p)
    (p : Fin live) : Fin live :=
  (table[w.links[e p]]).get (by
    obtain ⟨q, hq⟩ := h p
    have he := (congrArg (fun j : Fin size ↦ table[j]) hq).trans (ht q)
    rw [he]
    rfl)

/-- Inverse-table lookup agrees with the direct finite-search specification. -/
theorem tablePartner_eq (w : ArrayWiring size) (e : Fin live ↪ Fin size) (h : w.Closed e)
    (table : Vector (Option (Fin live)) size) (ht : ∀ p, table[e p] = some p)
    (p : Fin live) : tablePartner w e h table ht p = w.partner e h p := by
  unfold tablePartner
  apply Option.get_of_eq_some
  exact (congrArg (fun j : Fin size ↦ table[j]) (w.partner_spec e h p).symm).trans (ht _)

/-- Materialize the compact matching with constant-time inverse-table partner lookups. -/
def pullbackTable (w : ArrayWiring size) (e : Fin live ↪ Fin size) (h : w.Closed e)
    (table : Vector (Option (Fin live)) size) (ht : ∀ p, table[e p] = some p) :
    ArrayWiring live :=
  encode
    { partner := tablePartner w e h table ht
      involutive p := by
        simp only [tablePartner_eq]
        simpa only [pullbackCore, read_encode] using (w.pullbackCore e h).read.involutive p
      fixedPointFree p := by
        simp only [tablePartner_eq]
        simpa only [pullbackCore, read_encode] using
          (w.pullbackCore e h).read.fixedPointFree p }

/-- Using an inverse table leaves the complete compact array unchanged. -/
theorem pullbackTable_eq (w : ArrayWiring size) (e : Fin live ↪ Fin size) (h : w.Closed e)
    (table : Vector (Option (Fin live)) size) (ht : ∀ p, table[e p] = some p) :
    pullbackTable w e h table ht = w.pullbackCore e h := by
  unfold pullbackTable pullbackCore
  apply congrArg encode
  apply Wiring.ext
  funext p
  exact tablePartner_eq w e h table ht p

/-- Compact a closed live set using cached forward indices and an inverse lookup table. -/
def pullback (w : ArrayWiring size) (e : Fin live ↪ Fin size) (h : w.Closed e) :
    ArrayWiring live :=
  let indices := tableEmbedding (endpointTable e) e (endpointTable_get e)
  pullbackTable w indices (by dsimp only [indices]; rw [tableEmbedding_eq]; exact h)
    (inverseTable indices) (inverseTable_get indices)

/-- Caching the endpoint injection does not change the decoded compact matching. -/
theorem pullback_eq_core (w : ArrayWiring size) (e : Fin live ↪ Fin size) (h : w.Closed e) :
    w.pullback e h = w.pullbackCore e h := by
  simp only [pullback, pullbackTable_eq, tableEmbedding_eq]

/-- Compaction preserves every live wire through its original endpoint injection. -/
theorem pullback_respects (w : ArrayWiring size) (e : Fin live ↪ Fin size) (h : w.Closed e) :
    Wiring.Respects e (w.pullback e h).read w.read := by
  intro p
  simp only [pullback_eq_core, pullbackCore, read_encode]
  exact (w.partner_spec e h p).symm

/-- A compacted array reads back the matching represented by its live endpoint injection. -/
theorem pullback_eq {w : ArrayWiring size} {e : Fin live ↪ Fin size} {v : Wiring (Fin live)}
    (h : Wiring.Respects e v w.read) : (w.pullback e (closed_of_respects h)).read = v := by
  apply Wiring.ext
  funext p
  apply e.injective
  exact ((w.pullback_respects e (closed_of_respects h)) p).symm.trans (h p)

end Geb.InteractionNet.ArrayWiring

end
