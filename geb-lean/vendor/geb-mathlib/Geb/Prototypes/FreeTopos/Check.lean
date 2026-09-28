/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.FreeTopos.Infer

set_option doc.verso true in
/-!
# The checker of the theory of an elementary topos

The checker of shared developments of the theory {name}`Geb.FreeTopos.theory` extended by
definitions, whose oracle infers the typing of the store's terms: a certificate may cite the
definedness of a term the inference types, and the equation of two objects of one canonical
form, without proving them. The typings of the store's nodes are computed for each scope, a
context and hypotheses, each once and only when a certificate consults it, each node's from its
children's by one step of the term inference ({lit}`annotate`), so that each is the inference
of the node's term ({lit}`annotate_getElem?`). The oracle is sound by the soundness of the inference
({lit}`toposOracle_sound`), and every sequent of a development the checker accepts is valid in
every model of the extended theory ({lit}`checkTopos_sound`).

## Main definitions

* {lit}`annotate` — the terms and typings of a store's nodes in a scope.
* {lit}`toposOracle` — the oracle of the inferred typings.
* {lit}`checkTopos` — the checker of shared developments of the extended theory.

## Main statements

* {lit}`annotate_getElem?` — the pass computes the inference of each node's term.
* {lit}`toposOracle_sound` — the oracle is sound.
* {lit}`checkTopos_sound` — every sequent of a development that checks is valid.

## Tags

elementary topos, proof checker, type inference, sharing, soundness
-/

set_option doc.verso true

@[expose] public section

namespace Geb.FreeTopos

open PartialHorn Sorts
open scoped FinEnum

universe v

/-- The fuel of the inference: the depth of the axioms' sides it instantiates. -/
def inferFuel : ℕ := 8

/-- The terms and typings of a store's nodes in a context under hypotheses, each computed when
first demanded: each node's term from its children's, and its typing by one step of the term
inference. -/
def annotate (E : ExtEnv) (Γ : List ℕ) (H : List Eqn) (st : Store) :
    Array (Thunk (Tree × Option Ann)) :=
  st.nodes.foldl (fun acc x ↦ acc.push (Thunk.mk fun _ ↦
    let cs := x.2.map fun c ↦ (acc[c]?.map Thunk.get).getD (RoseTree.node 0 [], none)
    (RoseTree.node x.1 (cs.map Prod.fst),
      treeStep E Γ H (infers E Γ H inferFuel).1 (infers E Γ H inferFuel).2 x.1 cs))) #[]

/-- The pass computes, for each node, its term and the inference of its term. -/
theorem annotate_spec (E : ExtEnv) (Γ : List ℕ) (H : List Eqn) {st : Store}
    (hst : st.WF) :
    (annotate E Γ H st).size = st.nodes.size ∧ ∀ i < st.nodes.size,
      (annotate E Γ H st)[i]?.map Thunk.get =
        some (st.denote i, (infers E Γ H (inferFuel + 1)).2 (st.denote i)) :=
  Array.foldl_induction (as := st.nodes)
    (motive := fun k (acc : Array (Thunk (Tree × Option Ann))) ↦ acc.size = k ∧ ∀ j < k,
      acc[j]?.map Thunk.get =
        some (st.denote j, (infers E Γ H (inferFuel + 1)).2 (st.denote j)))
    (init := #[]) ⟨rfl, fun j hj ↦ _root_.absurd hj (Nat.not_lt_zero _)⟩
    (fun k b hb ↦ ⟨by rw [Array.size_push, hb.1], fun j hj ↦ by
      rcases Nat.lt_or_ge j k with hjk | hjk
      · have hjb : j < b.size := hb.1 ▸ hjk
        rw [Array.getElem?_push_lt hjb, ← Array.getElem?_eq_getElem hjb]
        exact hb.2 j hjk
      · have hjk : j = k := Nat.le_antisymm (Nat.le_of_lt_succ hj) hjk
        subst hjk
        rcases hn : st.nodes[k] with ⟨l, cs⟩
        have hx : st.nodes[(k : ℕ)]? = some (l, cs) := by
          rw [Array.getElem?_eq_getElem k.2]
          exact congrArg some hn
        have hc : ∀ c ∈ cs, (b[c]?.map Thunk.get).getD (RoseTree.node 0 [], none) =
            (st.denote c, (infers E Γ H (inferFuel + 1)).2 (st.denote c)) := fun c hc' ↦ by
          rw [hb.2 c (hst k _ hx c hc'), Option.getD_some]
        have hs : (k : ℕ) = b.size := hb.1.symm
        rw [hs, Array.getElem?_push_size, ← hs, Store.denote_eq hst hx, Option.map_some]
        simp only [List.map_congr_left hc, List.map_map, Function.comp_def]
        change _ = some (_, RoseTree.para (treeStep E Γ H (infers E Γ H inferFuel).1
          (infers E Γ H inferFuel).2) (RoseTree.node l (cs.map st.denote)))
        rw [RoseTree.para_node, List.map_map]
        rfl⟩)

/-- The typing of a node the pass computes is the inference of its term. -/
theorem annotate_getElem? {E : ExtEnv} {Γ : List ℕ} {H : List Eqn} {st : Store}
    (hst : st.WF) {i : ℕ} {a : Ann}
    (h : (((annotate E Γ H st)[i]?).map Thunk.get).bind Prod.snd = some a) :
    (infers E Γ H (inferFuel + 1)).2 (st.denote i) = some a := by
  obtain ⟨hsz, hsp⟩ := annotate_spec E Γ H hst
  by_cases hi : i < st.nodes.size
  · rw [hsp i hi, Option.bind_some] at h
    exact h
  · rw [Array.getElem?_eq_none (by omega), Option.map_none, Option.bind_none] at h
    exact _root_.absurd h (by simp)

/-- The oracle of the typings the inference computes for a store's nodes in a context under
hypotheses: a typed node is defined, and two objects of one canonical form are equal. Each
typing is computed when the oracle first consults it. -/
def toposOracle (E : ExtEnv) (st : Store) (Γ : List ℕ) (H : List Eqn) : Oracle :=
  let anns : Thunk (Array (Thunk (Tree × Option Ann))) := Thunk.mk fun _ ↦ annotate E Γ H st
  ⟨fun i ↦ ((anns.get[i]?.map Thunk.get).bind Prod.snd).isSome,
    fun a b ↦ match (anns.get[a]?.map Thunk.get).bind Prod.snd,
      (anns.get[b]?.map Thunk.get).bind Prod.snd with
      | some x, some y => x.sort == obj && y.sort == obj && x.lo == y.lo
      | _, _ => false⟩

/-- The oracle of the inferred typings is sound. -/
theorem toposOracle_sound {E : ExtEnv} (hE : E.WF) {M : Model.{v} (ext E.defs).sig}
    (hM : IsModel (ext E.defs) M) {st : Store} (hst : st.WF) (Γ : List ℕ) (H : List Eqn) :
    (toposOracle E st Γ H).Sound st M Γ H := by
  intro ρ hρ hH
  have hinf := (infers_sound (hE.sound_self hM) hρ hH (inferFuel + 1)).2
  refine ⟨fun i hi ↦ ?_, fun a b hab ↦ ?_⟩
  · obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hi
    obtain ⟨w, hw, -⟩ := hinf _ x (annotate_getElem? hst hx)
    exact ⟨w, hw⟩
  · simp only [toposOracle] at hab
    split at hab
    · rename_i x y hx hy
      simp only [Bool.and_eq_true, beq_iff_eq] at hab
      obtain ⟨⟨hxo, hyo⟩, hlo⟩ := hab
      obtain ⟨w, hw, -, hwl, -⟩ := hinf _ x (annotate_getElem? hst hx)
      obtain ⟨w', hw', -, hwl', -⟩ := hinf _ y (annotate_getElem? hst hy)
      have he : w = w' := Part.some_inj.mp ((hwl hxo).symm.trans (hlo ▸ hwl' hyo))
      exact ⟨w, hw, he ▸ hw'⟩
    · exact _root_.absurd hab (by simp)

/-- The oracle of a scope, from a table of the oracles of scopes, computed where the table has
none. -/
def oracleFrom (E : ExtEnv) (st : Store)
    (table : List ((List ℕ × List Eqn) × Oracle)) (a : Seq) : Oracle :=
  ((table.find? (·.1 == (a.ctx, a.hyps))).map Prod.snd).getD (toposOracle E st a.ctx a.hyps)

/-- Whether a shared development of the theory extended by definitions checks, with the oracle
of the inferred typings, computed once for each scope of its sequents. -/
def checkTopos (defs : List Defn) (d : SDevelopment) : Bool :=
  let E := ExtEnv.ofDefs defs
  let keys := (d.entries.map fun e ↦ (e.seq.ctx, e.seq.hyps)).eraseDups
  let table := keys.map fun k ↦ (k, toposOracle E d.store k.1 k.2)
  checkSharedWith (ext defs) d (oracleFrom E d.store table)

/-- Every sequent of a shared development of the theory extended by definitions that checks is
valid in every model of the extended theory. -/
theorem checkTopos_sound {defs : List Defn} {M : Model.{v} (ext defs).sig}
    (hM : IsModel (ext defs) M) {d : SDevelopment} (h : checkTopos defs d = true) :
    ∀ e ∈ d.entries, e.seq.Valid M := by
  have hwf : d.store.wf = true := by
    simp only [checkTopos, checkSharedWith, Bool.and_eq_true] at h
    exact h.1
  have hst := Store.wf_of_wf d.store hwf
  refine checkSharedWith_sound hM (fun a ↦ ?_) h
  unfold oracleFrom
  rcases hf : List.find? _ _ with _ | p
  · exact toposOracle_sound (ExtEnv.wf_ofDefs defs) hM hst a.ctx a.hyps
  · have hp := List.find?_some hf
    rw [beq_iff_eq] at hp
    obtain ⟨k, -, rfl⟩ := List.mem_map.mp (List.mem_of_find?_eq_some hf)
    simp only at hp
    rw [Option.map_some, Option.getD_some]
    rw [hp]
    exact toposOracle_sound (ExtEnv.wf_ofDefs defs) hM hst a.ctx a.hyps

end Geb.FreeTopos

end
