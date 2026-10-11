/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.FreeTopos.Internal.Proofs
public import Geb.Prototypes.FreeTopos.Internal.Prove

set_option doc.verso true in
/-!
# The checker with a step of conversion

A checker of the internal language beside {name}`Geb.FreeTopos.Internal.check`, whose
certificates add to the language's rules a step of conversion: the rewriting of a term to its
normal form under named rules, those of the prover's normalization
({name}`Geb.FreeTopos.Internal.NormRule`). The base checker does not compute that conversion; it
checks each step of it in a derivation. The conversion checker computes it, and admits it by its
translation: a step of conversion at a term in a context under hypotheses is the rewriting
derivation of the prover's normalization of the term under the named rules
({name}`Geb.FreeTopos.Internal.normalize`), and its rewriting is the base checker's rewriting by
that derivation. At every other node the conversion checker takes the base checker's step. Its
soundness is therefore relative to the base checker's, a stronger checker admitted beside a weaker
one by the translation of its certificates (\[Davis2009\]): each step of conversion by the
soundness of the base checker ({name}`Geb.FreeTopos.Internal.check_sound`), and each other node by
the soundness of the base checker's step ({name}`Geb.FreeTopos.Internal.checkStep_sound`). The
normalization is not trusted: the derivation it computes is checked. A step of conversion carries
the bound on the depth of the normalization.

## Main definitions

* {lit}`ConvRule`, {lit}`ConvDeriv` — the rules of the conversion checker's certificates, and
  its certificates.
* {lit}`convCheck`, {lit}`Thm.convChecks` — the conversion checker, and the test that a
  certificate proves a theorem.

## Main statements

* {lit}`convCheck_sound` — the conversion checker is sound.
* {lit}`Thm.valid_of_convChecks` — a theorem a certificate proves with valid earlier entries is
  valid.

## References

* \[Davis2009\], Chapter 1, for checkers admitted by relative soundness.

## Tags

internal language, proof checker, conversion, normalization, relative soundness
-/

set_option doc.verso true

@[expose] public section

namespace Geb.FreeTopos.Internal

open PartialHorn (Tree)
open Sorts

universe v

/-- A rule of the conversion checker's certificates. -/
inductive ConvRule where
  /-- A rule of the language's derivations. -/
  | base (r : Rule)
  /-- The rewriting of a term to its normal form under the rules {lit}`rs`, by the prover's
  normalization within the depth {lit}`fuel`. -/
  | norm (rs : List NormRule) (fuel : ℕ)

/-- A certificate of the conversion checker. -/
abbrev ConvDeriv : Type := RoseTree ConvRule

/-- The rule of the language's derivations a rule of the certificates stands for at a
congruence's choice of contexts: itself for a rule of the language, and one other than the
identity for a step of conversion. -/
def ConvRule.toRule : ConvRule → Rule
  | .base r => r
  | .norm _ _ => .trans

/-- One step of the conversion checker, at a node of a rule from its children's results: the base
checker's step at a rule of the language, each child standing for a derivation of its rule; and
at a step of conversion, the base checker's rewriting by the derivation of the normalization of
the term under the named rules, which proves no formula. -/
def convStep (G : Globals) (E : Array Entry) (n : ℕ) (l : ConvRule)
    (cs : List (ConvDeriv × Checks)) : Checks := match l with
  | .base r => checkStep G E n r (cs.map fun (d, c) ↦ (RoseTree.node d.label.toRule [], c))
  | .norm rs fuel => (fun Γ Φ t ↦ (normalize G E n rs fuel Γ Φ t).bind fun (_, d, _) ↦
      (check G E n d).1 Γ Φ t,
    fun _ _ _ ↦ false)

/-- The conversion checker: the rewriting a certificate performs on a term in a context under
hypotheses, and whether it proves a formula in a context under hypotheses. -/
def convCheck (G : Globals) (E : Array Entry) (n : ℕ) : ConvDeriv → Checks :=
  RoseTree.para (convStep G E n)

/-- The computation rule of the conversion checker. -/
theorem convCheck_node {G : Globals} {E : Array Entry} {n : ℕ} (l : ConvRule)
    (cs : List ConvDeriv) :
    convCheck G E n (RoseTree.node l cs) =
      convStep G E n l (cs.map fun c ↦ (c, convCheck G E n c)) :=
  RoseTree.para_node _ l cs

/-- Whether a certificate proves a theorem: its context's types are types, its hypotheses and
conclusion formulas, and the conversion checker proves the conclusion from the hypotheses. -/
def Thm.convChecks (G : Globals) (E : Array Entry) (a : Thm) (d : ConvDeriv) : Bool :=
  a.wellFormed G && (convCheck G E a.arity d).2 a.ctx a.hyps a.concl

/-- A certificate whose rule is the identity rule's rewrites a term only to itself. -/
theorem convCheck_isRefl {G : Globals} {E : Array Entry} {n : ℕ} {c : ConvDeriv}
    (hc : c.label.toRule.isRefl = true)
    {Γ : List Tree} {Φ : List Term} {t t' : Term} (h : (convCheck G E n c).1 Γ Φ t = some t') :
    t' = t := by
  obtain ⟨l, cs, rfl⟩ : ∃ l cs, c = RoseTree.node l cs :=
    ⟨_, _, (RoseTree.node_label_children c).symm⟩
  rcases l with r | ⟨rs, fuel⟩
  · cases r <;> simp only [RoseTree.label_node, ConvRule.toRule, Rule.isRefl, reduceCtorEq] at hc
    rw [convCheck_node] at h
    rcases cs with _ | ⟨c', cs⟩
    · exact (Option.some_inj.mp h).symm
    · simp [convStep, checkStep] at h
  · simp [RoseTree.label_node, ConvRule.toRule, Rule.isRefl] at hc

section Soundness

variable {defs : List PartialHorn.Defn} {M : PartialHorn.Model.{v} (ext defs).sig}
  (hM : PartialHorn.IsModel (ext defs) M) {G : Globals} (hG : G.WF) {ρ : List M.Val} {n : ℕ}
  (hρ : ρ.map Sigma.fst = List.replicate n obj) (hps : PrimsHom M ρ G n) (hds : DefsHom M ρ G n)
include hM hG hρ hps hds

/-- The conversion checker is sound: every rewriting a certificate performs is sound, and every
formula it proves holds, with sound unfoldings and valid earlier entries, when the model's
definitions are the compilations of the definitions of {name}`G` wherever a certificate is
checked. -/
theorem convCheck_sound (hδ : DefnsOk M G) {E : Array Entry}
    (hE : ∀ (j : ℕ) (e : Entry), E[j]? = some e → e.Valid M G)
    (hcert : ∀ cds, compileDefs G = some cds → G.base = sig.length → cds <+: defs) :
    ∀ d : ConvDeriv, ChecksSound M ρ G n (convCheck G E n d) :=
  RoseTree.ind fun l cs ih ↦ by
    rw [convCheck_node]
    rcases l with r | ⟨rs, fuel⟩
    · refine checkStep_sound hM hG hρ hps hds hδ hE hcert r _ (fun x hx ↦ ?_) fun x hx ↦ ?_
      all_goals
        obtain ⟨⟨d, dc⟩, hd, rfl⟩ := List.mem_map.mp hx
        obtain ⟨c, hc, h⟩ := List.mem_map.mp hd
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
      · exact ih c hc
      · exact fun hr _ _ _ _ h ↦ convCheck_isRefl hr h
    · refine ⟨fun Γ Φ t t' h ↦ ?_, fun _ _ _ h ↦ nomatch h⟩
      obtain ⟨⟨_, d, _⟩, -, h⟩ := Option.bind_eq_some_iff.mp h
      exact (check_sound hM hG hρ hps hds hδ hE hcert d).1 _ _ _ _ h

end Soundness

section Theorems

variable {defs : List PartialHorn.Defn} {M : PartialHorn.Model.{v} (ext defs).sig}
  (hM : PartialHorn.IsModel (ext defs) M) {G : Globals} (hG : G.WF)
  (hps : ∀ (m : ℕ) (ρ : List M.Val), ρ.map Sigma.fst = List.replicate m obj → PrimsHom M ρ G m)
  (hds : ∀ (m : ℕ) (ρ : List M.Val), ρ.map Sigma.fst = List.replicate m obj → DefsHom M ρ G m)
  (hδ : DefnsOk M G)
  (hcert : ∀ cds, compileDefs G = some cds → G.base = sig.length → cds <+: defs)
include hM hG hps hds hδ hcert

/-- A theorem a certificate of the conversion checker proves with valid earlier entries is
valid. -/
theorem Thm.valid_of_convChecks {E : Array Entry}
    (hE : ∀ (j : ℕ) (e : Entry), E[j]? = some e → e.Valid M G) {a : Thm} {d : ConvDeriv}
    (h : a.convChecks G E d = true) : a.Valid M G := by
  simp only [Thm.convChecks, Bool.and_eq_true] at h
  obtain ⟨hwf, hd⟩ := h
  obtain ⟨hctx, hhyps, hconcl⟩ := Thm.wellFormed_iff.mp hwf
  exact ⟨hctx, hhyps, hconcl,
    fun ρ hρ ↦ ⟨hps _ ρ hρ, hds _ ρ hρ,
      (convCheck_sound hM hG hρ (hps _ ρ hρ) (hds _ ρ hρ) hδ hE hcert d).2 _ _ _ hd⟩⟩

end Theorems

end Geb.FreeTopos.Internal

end
