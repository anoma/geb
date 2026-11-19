/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.FreeTopos.Internal.Represent
public import Geb.Prototypes.FreeTopos.Internal.Square

set_option doc.verso true in
/-!
# A representation over constants is one over constants that extend them

Constants extend others when the first's primitive arrows and definitions are the others'
before further ones ({name}`Geb.FreeTopos.Internal.Globals.Le`), and then the definitions the
first compile to are those the others compile to, before further ones. A term over the first
compiles over the others to the same arrow ({name}`Geb.FreeTopos.Internal.compile_mono`), and
the unfolding of the further definitions leaves the arrow, whose operations are the first's
({name}`Geb.FreeTopos.unfoldTerm_append`): so a term's representation over the first
({name}`Geb.FreeTopos.Internal.RepC`) is one over the others, and the arrow of a definition of
the first represents over the others what it represents over the first. The representations of
a translated program's definitions and of the library are stated over the translation's
constants; a program that extends the translation by further definitions reads them so. In the
same way a definition's body, which compiles over the definitions before it, compiles over all
the constants to the same arrow, so the definition's arrow represents what the body represents
there.

## Main definitions

* {lit}`EnvSorted` — an environment whose object and entries are of the definitions' signature.

## Main statements

* {lit}`unfoldTerm_append_defn` — the unfolding of further definitions leaves a definition's
  arrow.
* {lit}`repC_lift`, {lit}`repC_le` — a term's representation over constants, in a sorted
  environment, is one over constants that extend them.
* {lit}`rep_def_full` — a definition's arrow represents what its body represents over all the
  constants.

## Tags

internal language, logical relation, representation, definitional extension
-/

set_option doc.verso true

@[expose] public section

namespace Geb.FreeTopos.Internal

open PartialHorn (Tree)
open Sorts
open scoped FinEnum

variable {ds ext : List PartialHorn.Defn}

/-- The unfolding of a list of well-formed definitions with further ones after them leaves the
body of one of them as their own unfolding does: its operations are those before it. -/
theorem unfoldTerm_append_defn (hwf : PartialHorn.DefnsWF sig ds) {k : ℕ} {d : PartialHorn.Defn}
    (hk : ds[k]? = some d) : unfoldTerm sig (ds ++ ext) d.body = unfoldTerm sig ds d.body := by
  have hs := (defnsWF_getElem ds sig hwf hk).sort
  have hops := PartialHorn.opsBelow_of_sortOf d.body hs
  refine unfoldTerm_append ext ds sig d.body (PartialHorn.opsBelow_mono ?_ d.body hops)
  rw [extendAll_eq, extendAll_eq, List.length_append, List.length_append, List.length_map,
    List.length_map, List.length_take]
  omega

/-- An environment over an object is sorted over constants and the definitions they compile to:
the object is an object of the definitions' signature, and each entry an arrow of it to a
type. -/
def EnvSorted (G : Globals) (ds : List PartialHorn.Defn) (n : ℕ) (X : Tree)
    (e : List (Tree × Tree)) : Prop :=
  PartialHorn.sortOf (FreeTopos.ext ds).sig (List.replicate n obj) X = some obj ∧
    ∀ p ∈ e, PartialHorn.sortOf (FreeTopos.ext ds).sig (List.replicate n obj) p.1 = some arr ∧
      IsTy G n p.2 = true

section Sorted

variable {G : Globals} (hbase : G.base = sig.length) (hc : compileDefs G = some ds) {n : ℕ}
include hbase hc

/-- The standard environment of a context of types is sorted. -/
theorem EnvSorted.std {Γ : List Tree} (hΓ : Γ.all (IsTy G n) = true) :
    EnvSorted G ds n (ctxObj Γ) (stdEnv Γ) :=
  have hdefs := fun k d (hd : G.defs[k]? = some d) ↦
    getElem?_sig_compileDefs (pre := []) (by simpa using hbase) hc hd
  ⟨sortOf_ctxObj hdefs Γ hΓ, sortOf_stdEnv hdefs Γ hΓ⟩

/-- The extension of a sorted environment by a variable of a type is sorted. -/
theorem EnvSorted.extend {X : Tree} {e : List (Tree × Tree)} (h : EnvSorted G ds n X e)
    {a : Tree} (ha : IsTy G n a = true) : EnvSorted G ds n (prod X a) (extEnv X a e) := by
  have hdefs := fun k d (hd : G.defs[k]? = some d) ↦
    getElem?_sig_compileDefs (pre := []) (by simpa using hbase) hc hd
  have hA := sortOf_of_isTy (defs := [] ++ ds) hdefs a ha
  refine ⟨sortOf_prod h.1 hA, fun p hp ↦ ?_⟩
  simp only [extEnv, List.mem_cons, List.mem_map] at hp
  rcases hp with rfl | ⟨q, hq, rfl⟩
  · exact ⟨sortOf_snd h.1 hA, ha⟩
  · exact ⟨sortOf_comp (h.2 q hq).1 (sortOf_fst h.1 hA), (h.2 q hq).2⟩

omit hbase hc in
/-- The unfolding of further definitions leaves the object of a sorted environment. -/
theorem EnvSorted.unfold {X : Tree} {e : List (Tree × Tree)} (h : EnvSorted G ds n X e) :
    unfoldTerm sig (ds ++ ext) X = unfoldTerm sig ds X := by
  have hops := PartialHorn.opsBelow_of_sortOf _ h.1
  rw [PartialHorn.Theory.extendAll_sig] at hops
  exact unfoldTerm_append ext ds sig X hops

/-- A term's representation in a sorted environment, over constants the check accepts, is one
over constants that extend them and compile to their definitions before further ones. -/
theorem repC_lift {G' : Globals} (hle : G.Le G') (hok : G.ok (ExtEnv.ofDefs ds) = true)
    {X : Tree} {e : List (Tree × Tree)} (hs : EnvSorted G ds n X e)
    {ρ : List relTopos.model.Val} {t : Term} {a : Tree} {S T A B : Type} {R : S → A → Prop}
    {R' : T → B → Prop} {F : S → T} (h : RepC G n ds ρ t X e a R R' F) :
    RepC G' n (ds ++ ext) ρ t X e a R R' F := by
  obtain ⟨f, hf, hR⟩ := h
  have hdefs := fun k d (hd : G.defs[k]? = some d) ↦
    getElem?_sig_compileDefs (pre := []) (by simpa using hbase) hc hd
  have hsf := (compile_sortOf (defs := [] ++ ds) (Globals.wf_of_ok hok)
    (fun k p hp ↦ sortOf_prims_of_ok (by simpa using hok) hp) hdefs _ _ _ _ hf hs.1 hs.2).1
  have hops := PartialHorn.opsBelow_of_sortOf _ hsf
  rw [List.nil_append, PartialHorn.Theory.extendAll_sig] at hops
  exact ⟨f, compile_mono hle _ _ _ _ hf, by rw [unfoldTerm_append ext ds sig f hops]; exact hR⟩

end Sorted

/-- A term's representation in the standard environment of a context of types, over constants
the check accepts, is one over constants that extend them and compile to their definitions
before further ones. -/
theorem repC_le {G G' : Globals} (hle : G.Le G') (hbase : G.base = sig.length)
    (hok : G.ok (ExtEnv.ofDefs ds) = true) (hc : compileDefs G = some ds) {n : ℕ}
    {Γ : List Tree} (hΓ : Γ.all (IsTy G n) = true) {ρ : List relTopos.model.Val} {t : Term}
    {a : Tree} {S T A B : Type} {R : S → A → Prop} {R' : T → B → Prop} {F : S → T}
    (h : RepC G n ds ρ t (ctxObj Γ) (stdEnv Γ) a R R' F) :
    RepC G' n (ds ++ ext) ρ t (ctxObj Γ) (stdEnv Γ) a R R' F :=
  repC_lift hbase hc hle hok (EnvSorted.std hbase hc hΓ) h

/-- A definition's arrow represents what its body represents over all the constants: the body
compiles over the definitions before it, hence over all of them, to that arrow. -/
theorem rep_def_full {G : Globals} {ds : List PartialHorn.Defn} (hF : compileDefs G = some ds)
    {k : ℕ} {d : Defn} (hk : G.defs[k]? = some (.language d)) {τ' : List Type}
    {S T A B : Type} {Rp : S → A → Prop} {Rt : T → B → Prop} {Fk Fk' : S → T}
    (hb : RepC G d.arity ds (objs τ') d.body (ctxObj d.params) (stdEnv d.params) d.type Rp Rt
      Fk) (hFk : ∀ s, Fk s = Fk' s) {fk : Tree}
    (hdk : ds[k]? = some ⟨List.replicate d.arity obj, arr, fk⟩) :
    Represents (objs τ') (unfoldTerm sig ds fk) Rp Rt Fk' := by
  obtain ⟨f, hf, hR⟩ := hb
  obtain ⟨r, hr, hc⟩ := mapM_getElem? _ hF
    (show G.defs.zipIdx[k]? = some (Definition.language d, k) by simp [List.getElem?_zipIdx, hk])
  obtain ⟨⟨f₀, c⟩, hf₀, -⟩ := Option.bind_eq_some_iff.mp hc
  have hle : ({ G with defs := G.defs.take k } : Globals).Le G :=
    ⟨List.prefix_refl _, rfl, List.take_prefix _ _⟩
  obtain ⟨rfl, rfl⟩ :=
    Prod.mk.inj (Option.some.inj ((compile_mono hle _ _ _ _ hf₀).symm.trans hf))
  have hc' : r = ⟨List.replicate d.arity obj, arr, f₀⟩ := by
    simp only [Definition.compile, Defn.compile, hf₀, Option.bind_eq_bind, Option.bind_some,
      Option.pure_def] at hc
    split_ifs at hc
    exact (Option.some_inj.mp hc).symm
  obtain rfl : f₀ = fk := by
    have e := (hr.trans (congrArg some hc')).symm.trans hdk
    simp only [Option.some.injEq, PartialHorn.Defn.mk.injEq, true_and] at e
    exact e
  exact hR.congr hFk

end Geb.FreeTopos.Internal

end
