/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.FreeTopos.Internal.Development
public import Geb.Prototypes.FreeTopos.Internal.Logic
public import Geb.Prototypes.FreeTopos.Internal.Proofs
public import Geb.Prototypes.PartialHorn.Completeness

set_option doc.verso true in
/-!
# The completeness of the internal language

A theorem of the language whose hypotheses and conclusion are formulas, valid in every model of
the theory extended by the compilations of the language's definitions, is proved by a derivation
of one rule: the citation of a certificate of the sequent it compiles to
({name}`Geb.FreeTopos.Internal.Thm.seq`). The sequent is valid in every such model
({name}`Geb.FreeTopos.Internal.Thm.seq_valid`), the extended theory's axioms are in scope and
equate terms of one sort, and so the partial Horn logic's completeness
({name}`Geb.PartialHorn.derivable_of_valid`) gives the certificate, with any environment of
theorems. The citation is sound in every such model
({name}`Geb.FreeTopos.Internal.certSeq_sound`), so that the language citing certificates proves
exactly the theorems valid in every model.

The round trips of the compilation are provably the identity. A primitive arrow, applied in its
object variables to the variable of its domain, compiles to its arrow after the identity, an
equation of the combinators valid in every model and so derivable ({lit}`roundTrip_prim`). A
term compiles in its context to an arrow; declared as a primitive arrow, that arrow applied to
the tuple of the context's variables ({lit}`varsTerm`) compiles, in every environment, to the
arrow after the environment's tuple, as the term does, so that their equation is valid in every
model and proved by the citation of a certificate ({lit}`roundTrip_term`). The primitive arrow
is applied at the object variables, which, substituted for themselves, leave its domain, the
context's product, its codomain and its arrow in place, since each is in their scope.

## Main definitions

* {lit}`varsTerm` — the tuple of a context's variables.

## Main statements

* {lit}`theory_scoped` — the theory's axioms are in scope.
* {lit}`exists_certSeq_of_valid` — completeness: a theorem valid in every model is proved by the
  citation of a certificate.
* {lit}`compile_varsTerm` — the tuple of a context's variables compiles to the environment's
  tuple.
* {lit}`roundTrip_prim`, {lit}`roundTrip_term` — the round trips of the compilation.

## Tags

internal language, Mitchell–Bénabou language, completeness, proof certificate, round trip
-/

set_option doc.verso true

@[expose] public section

namespace Geb.FreeTopos.Internal

open Geb.PartialHorn (Seq Model IsModel Tree eval)
open Geb.FreeTopos.Sorts
open Geb.FreeTopos.Internal.Logic (nd)

/-- The theory's axioms are in scope. -/
theorem theory_scoped : ∀ a ∈ theory.axioms, a.Scoped = true := by
  have h : axioms.all Seq.Scoped = true := by decide
  exact fun a ha ↦ List.all_eq_true.mp h a ha

/-- The theory extended by well-formed definitions has its axioms in scope, each equating terms
of one sort. -/
theorem ext_axioms_complete {cds : List PartialHorn.Defn} (hwf : PartialHorn.DefnsWF sig cds) :
    ∀ a ∈ (ext cds).axioms, a.Scoped = true ∧ PartialHorn.SidesSorted (ext cds).sig a :=
  fun a ha ↦ ⟨PartialHorn.scoped_extendAll cds theory theory_scoped hwf a ha,
    PartialHorn.sidesSorted_extendAll cds theory theory_sidesSorted hwf a ha⟩

/-- Completeness: a theorem whose hypotheses and conclusion are formulas, valid in every model of
the theory extended by the compilations of the definitions of {lit}`G`, is proved by the citation
of a certificate of the sequent it compiles to, with any environment. -/
theorem exists_certSeq_of_valid {G : Globals} (hG : G.WF) {cds : List PartialHorn.Defn}
    (hc : compileDefs G = some cds) (hb : G.base = sig.length)
    (hwf : PartialHorn.DefnsWF sig cds) {E : Array Entry} {a : Thm}
    (hΦ : ∀ ψ ∈ a.hyps, typeIn G a.arity a.ctx ψ = some omega)
    (hφ : typeIn G a.arity a.ctx a.concl = some omega)
    (hv : ∀ M : Model.{0} (ext cds).sig, IsModel (ext cds) M → a.Valid M G) :
    ∃ c, (check G E a.arity (nd (.certSeq c))).2 a.ctx a.hyps a.concl = true := by
  obtain ⟨c, hc'⟩ := PartialHorn.derivable_of_valid (E := E.map (Entry.seq G))
    (ext_axioms_complete hwf) (H := []) (fun _ h ↦ by simp at h)
    fun M hM ↦ Thm.seq_valid hM hG (hv M hM)
  refine ⟨c, ?_⟩
  rw [nd, check_node]
  simp only [checkStep, List.map_nil, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨hΦ, hφ⟩, ?_⟩
  simp only [certifies, hc, Option.any_some, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨hb, hc'⟩

section RoundTrips

/-- The tuple of the variables of a context, the first of index {lit}`i`: the element of the
terminal type for the empty context, and the variable itself for a context of one. -/
def varsTerm (Γ : List Tree) : ℕ → Term :=
  Γ.rec (fun _ ↦ Term.star) fun _ Γ ih i ↦ match Γ with
    | [] => Term.var i
    | _ :: _ => Term.pair (ih (i + 1)) (Term.var i)

/-- The tuple of a context's variables, after the variables of another environment, compiles to
the tuple of the environment's arrows at them. -/
theorem compile_varsTerm {G : Globals} {n : ℕ} {X : Tree} :
    ∀ (Γ : List Tree) (e₀ e : List (Tree × Tree)), e.map Prod.snd = Γ →
      compile G n (varsTerm Γ e₀.length) X (e₀ ++ e) =
        some (tuple X (e.map Prod.fst), ctxObj Γ) :=
  List.rec (fun e₀ e he ↦ by
      obtain rfl : e = [] := List.map_eq_nil_iff.mp he
      exact compile_star_iff.mpr ⟨rfl, rfl⟩)
    fun a Γ ih e₀ e he ↦ by
      rcases e with _ | ⟨⟨f, A⟩, e⟩
      · simp at he
      simp only [List.map_cons, List.cons.injEq] at he
      obtain ⟨rfl, he⟩ := he
      have hv : (e₀ ++ (f, A) :: e)[e₀.length]? = some (f, A) := by
        rw [List.getElem?_append_right (le_refl _), Nat.sub_self]
        rfl
      rcases Γ with _ | ⟨b, Γ⟩
      · obtain rfl : e = [] := List.map_eq_nil_iff.mp he
        exact compile_var_iff.mpr ⟨rfl, hv⟩
      · rcases e with _ | ⟨q, e⟩
        · simp at he
        have h := ih (e₀ ++ [(f, A)]) (q :: e) he
        rw [List.length_append, List.length_singleton, List.append_assoc,
          List.singleton_append] at h
        exact compile_pair_iff.mpr ⟨_, _, _, _, _, _, rfl, h, compile_var_iff.mpr ⟨rfl, hv⟩, rfl⟩

/-- The first round trip: a primitive arrow, applied in its object variables to the variable of
its domain, compiles to its arrow after the identity, which is provably its arrow, when it is an
arrow between its types in every model of the theory extended by well-formed definitions. -/
theorem roundTrip_prim {G : Globals} (hG : G.WF) {cds : List PartialHorn.Defn}
    (hwf : PartialHorn.DefnsWF sig cds) {k : ℕ} {p : Prim} (hk : G.prims[k]? = some p)
    (hval : ∀ M : Model.{0} (ext cds).sig, IsModel (ext cds) M → p.Val M)
    (E : Array Seq) :
    compile G p.arity (Term.arr k (objVars p.arity) (Term.var 0)) (ctxObj [p.dom])
        (stdEnv [p.dom]) = some (comp p.arrow (idt p.dom), p.cod) ∧
      PartialHorn.Derivable (ext cds) E (List.replicate p.arity obj) []
        ⟨comp p.arrow (idt p.dom), p.arrow⟩ := by
  have hθl : (objVars p.arity).length = p.arity := by simp [objVars]
  obtain ⟨har, hdt, hct⟩ := hG.prims k p hk
  have hfix : ∀ A : Tree, PartialHorn.Scoped p.arity A = true →
      PartialHorn.subst (objVars p.arity) A = A := fun A hA ↦ subst_vars p.arity A hA
  refine ⟨compile_arr_iff.mpr ⟨_, rfl, p, hk, idt p.dom, ?_, hθl, all_isTy_vars G p.arity, ?_⟩,
    ?_⟩
  · rw [hfix _ (scoped_of_isTy _ hdt)]
    exact compile_var_iff.mpr ⟨rfl, rfl⟩
  · rw [hfix _ har, hfix _ (scoped_of_isTy _ hct)]
  refine PartialHorn.derivable_of_valid (ext_axioms_complete hwf) (fun _ h ↦ by simp at h)
    fun M hM ρ hρ _ ↦ ?_
  have hv := hval M hM ρ hρ
  obtain ⟨w, hw, -⟩ := hv.exists_eval
  exact holds_of_eval_eq (comp_idt hM hv) hw

/-- The second round trip: a term, compiled in its context to an arrow in its object variables
that is declared as a primitive arrow, is provably that primitive arrow at the object variables
applied to the tuple of the context's variables, by the citation of a certificate, when the
constants are arrows between their types, and the definitions valid, in every model of the
theory extended by the definitions' well-formed compilations. -/
theorem roundTrip_term {G : Globals} (hG : G.WF) {cds : List PartialHorn.Defn}
    (hc : compileDefs G = some cds) (hb : G.base = sig.length)
    (hwf : PartialHorn.DefnsWF sig cds)
    (hsorts : ∀ (k : ℕ) (p : Prim), G.prims[k]? = some p →
      PartialHorn.sortOf (ext cds).sig (List.replicate p.arity obj) p.arrow = some arr)
    (hval : ∀ M : Model.{0} (ext cds).sig, IsModel (ext cds) M →
      (∀ (k : ℕ) (p : Prim), G.prims[k]? = some p → p.Val M) ∧ DefsVal M G)
    {n : ℕ} {Γ : List Tree} (hΓ : Γ.all (IsTy G n) = true) {t : Term} {F B : Tree}
    (ht : compile G n t (ctxObj Γ) (stdEnv Γ) = some (F, B)) (E : Array Entry) :
    ∃ c, (check { G with prims := G.prims ++ [⟨n, F, ctxObj Γ, B⟩] } E n
      (nd (.certSeq c))).2 Γ []
        (Term.eq (Term.arr G.prims.length (objVars n) (varsTerm Γ 0)) t) = true := by
  set θ := objVars n
  set p : Prim := ⟨n, F, ctxObj Γ, B⟩
  set G' : Globals := { G with prims := G.prims ++ [p] }
  have hle : G.Le G' := ⟨List.prefix_append _ _, rfl, List.prefix_refl _⟩
  have hθl : θ.length = n := by simp [θ, objVars]
  have hfix : ∀ A : Tree, PartialHorn.Scoped n A = true → PartialHorn.subst θ A = A :=
    fun A hA ↦ subst_vars n A hA
  have hdefs : ∀ (k : ℕ) (d : Definition), G.defs[k]? = some d →
      (ext cds).sig[G.base + k]? = some d.sig := fun k d hd ↦ by
    simpa using getElem?_sig_compileDefs (pre := []) (by simpa using hb) hc hd
  obtain ⟨hFs, hBt⟩ := compile_sortOf hG hsorts hdefs t _ _ _ ht
    (sortOf_ctxObj hdefs Γ hΓ) (sortOf_stdEnv hdefs Γ hΓ)
  have hFsc : PartialHorn.Scoped n F = true := by simpa using PartialHorn.scoped_of_sortOf _ hFs
  have hG' : G'.WF := by
    refine ⟨fun k p' hp' ↦ ?_, hG.defs⟩
    rw [List.getElem?_append] at hp'
    split_ifs at hp' with hlt
    · exact hG.prims k p' hp'
    · rw [List.getElem?_singleton] at hp'
      split_ifs at hp'
      obtain rfl := Option.some_inj.mp hp'
      exact ⟨hFsc, isTy_ctxObj Γ hΓ, hBt⟩
  have hstd := compile_mono hle t _ _ _ ht
  have hk : G'.prims[G.prims.length]? = some p := by simp [G']
  have harr : ∀ (X : Tree) (e : List (Tree × Tree)), e.map Prod.snd = Γ →
      compile G' n (Term.arr G.prims.length θ (varsTerm Γ 0)) X e =
        some (comp F (tuple X (e.map Prod.fst)), B) := fun X e he ↦ by
    have hv := compile_varsTerm (G := G') (n := n) (X := X) Γ [] e he
    rw [List.length_nil, List.nil_append,
      ← hfix _ (scoped_of_isTy _ (isTy_ctxObj Γ hΓ))] at hv
    refine compile_arr_iff.mpr ⟨_, rfl, p, hk, _, hv, hθl, all_isTy_vars G' n, ?_⟩
    rw [hfix _ hFsc, hfix _ (scoped_of_isTy _ hBt)]
  have heq := compile_eq_iff.mpr ⟨_, _, rfl, _, _, harr _ _ (map_snd_stdEnv Γ), _, hstd, rfl⟩
  have hφ : typeIn G' n Γ (Term.eq (Term.arr G.prims.length θ (varsTerm Γ 0)) t) =
      some omega := by
    rw [typeIn]
    exact (congrArg (Option.map Prod.snd) heq).trans rfl
  refine exists_certSeq_of_valid hG' (compileDefs_of_prims hle rfl hc) hb hwf
    (a := ⟨n, Γ, [], _⟩) (fun _ h ↦ by simp at h) hφ fun M hM ↦ ?_
  obtain ⟨hpv, hdv⟩ := hval M hM
  have hpval : p.Val M := fun ws hws ↦
    (compile_hom hM hG hws (primsHom_of_val hM hG hdv.2 hpv hws) (defsHom_of_val hM hG hdv hws)
      t _ _ _ ht (stdEnv_hom hM hdv.2 hws Γ hΓ)).1
  have hpv' : ∀ (k : ℕ) (p' : Prim), G'.prims[k]? = some p' → p'.Val M := fun k p' hp' ↦ by
    rw [List.getElem?_append] at hp'
    split_ifs at hp' with hlt
    · exact hpv k p' hp'
    · rw [List.getElem?_singleton] at hp'
      split_ifs at hp'
      obtain rfl := Option.some_inj.mp hp'
      exact hpval
  refine ⟨all_isTy_mono hle hΓ, fun _ h ↦ by simp at h, hφ, fun ρ hρ ↦ ?_⟩
  have hps := primsHom_of_val hM hG' hdv.2 hpv' hρ
  have hds := defsHom_of_val hM hG' hdv hρ
  refine ⟨hps, hds, fun X e he hΓe _ r hr ↦ ?_⟩
  obtain ⟨t', u', htu, f, A, hf, g, hg, rfl⟩ := compile_eq_iff.mp hr
  simp only [List.cons.injEq, and_true] at htu
  obtain ⟨rfl, rfl⟩ := htu
  have hf' := harr X e hΓe
  rw [hf] at hf'
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some_inj.mp hf')
  obtain ⟨r', hr', hres⟩ := compile_of_stdEnv hM hG' hρ hps hds hstd he hΓe
  obtain rfl := Option.some_inj.mp (hr'.symm.trans hg)
  exact (holds_eq_iff hM hG' hρ hps hds he hf hg).mpr hres.2.symm

end RoundTrips

end Geb.FreeTopos.Internal

end
