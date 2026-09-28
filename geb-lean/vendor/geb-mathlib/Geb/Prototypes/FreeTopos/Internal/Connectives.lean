/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.FreeTopos.Internal.Logic
public import Geb.Prototypes.FreeTopos.Internal.Soundness

set_option doc.verso true in
/-!
# The meaning of the connectives in a model

The conditions under which the connectives' definitions ({name}`Geb.FreeTopos.Internal.Logic.defs`)
hold in a model of the theory extended by the combinators' definitions, placed at an index of the
constants' definitions ({lit}`LogicAt`). A formula holds over an object when its arrow is truth
after the arrow to the terminal object, and is true after an arrow into the object when its arrow
after that arrow is; the conditions are those of the Kripke–Joyal semantics of a topos
(\[MacLaneMoerdijk1992\], Section VI.6), stated of the arrows the formulas compile to, each
derived from the equality its connective is defined by.
Truth holds; a conjunction holds when both its formulas do; an implication, when its consequent is
true after every arrow after which its antecedent is; a universal quantification, when its
predicate is true at the generic element of the quantified type; an existential quantification
that holds makes true every formula that is true after each arrow at whose pairing with an element
the predicate is true; and a unique existential quantification that holds is an existential
quantification that holds whose predicate is true at the pairing of an arrow with at most one
element.

Description follows by unique choice ({name}`Geb.FreeTopos.unique_choice`, after
\[DubucSzyld2015\], Proposition 1.21): a formula of a new variable of which a unique
existential quantification holds holds at exactly one element of the variable's type
({lit}`description`). The language has no description operator: an arrow a functional relation
determines is named by the relation, and constructed in every model from the classifier.

## Main definitions

* {lit}`LogicAt` — the connectives' definitions are among the constants'.

## Main statements

* {lit}`holds_tt`, {lit}`holds_conj_iff`, {lit}`holds_imp_iff`, {lit}`holds_all_iff`,
  {lit}`holds_ex_elim`, {lit}`holds_exu` — the connectives' conditions.
* {lit}`conj_comp_iff`, {lit}`imp_comp_iff`, {lit}`all_comp_iff`, {lit}`all_lam_inst` — the
  conditions after an arrow.
* {lit}`description` — a formula of which a unique existential quantification holds holds at
  exactly one element.

## References

* \[MacLaneMoerdijk1992\]
* \[DubucSzyld2015\]

## Tags

internal language, Kripke–Joyal semantics, unique choice, description, local set theory
-/

set_option doc.verso true

@[expose] public section

namespace Geb.FreeTopos.Internal

open PartialHorn (Tree op eval Model IsModel)
open Sorts
open scoped FinEnum

universe v

/-- The connectives' definitions are those of {lit}`G` from the index {lit}`o`. -/
def LogicAt (G : Globals) (o : ℕ) : Prop :=
  ∀ (k : ℕ) (d : Defn), (Logic.defs o)[k]? = some d → G.defs[o + k]? = some (.language d)

/-- A map with failure of a list of one element succeeds at the element. -/
theorem mapM_one {α β : Type} {f : α → Option β} {a : α} {rs : List β}
    (h : [a].mapM f = some rs) : ∃ x, f a = some x ∧ rs = [x] := by
  simp only [List.mapM_cons, List.mapM_nil, Option.bind_eq_bind, Option.bind_eq_some_iff,
    Option.pure_def, Option.some.injEq] at h
  obtain ⟨x, hx, _, rfl, rfl⟩ := h
  exact ⟨x, hx, rfl⟩

/-- A map with failure of a list of two elements succeeds at each. -/
theorem mapM_two {α β : Type} {f : α → Option β} {a b : α} {rs : List β}
    (h : [a, b].mapM f = some rs) : ∃ x y, f a = some x ∧ f b = some y ∧ rs = [x, y] := by
  simp only [List.mapM_cons, List.mapM_nil, Option.bind_eq_bind, Option.bind_eq_some_iff,
    Option.pure_def, Option.some.injEq] at h
  obtain ⟨x, hx, _, ⟨y, hy, _, rfl, rfl⟩, rfl⟩ := h
  exact ⟨x, y, hx, hy, rfl⟩

section Connectives

variable {defs : List PartialHorn.Defn} {M : Model.{v} (ext defs).sig} {ρ : List M.Val}

/-- Related results hold together. -/
theorem holds_congr {X : Tree} {r r' : Tree × Tree} (h : ResEq M ρ r r') :
    Holds M ρ X r ↔ Holds M ρ X r' :=
  ⟨fun hr ↦ ⟨h.1.trans hr.1, h.2.trans hr.2⟩, fun hr ↦ ⟨h.1.symm.trans hr.1, h.2.symm.trans hr.2⟩⟩

/-- Pairings are equal exactly when their components are. -/
theorem pair_eq_iff (hM : IsModel (ext defs) M) {f g f' g' X A B : Tree} (hf : Hom M ρ f X A)
    (hg : Hom M ρ g X B) (hf' : Hom M ρ f' X A) (hg' : Hom M ρ g' X B) :
    eval M ρ (pair f g) = eval M ρ (pair f' g') ↔
      eval M ρ f = eval M ρ f' ∧ eval M ρ g = eval M ρ g' :=
  ⟨fun h ↦ ⟨(fst_pair hM hf hg).symm.trans ((eval_op₂_congr 3 rfl h).trans (fst_pair hM hf' hg')),
    (snd_pair hM hf hg).symm.trans ((eval_op₂_congr 3 rfl h).trans (snd_pair hM hf' hg'))⟩,
    fun h ↦ eval_op₂_congr 9 h.1 h.2⟩

variable (hM : IsModel (ext defs) M) {G : Globals} (hG : G.WF) {n : ℕ}
  (hρ : ρ.map Sigma.fst = List.replicate n obj) (hps : PrimsHom M ρ G n) (hds : DefsHom M ρ G n)
  (hδ : DefnsOk M G) {o : ℕ} (hL : LogicAt G o)
include hM hG hρ hps hds hδ

/-- The application of a definition compiles to a result related to its unfolding's. -/
theorem compile_delta {k : ℕ} {d : Defn} (hd : G.defs[k]? = some (.language d)) {θ : List Tree}
    {args : List Term} {t : Term} (ht : Term.subst (Term.osubst θ d.body) (Term.substList args) = t)
    {X : Tree} {e : List (Tree × Tree)} (he : EnvHom M ρ G n X e) {r : Tree × Tree}
    (h : compile G n (Term.defn k θ args) X e = some r) :
    ∃ r', compile G n t X e = some r' ∧ ResEq M ρ r r' :=
  ht ▸ delta_sound hM hG hρ hps hds (Φ := []) hδ hd (e.map Prod.snd) θ args X e he rfl
    (fun _ h ↦ by simp at h) r h

omit hδ in
/-- A term weakened past two new variables compiles, in the environment extended by them, to its
arrow after the projection to the environment's object. -/
theorem compile_weaken_two {s : Term} {X a b : Tree} {e : List (Tree × Tree)}
    (he : EnvHom M ρ G n X e) (ha : IsObj M ρ a) (hb : IsObj M ρ b) {r : Tree × Tree}
    (h : compile G n s X e = some r) :
    ∃ r', compile G n (Term.rename (Term.rename s Nat.succ) Nat.succ) (prod (prod X a) b)
        (extEnv (prod X a) b (extEnv X a e)) = some r' ∧
      ResEq M ρ (comp r.1 (comp (fst X a) (fst (prod X a) b)), r.2) r' := by
  have hfP := fst_hom hM (isObj_prod hM he.1 ha) hb
  have hfX := fst_hom hM he.1 ha
  obtain ⟨r₃, hr₃, hr₃'⟩ := compile_precomp hM hG hρ hps hds h he (comp_hom hM hfP hfX)
    (e' := e.map fun p ↦ (comp (comp p.1 (fst X a)) (fst (prod X a) b), p.2))
    fun i p hp ↦ by
      simp only [precomp, List.getElem?_map, Option.map_eq_some_iff] at hp
      obtain ⟨q₀, hq₀, rfl⟩ := hp
      exact ⟨(comp (comp q₀.1 (fst X a)) (fst (prod X a) b), q₀.2), by simp [hq₀], rfl,
        (comp_assoc hM hfP hfX (he.2 q₀ (List.mem_of_getElem? hq₀)).1).symm⟩
  exact ⟨r₃, compile_rename (Term.rename s Nat.succ) _ (extEnv (prod X a) b (extEnv X a e)) _
    Nat.succ r₃ (compile_rename s _ ((extEnv X a e).map fun p ↦ (comp p.1 (fst (prod X a) b), p.2))
      _ Nat.succ r₃ hr₃ fun i _ ↦ by simp [extEnv, Function.comp_def])
    (fun i _ ↦ by simp [extEnv]), hr₃'⟩

include hL

/-- Truth holds. -/
theorem holds_tt {X : Tree} {e : List (Tree × Tree)} (he : EnvHom M ρ G n X e) {r : Tree × Tree}
    (h : compile G n (Logic.tt o) X e = some r) : Holds M ρ X r := by
  obtain ⟨r', h', hr⟩ := compile_delta hM hG hρ hps hds hδ (hL 0 _ rfl)
    (t := Term.eq Term.star Term.star) rfl he h
  refine (holds_congr hr).mpr ?_
  obtain ⟨t, u, htu, f, a, hf, g, hg, rfl⟩ := compile_eq_iff.mp h'
  obtain ⟨rfl, rfl⟩ : t = Term.star ∧ u = Term.star := by simpa using htu.symm
  obtain ⟨-, hfa⟩ := compile_star_iff.mp hf
  obtain ⟨-, hgb⟩ := compile_star_iff.mp hg
  simp only [Prod.mk.injEq] at hfa hgb
  obtain ⟨rfl, rfl⟩ := hfa
  obtain ⟨rfl, -⟩ := hgb
  exact ⟨rfl, chi_diag_pair_self hM (bang_hom hM he.1)⟩

/-- A conjunction holds exactly when both its formulas hold. -/
theorem holds_conj_iff {p q : Term} {X : Tree} {e : List (Tree × Tree)} (he : EnvHom M ρ G n X e)
    {r : Tree × Tree} (h : compile G n (Logic.conj o p q) X e = some r) :
    ∃ P Q, compile G n p X e = some (P, omega) ∧ compile G n q X e = some (Q, omega) ∧
      (Holds M ρ X r ↔ Holds M ρ X (P, omega) ∧ Holds M ρ X (Q, omega)) := by
  obtain ⟨d, rs, hd, hrs, -, -, hsnd, -⟩ := compile_defn_iff.mp h
  obtain rfl := Definition.language.inj (Option.some_inj.mp (hd.symm.trans (hL 1 _ rfl)))
  obtain ⟨⟨Q, c⟩, ⟨P, c'⟩, hq, hp, rfl⟩ := mapM_two hrs
  obtain ⟨rfl, rfl⟩ : c = omega ∧ c' = omega := by simpa [subst_omega] using hsnd
  refine ⟨P, Q, hp, hq, ?_⟩
  obtain ⟨r', h', hr⟩ := compile_delta hM hG hρ hps hds hδ (hL 1 _ rfl)
    (t := Term.eq (Term.pair p q) (Term.pair (Logic.tt o) (Logic.tt o))) rfl he h
  obtain ⟨t, u, htu, f, a, hf, g, hg, rfl⟩ := compile_eq_iff.mp h'
  simp only [List.cons.injEq, and_true] at htu
  obtain ⟨rfl, rfl⟩ := htu
  obtain ⟨t₁, u₁, f₁, a₁, g₁, b₁, htu₁, hf₁, hg₁, hfa⟩ := compile_pair_iff.mp hf
  simp only [List.cons.injEq, and_true] at htu₁
  obtain ⟨rfl, rfl⟩ := htu₁
  obtain ⟨t₂, u₂, f₂, a₂, g₂, b₂, htu₂, hf₂, hg₂, hgb⟩ := compile_pair_iff.mp hg
  simp only [List.cons.injEq, and_true] at htu₂
  obtain ⟨rfl, rfl⟩ := htu₂
  rw [hp] at hf₁
  rw [hq] at hg₁
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some_inj.mp hf₁)
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some_inj.mp hg₁)
  rw [hf₂] at hg₂
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some_inj.mp hg₂)
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj hfa
  have hT := holds_tt hM hG hρ hps hds hδ hL he hf₂
  obtain ⟨rfl, -⟩ := prod_inj (Prod.mk.inj hgb).2
  have hty := compile_hom hM hG hρ hps hds
  have hP := (hty _ _ _ _ hp he).1
  have hQ := (hty _ _ _ _ hq he).1
  have hT' := (hty _ _ _ _ hf₂ he).1
  rw [holds_congr hr, holds_eq_iff hM hG hρ hps hds he hf hg, ← (Prod.mk.inj hgb).1,
    pair_eq_iff hM hP hQ hT' hT']
  simp only [Holds, true_and, hT.2]

/-- A conjunction is true after an arrow exactly when both its formulas are. -/
theorem conj_comp_iff {p q : Term} {X : Tree} {e : List (Tree × Tree)} (he : EnvHom M ρ G n X e)
    {C P Q : Tree} (hc : compile G n (Logic.conj o p q) X e = some (C, omega))
    (hp : compile G n p X e = some (P, omega)) (hq : compile G n q X e = some (Q, omega))
    {Y h : Tree} (hh : Hom M ρ h Y X) :
    eval M ρ (comp C h) = eval M ρ (comp tru (bang Y)) ↔
      eval M ρ (comp P h) = eval M ρ (comp tru (bang Y)) ∧
        eval M ρ (comp Q h) = eval M ρ (comp tru (bang Y)) := by
  have he' := envHom_precomp hM he hh
  obtain ⟨rc, hc', hrc⟩ := compile_precomp hM hG hρ hps hds hc he hh (envEq_refl _)
  obtain ⟨P', Q', hp', hq', hiff⟩ := holds_conj_iff hM hG hρ hps hds hδ hL he' hc'
  obtain ⟨rp, hrp, hrp'⟩ := compile_precomp hM hG hρ hps hds hp he hh (envEq_refl _)
  obtain ⟨rq, hrq, hrq'⟩ := compile_precomp hM hG hρ hps hds hq he hh (envEq_refl _)
  rw [hp'] at hrp
  rw [hq'] at hrq
  obtain rfl := Option.some_inj.mp hrp
  obtain rfl := Option.some_inj.mp hrq
  have key := (holds_congr (X := Y) hrc).trans hiff
  simp only [Holds, true_and, hrp'.2, hrq'.2] at key
  exact key

/-- An implication holds exactly when its consequent is true after every arrow after which its
antecedent is. -/
theorem holds_imp_iff {p q : Term} {X : Tree} {e : List (Tree × Tree)} (he : EnvHom M ρ G n X e)
    {r : Tree × Tree} (h : compile G n (Logic.imp o p q) X e = some r) :
    ∃ P Q, compile G n p X e = some (P, omega) ∧ compile G n q X e = some (Q, omega) ∧
      (Holds M ρ X r ↔ ∀ Y k : Tree, Hom M ρ k Y X →
        eval M ρ (comp P k) = eval M ρ (comp tru (bang Y)) →
          eval M ρ (comp Q k) = eval M ρ (comp tru (bang Y))) := by
  obtain ⟨d, rs, hd, hrs, -, -, hsnd, -⟩ := compile_defn_iff.mp h
  obtain rfl := Definition.language.inj (Option.some_inj.mp (hd.symm.trans (hL 2 _ rfl)))
  obtain ⟨⟨Q, c⟩, ⟨P, c'⟩, hq, hp, rfl⟩ := mapM_two hrs
  obtain ⟨rfl, rfl⟩ : c = omega ∧ c' = omega := by simpa [subst_omega] using hsnd
  refine ⟨P, Q, hp, hq, ?_⟩
  obtain ⟨r', h', hr⟩ := compile_delta hM hG hρ hps hds hδ (hL 2 _ rfl)
    (t := Term.eq (Logic.conj o p q) p) rfl he h
  obtain ⟨t, u, htu, C, a, hC, g, hg, rfl⟩ := compile_eq_iff.mp h'
  simp only [List.cons.injEq, and_true] at htu
  obtain ⟨rfl, rfl⟩ := htu
  rw [hp] at hg
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some_inj.mp hg)
  have hty := compile_hom hM hG hρ hps hds
  have hCh := (hty _ _ _ _ hC he).1
  have hPh := (hty _ _ _ _ hp he).1
  have hconj : ∀ {Y k : Tree}, Hom M ρ k Y X → _ := fun hk ↦
    conj_comp_iff hM hG hρ hps hds hδ hL he hC hp hq hk
  rw [holds_congr hr, holds_eq_iff hM hG hρ hps hds he hC hp]
  refine ⟨fun hCP Y k hk hPk ↦ ((hconj hk).mp ((eval_op₂_congr 3 hCP rfl).trans hPk)).2,
    fun hPQ ↦ omega_ext hM hCh hPh ?_ ?_⟩
  · obtain ⟨hi, hCi⟩ := truthIncl_hom hM hCh
    exact ((hconj hi).mp hCi).1
  · obtain ⟨hi, hPi⟩ := truthIncl_hom hM hPh
    exact (hconj hi).mpr ⟨hPi, hPQ _ _ hi hPi⟩

/-- A universal quantification holds exactly when the predicate is true at the generic element,
the second projection of the product with the quantified type. -/
theorem holds_all_iff {a : Tree} {P : Term} {X : Tree} {e : List (Tree × Tree)}
    (he : EnvHom M ρ G n X e) {r : Tree × Tree} (h : compile G n (Logic.all o a P) X e = some r) :
    ∃ F, IsTy G n a = true ∧ compile G n P X e = some (F, exp a omega) ∧
      (Holds M ρ X r ↔ eval M ρ (comp (ev a omega) (pair (comp F (fst X a)) (snd X a))) =
        eval M ρ (comp tru (bang (prod X a)))) := by
  obtain ⟨d, rs, hd, hrs, -, hθ, hsnd, -⟩ := compile_defn_iff.mp h
  obtain rfl := Definition.language.inj (Option.some_inj.mp (hd.symm.trans (hL 3 _ rfl)))
  obtain ⟨⟨F, c⟩, hP, rfl⟩ := mapM_one hrs
  obtain rfl : c = exp a omega := by simpa [subst_exp, subst_x, subst_omega] using hsnd
  have ha : IsTy G n a = true := by simpa using hθ
  refine ⟨F, ha, hP, ?_⟩
  obtain ⟨r', h', hr⟩ := compile_delta hM hG hρ hps hds hδ (hL 3 _ rfl)
    (t := Term.eq P (Term.lam a (Logic.tt o))) rfl he h
  obtain ⟨t, u, htu, f, A, hf, g, hg, rfl⟩ := compile_eq_iff.mp h'
  simp only [List.cons.injEq, and_true] at htu
  obtain ⟨rfl, rfl⟩ := htu
  rw [hP] at hf
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some_inj.mp hf)
  obtain ⟨t₁, T, b, ht₁, -, hT, hgb⟩ := compile_lam_iff.mp hg
  obtain rfl : t₁ = Logic.tt o := by simpa using ht₁.symm
  obtain ⟨rfl, -⟩ := Prod.mk.inj hgb
  have hA := isObj_of_isTy hM hds.2 hρ a ha
  have he' := he.ext hM hA ha
  have hTt := holds_tt hM hG hρ hps hds hδ hL he' hT
  obtain rfl : b = omega := hTt.1
  have hTh := (compile_hom hM hG hρ hps hds _ _ _ _ hT he').1
  have hFh := (compile_hom hM hG hρ hps hds _ _ _ _ hP he).1
  rw [holds_congr hr, holds_eq_iff hM hG hρ hps hds he hP hg, ← hTt.2]
  exact ⟨fun hFT ↦ (eval_op₂_congr 3 rfl (eval_op₂_congr 9 (eval_op₂_congr 3 hFT rfl) rfl)).trans
      (ev_curry hM he.1 hA hTh),
    fun hFT ↦ (curry_eta hM hA (isObj_omega hM) hFh).symm.trans (eval_op₃_congr 24 rfl rfl hFT)⟩

/-- An implication is true after an arrow exactly when its consequent is true after every
arrow through it after which its antecedent is. -/
theorem imp_comp_iff {p q : Term} {X : Tree} {e : List (Tree × Tree)} (he : EnvHom M ρ G n X e)
    {I P Q : Tree} (hi : compile G n (Logic.imp o p q) X e = some (I, omega))
    (hp : compile G n p X e = some (P, omega)) (hq : compile G n q X e = some (Q, omega))
    {Y k : Tree} (hk : Hom M ρ k Y X) :
    eval M ρ (comp I k) = eval M ρ (comp tru (bang Y)) ↔ ∀ Z k' : Tree, Hom M ρ k' Z Y →
      eval M ρ (comp P (comp k k')) = eval M ρ (comp tru (bang Z)) →
        eval M ρ (comp Q (comp k k')) = eval M ρ (comp tru (bang Z)) := by
  have he' := envHom_precomp hM he hk
  obtain ⟨ri, hi', hri⟩ := compile_precomp hM hG hρ hps hds hi he hk (envEq_refl _)
  obtain ⟨P', Q', hp', hq', hiff⟩ := holds_imp_iff hM hG hρ hps hds hδ hL he' hi'
  obtain ⟨rp, hrp, hrp'⟩ := compile_precomp hM hG hρ hps hds hp he hk (envEq_refl _)
  obtain ⟨rq, hrq, hrq'⟩ := compile_precomp hM hG hρ hps hds hq he hk (envEq_refl _)
  rw [hp'] at hrp
  rw [hq'] at hrq
  obtain rfl := Option.some_inj.mp hrp
  obtain rfl := Option.some_inj.mp hrq
  have hty := compile_hom hM hG hρ hps hds
  have hP : Hom M ρ P X omega := (hty _ _ _ _ hp he).1
  have hQ : Hom M ρ Q X omega := (hty _ _ _ _ hq he).1
  have key := (holds_congr (X := Y) hri).trans hiff
  simp only [Holds, true_and] at key
  rw [key]
  have eP : eval M ρ P' = eval M ρ (comp P k) := hrp'.2
  have eQ : eval M ρ Q' = eval M ρ (comp Q k) := hrq'.2
  refine forall_congr' fun Z ↦ forall_congr' fun k' ↦ forall_congr' fun hk' ↦ ?_
  have eP' : eval M ρ (comp P' k') = eval M ρ (comp P (comp k k')) :=
    (eval_op₂_congr 3 eP rfl).trans (comp_assoc hM hk' hk hP).symm
  have eQ' : eval M ρ (comp Q' k') = eval M ρ (comp Q (comp k k')) :=
    (eval_op₂_congr 3 eQ rfl).trans (comp_assoc hM hk' hk hQ).symm
  rw [eP', eQ']

/-- A universal quantification is true after an arrow exactly when the predicate after it is
true at the generic element. -/
theorem all_comp_iff {a : Tree} {Pr : Term} {X : Tree} {e : List (Tree × Tree)}
    (he : EnvHom M ρ G n X e) {A F : Tree}
    (h : compile G n (Logic.all o a Pr) X e = some (A, omega))
    (hF : compile G n Pr X e = some (F, exp a omega)) {Y k : Tree} (hk : Hom M ρ k Y X) :
    eval M ρ (comp A k) = eval M ρ (comp tru (bang Y)) ↔
      eval M ρ (comp (ev a omega) (pair (comp (comp F k) (fst Y a)) (snd Y a))) =
        eval M ρ (comp tru (bang (prod Y a))) := by
  have he' := envHom_precomp hM he hk
  obtain ⟨ra, ha', hra⟩ := compile_precomp hM hG hρ hps hds h he hk (envEq_refl _)
  obtain ⟨F', -, hF', hiff⟩ := holds_all_iff hM hG hρ hps hds hδ hL he' ha'
  obtain ⟨rf, hrf, hrf'⟩ := compile_precomp hM hG hρ hps hds hF he hk (envEq_refl _)
  rw [hF'] at hrf
  obtain rfl := Option.some_inj.mp hrf
  have key := (holds_congr (X := Y) hra).trans hiff
  simp only [Holds, true_and] at key
  have eF : eval M ρ (comp (ev a omega) (pair (comp F' (fst Y a)) (snd Y a))) =
      eval M ρ (comp (ev a omega) (pair (comp (comp F k) (fst Y a)) (snd Y a))) :=
    eval_op₂_congr 3 rfl (eval_op₂_congr 9 (eval_op₂_congr 3 hrf'.2 rfl) rfl)
  rw [key, eF]

/-- A universal quantification of an abstraction true after an arrow has its body true after
the pairing of the arrow with each element. -/
theorem all_lam_inst {a : Tree} {b : Term} {X : Tree} {e : List (Tree × Tree)}
    (he : EnvHom M ρ G n X e) {A : Tree}
    (h : compile G n (Logic.all o a (Term.lam a b)) X e = some (A, omega)) {Bd : Tree}
    (hb : compile G n b (prod X a) (extEnv X a e) = some (Bd, omega)) {Y k y : Tree}
    (hk : Hom M ρ k Y X) (hy : Hom M ρ y Y a)
    (hA : eval M ρ (comp A k) = eval M ρ (comp tru (bang Y))) :
    eval M ρ (comp Bd (pair k y)) = eval M ρ (comp tru (bang Y)) := by
  obtain ⟨F₁, ha, hF₁, -⟩ := holds_all_iff hM hG hρ hps hds hδ hL he h
  obtain ⟨t, Bd', c, ht, -, hb', hFc⟩ := compile_lam_iff.mp hF₁
  obtain rfl := (List.cons.inj ht).1
  rw [hb] at hb'
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some_inj.mp hb')
  obtain ⟨rfl, -⟩ := Prod.mk.inj hFc
  have hAa := isObj_of_isTy hM hds.2 hρ a ha
  have hY := hk.isObj_dom
  have hBh : Hom M ρ Bd (prod X a) omega :=
    (compile_hom hM hG hρ hps hds _ _ _ _ hb (he.ext hM hAa ha)).1
  have hc := curry_hom hM he.1 hAa hBh
  have hfY := fst_hom hM hY hAa
  have hsY := snd_hom hM hY hAa
  have hiy := pair_hom hM (idt_hom hM hY) hy
  have hgen := (all_comp_iff hM hG hρ hps hds hδ hL he h hF₁ hk).mp hA
  -- the generic element after the pairing of the identity with the element
  refine Eq.trans ?_ ((eval_op₂_congr 3 hgen rfl).trans (truth_comp hM hiy))
  refine (ev_curry_pair hM he.1 hAa hBh hk hy).symm.trans ?_
  refine Eq.trans ?_ (comp_assoc hM hiy (pair_hom hM (comp_hom hM hfY (comp_hom hM hk hc)) hsY)
    (ev_hom hM hAa (isObj_omega hM)))
  refine eval_op₂_congr 3 rfl ((eval_op₂_congr 9 ?_ (snd_pair hM (idt_hom hM hY) hy).symm).trans
    (pair_comp hM (comp_hom hM hfY (comp_hom hM hk hc)) hsY hiy).symm)
  have hck := comp_hom hM hk hc
  exact ((comp_idt hM hck).symm.trans (eval_op₂_congr 3 rfl
    (fst_pair hM (idt_hom hM hY) hy).symm)).trans (comp_assoc hM hiy hfY hck)

/-- An existential quantification that holds makes true every arrow into the subobject
classifier that is true after each arrow at whose pairing with an element the predicate is
true. -/
theorem holds_ex_elim {a : Tree} {Pr : Term} {X : Tree} {e : List (Tree × Tree)}
    (he : EnvHom M ρ G n X e) {r : Tree × Tree} (h : compile G n (Logic.ex o a Pr) X e = some r)
    (hr : Holds M ρ X r) {F : Tree} (hF : compile G n Pr X e = some (F, exp a omega))
    {R : Tree} (hR : Hom M ρ R X omega)
    (hRF : ∀ Y k y : Tree, Hom M ρ k Y X → Hom M ρ y Y a →
      eval M ρ (comp (ev a omega) (pair (comp F k) y)) = eval M ρ (comp tru (bang Y)) →
        eval M ρ (comp R k) = eval M ρ (comp tru (bang Y))) :
    eval M ρ R = eval M ρ (comp tru (bang X)) := by
  obtain ⟨d, rs, hd, -, -, hθ, -, -⟩ := compile_defn_iff.mp h
  obtain rfl := Definition.language.inj (Option.some_inj.mp (hd.symm.trans (hL 7 _ rfl)))
  have ha : IsTy G n a = true := by simpa using hθ
  have hA := isObj_of_isTy hM hds.2 hρ a ha
  have hO := isObj_omega (ρ := ρ) hM
  have hX := he.1
  have hty := compile_hom hM hG hρ hps hds
  -- the unfolding: every formula implied by the predicate's consequences holds
  obtain ⟨r', h', hr'⟩ := compile_delta hM hG hρ hps hds hδ (hL 7 _ rfl) (θ := [a])
    (args := [Pr])
    (t := Logic.all o omega (Term.lam omega (Logic.imp o (Logic.all o a (Term.lam a
      (Logic.imp o (Term.app (Term.rename (Term.rename Pr Nat.succ) Nat.succ) (Term.var 0))
        (Term.var 1)))) (Term.var 0)))) rfl he h
  obtain ⟨F₁, -, hF₁, hiff₁⟩ := holds_all_iff hM hG hρ hps hds hδ hL he h'
  obtain ⟨t₁, B, b, ht₁, -, hB, hFb⟩ := compile_lam_iff.mp hF₁
  obtain rfl := (List.cons.inj ht₁).1
  obtain ⟨rfl, hb⟩ := Prod.mk.inj hFb
  obtain ⟨-, rfl⟩ := exp_inj hb
  have he₁ := he.ext hM hO isTy_omega
  have hBh : Hom M ρ B (prod X omega) omega := (hty _ _ _ _ hB he₁).1
  have hBt : eval M ρ B = eval M ρ (comp tru (bang (prod X omega))) :=
    (ev_curry hM hX hO hBh).symm.trans (hiff₁.mp ((holds_congr hr').mp hr))
  -- the formula at the pairing of the identity with the arrow
  obtain ⟨PA, QR, hPA, hQR, -⟩ := holds_imp_iff hM hG hρ hps hds hδ hL he₁ hB
  obtain ⟨-, hQR'⟩ := compile_var_iff.mp hQR
  obtain rfl : QR = snd X omega := by simpa [extEnv] using hQR'.symm
  have hk := pair_hom hM (idt_hom hM hX) hR
  have hImp := (imp_comp_iff hM hG hρ hps hds hδ hL he₁ hB hPA hQR hk).mp
    ((eval_op₂_congr 3 hBt rfl).trans (truth_comp hM hk)) X (idt X) (idt_hom hM hX)
  have hkid : eval M ρ (comp (pair (idt X) R) (idt X)) = eval M ρ (pair (idt X) R) :=
    comp_idt hM hk
  have hsndk : eval M ρ (comp (snd X omega) (pair (idt X) R)) = eval M ρ R :=
    snd_pair hM (idt_hom hM hX) hR
  refine hsndk.symm.trans ((eval_op₂_congr 3 rfl hkid).symm.trans (hImp ?_))
  refine (eval_op₂_congr 3 rfl hkid).trans ?_
  -- the universal quantification over the type, at the generic element
  obtain ⟨FA, -, hFA, -⟩ := holds_all_iff hM hG hρ hps hds hδ hL he₁ hPA
  refine (all_comp_iff hM hG hρ hps hds hδ hL he₁ hPA hFA hk).mpr ?_
  obtain ⟨t₂, I, c, ht₂, -, hI, hFc⟩ := compile_lam_iff.mp hFA
  obtain rfl := (List.cons.inj ht₂).1
  obtain ⟨rfl, hc⟩ := Prod.mk.inj hFc
  obtain ⟨-, rfl⟩ := exp_inj hc
  have he₂ := he₁.ext hM hA ha
  have hIh : Hom M ρ I (prod (prod X omega) a) omega := (hty _ _ _ _ hI he₂).1
  have hfa := fst_hom hM hX hA
  have hsa := snd_hom hM hX hA
  have hm₁ := comp_hom hM hfa hk
  have hm := pair_hom hM hm₁ hsa
  refine (eval_op₂_congr 3 rfl (eval_op₂_congr 9 (comp_assoc hM hfa hk
    (curry_hom hM (isObj_prod hM hX hO) hA hIh)).symm rfl)).trans
    ((ev_curry_pair hM (isObj_prod hM hX hO) hA hIh hm₁ hsa).trans ?_)
  -- the implication at the generic element: the predicate's instance implies the formula
  obtain ⟨Pa, Rv, hPa, hRv, -⟩ := holds_imp_iff hM hG hρ hps hds hδ hL he₂ hI
  refine (imp_comp_iff hM hG hρ hps hds hδ hL he₂ hI hPa hRv hm).mpr fun Z k' hk' hPk ↦ ?_
  have hPo := isObj_prod hM hX hO
  have hfP := fst_hom hM hPo hA
  have hsP := snd_hom hM hPo hA
  have hfX := fst_hom hM hX hO
  have hsX := snd_hom hM hX hO
  have hmk := comp_hom hM hk' hm
  have hfk := comp_hom hM hk' hfa
  have hsk := comp_hom hM hk' hsa
  -- the projections after the generic element
  have eP₁ : eval M ρ (comp (fst (prod X omega) a) (comp (pair (comp (pair (idt X) R) (fst X a))
      (snd X a)) k')) = eval M ρ (comp (comp (pair (idt X) R) (fst X a)) k') :=
    (comp_assoc hM hk' hm hfP).trans (eval_op₂_congr 3 (fst_pair hM hm₁ hsa) rfl)
  have eP₂ : eval M ρ (comp (snd (prod X omega) a) (comp (pair (comp (pair (idt X) R) (fst X a))
      (snd X a)) k')) = eval M ρ (comp (snd X a) k') :=
    (comp_assoc hM hk' hm hsP).trans (eval_op₂_congr 3 (snd_pair hM hm₁ hsa) rfl)
  have eP₃ : eval M ρ (comp (comp (pair (idt X) R) (fst X a)) k') =
      eval M ρ (comp (pair (idt X) R) (comp (fst X a) k')) := (comp_assoc hM hk' hfa hk).symm
  have eX : ∀ {g W : Tree}, Hom M ρ g (prod X omega) W →
      eval M ρ (comp (comp g (fst (prod X omega) a)) (comp (pair (comp (pair (idt X) R)
        (fst X a)) (snd X a)) k')) =
        eval M ρ (comp (comp g (pair (idt X) R)) (comp (fst X a) k')) :=
    fun hg ↦ (comp_assoc hM hmk hfP hg).symm.trans ((eval_op₂_congr 3 rfl (eP₁.trans eP₃)).trans
      (comp_assoc hM hfk hk hg))
  -- the variable of the formula
  obtain ⟨-, hRv'⟩ := compile_var_iff.mp hRv
  obtain rfl : Rv = comp (snd X omega) (fst (prod X omega) a) := by
    simpa [extEnv] using hRv'.symm
  -- the predicate, renamed past the two new variables
  obtain ⟨r₃, hr₄, hr₃'⟩ := compile_weaken_two hM hG hρ hps hds he hO hA hF
  obtain ⟨t, u, htu, f, a', b', hf, g, hg, hPab⟩ := compile_app_iff.mp hPa
  simp only [List.cons.injEq, and_true] at htu
  obtain ⟨rfl, rfl⟩ := htu
  obtain ⟨-, hg'⟩ := compile_var_iff.mp hg
  obtain ⟨rfl, ha'⟩ : g = snd (prod X omega) a ∧ a' = a := by simpa [extEnv] using hg'.symm
  obtain rfl : a = a' := ha'.symm
  rw [hr₄] at hf
  obtain rfl := Option.some_inj.mp hf
  obtain ⟨-, rfl⟩ := exp_inj hr₃'.1
  obtain ⟨rfl, -⟩ := Prod.mk.inj hPab
  have hFh : Hom M ρ F X (exp a omega) := (hty _ _ _ _ hF he).1
  have hfh : Hom M ρ f (prod (prod X omega) a) (exp a omega) := (hty _ _ _ _ hr₄ he₂).1
  have ef : eval M ρ f = eval M ρ (comp F (comp (fst X omega) (fst (prod X omega) a))) := hr₃'.2
  have hev := ev_hom hM hA hO
  -- the predicate's instance at the generic element
  have eh : eval M ρ (comp (comp (fst X omega) (fst (prod X omega) a))
      (comp (pair (comp (pair (idt X) R) (fst X a)) (snd X a)) k')) =
      eval M ρ (comp (fst X a) k') :=
    (eX hfX).trans ((eval_op₂_congr 3 (fst_pair hM (idt_hom hM hX) hR) rfl).trans
      (idt_comp hM hfk))
  have ef' : eval M ρ (comp f (comp (pair (comp (pair (idt X) R) (fst X a)) (snd X a)) k')) =
      eval M ρ (comp F (comp (fst X a) k')) :=
    (eval_op₂_congr 3 ef rfl).trans ((comp_assoc hM hmk (comp_hom hM hfP hfX) hFh).symm.trans
      (eval_op₂_congr 3 rfl eh))
  have hpre : eval M ρ (comp (ev a omega) (pair (comp F (comp (fst X a) k'))
      (comp (snd X a) k'))) = eval M ρ (comp tru (bang Z)) :=
    (eval_op₂_congr 3 rfl ((eval_op₂_congr 9 ef'.symm eP₂.symm).trans
      (pair_comp hM hfh hsP hmk).symm)).trans ((comp_assoc hM hmk (pair_hom hM hfh hsP) hev).trans
      hPk)
  -- the formula after the generic element
  refine (eX hsX).trans ((eval_op₂_congr 3 (snd_pair hM (idt_hom hM hX) hR) rfl).trans ?_)
  exact hRF Z _ _ hfk hsk hpre

/-- A unique existential quantification that holds is an existential quantification that
holds, and its predicate is true at the pairing of an arrow with at most one element. -/
theorem holds_exu {a : Tree} {Pr : Term} {X : Tree} {e : List (Tree × Tree)}
    (he : EnvHom M ρ G n X e) {r : Tree × Tree} (h : compile G n (Logic.exu o a Pr) X e = some r)
    (hr : Holds M ρ X r) :
    ∃ F, IsTy G n a = true ∧ compile G n Pr X e = some (F, exp a omega) ∧
      (∀ R : Tree, Hom M ρ R X omega → (∀ Y k y : Tree, Hom M ρ k Y X → Hom M ρ y Y a →
        eval M ρ (comp (ev a omega) (pair (comp F k) y)) = eval M ρ (comp tru (bang Y)) →
          eval M ρ (comp R k) = eval M ρ (comp tru (bang Y))) →
        eval M ρ R = eval M ρ (comp tru (bang X))) ∧
      ∀ Y k y y' : Tree, Hom M ρ k Y X → Hom M ρ y Y a → Hom M ρ y' Y a →
        eval M ρ (comp (ev a omega) (pair (comp F k) y)) = eval M ρ (comp tru (bang Y)) →
        eval M ρ (comp (ev a omega) (pair (comp F k) y')) = eval M ρ (comp tru (bang Y)) →
          eval M ρ y = eval M ρ y' := by
  obtain ⟨d, rs, hd, hrs, -, hθ, hsnd, -⟩ := compile_defn_iff.mp h
  obtain rfl := Definition.language.inj (Option.some_inj.mp (hd.symm.trans (hL 8 _ rfl)))
  obtain ⟨⟨F, c⟩, hF, rfl⟩ := mapM_one hrs
  obtain rfl : c = exp a omega := by simpa [subst_exp, subst_x, subst_omega] using hsnd
  have ha : IsTy G n a = true := by simpa using hθ
  have hA := isObj_of_isTy hM hds.2 hρ a ha
  have hO := isObj_omega (ρ := ρ) hM
  have hty := compile_hom hM hG hρ hps hds
  obtain ⟨r', h', hr'⟩ := compile_delta hM hG hρ hps hds hδ (hL 8 _ rfl) (θ := [a])
    (args := [Pr]) (t := Logic.conj o (Logic.ex o a Pr) (Logic.all o a (Term.lam a
      (Logic.all o a (Term.lam a (Logic.imp o (Logic.conj o
        (Term.app (Term.rename (Term.rename Pr Nat.succ) Nat.succ) (Term.var 1))
        (Term.app (Term.rename (Term.rename Pr Nat.succ) Nat.succ) (Term.var 0)))
        (Term.eq (Term.var 1) (Term.var 0)))))))) rfl he h
  obtain ⟨PE, PU, hPE, hPU, hiff⟩ := holds_conj_iff hM hG hρ hps hds hδ hL he h'
  obtain ⟨hE, hU⟩ := hiff.mp ((holds_congr hr').mp hr)
  refine ⟨F, ha, hF, fun R hR hRF ↦ holds_ex_elim hM hG hρ hps hds hδ hL he hPE hE hF hR hRF,
    fun Y k y y' hk hy hy' h₁ h₂ ↦ ?_⟩
  -- the bodies of the two universal quantifications
  have he₁ := he.ext hM hA ha
  have he₂ := he₁.ext hM hA ha
  obtain ⟨F₁, -, hF₁, -⟩ := holds_all_iff hM hG hρ hps hds hδ hL he hPU
  obtain ⟨t₁, A₂, c₁, ht₁, -, hA₂, hFc₁⟩ := compile_lam_iff.mp hF₁
  obtain rfl := (List.cons.inj ht₁).1
  obtain ⟨-, rfl⟩ := exp_inj (Prod.mk.inj hFc₁).2
  obtain ⟨F₂, -, hF₂, -⟩ := holds_all_iff hM hG hρ hps hds hδ hL he₁ hA₂
  obtain ⟨t₂, I, c₂, ht₂, -, hI, hFc₂⟩ := compile_lam_iff.mp hF₂
  obtain rfl := (List.cons.inj ht₂).1
  obtain ⟨-, rfl⟩ := exp_inj (Prod.mk.inj hFc₂).2
  have hky := pair_hom hM hk hy
  have ht := pair_hom hM hky hy'
  have hI₁ := all_lam_inst hM hG hρ hps hds hδ hL he hPU hA₂ hk hy
    ((eval_op₂_congr 3 hU.2 rfl).trans (truth_comp hM hk))
  have hI₂ := all_lam_inst hM hG hρ hps hds hδ hL he₁ hA₂ hI hky hy' hI₁
  -- the implication at the pairing
  obtain ⟨C, Q, hC, hQ, -⟩ := holds_imp_iff hM hG hρ hps hds hδ hL he₂ hI
  have hti := comp_hom hM (idt_hom hM hk.isObj_dom) ht
  have eti : eval M ρ (comp (pair (pair k y) y') (idt Y)) = eval M ρ (pair (pair k y) y') :=
    comp_idt hM ht
  obtain ⟨A1, A0, hA1, hA0, -⟩ := holds_conj_iff hM hG hρ hps hds hδ hL he₂ hC
  -- the predicate's instances, and the equality, after the pairing
  obtain ⟨r₃, hr₄, hr₃'⟩ := compile_weaken_two hM hG hρ hps hds he hA hA hF
  have hFh : Hom M ρ F X (exp a omega) := (hty _ _ _ _ hF he).1
  have hfX := fst_hom hM he.1 hA
  have hsX := snd_hom hM he.1 hA
  have hfP := fst_hom hM (isObj_prod hM he.1 hA) hA
  have hsP := snd_hom hM (isObj_prod hM he.1 hA) hA
  have ek : eval M ρ (comp (comp (fst X a) (fst (prod X a) a)) (comp (pair (pair k y) y') (idt Y)))
      = eval M ρ k :=
    (comp_assoc hM hti hfP hfX).symm.trans ((eval_op₂_congr 3 rfl ((eval_op₂_congr 3 rfl eti).trans
      (fst_pair hM hky hy'))).trans (fst_pair hM hk hy))
  have ey : eval M ρ (comp (comp (snd X a) (fst (prod X a) a)) (comp (pair (pair k y) y') (idt Y)))
      = eval M ρ y :=
    (comp_assoc hM hti hfP hsX).symm.trans ((eval_op₂_congr 3 rfl ((eval_op₂_congr 3 rfl eti).trans
      (fst_pair hM hky hy'))).trans (snd_pair hM hk hy))
  have ey' : eval M ρ (comp (snd (prod X a) a) (comp (pair (pair k y) y') (idt Y))) =
      eval M ρ y' :=
    (eval_op₂_congr 3 rfl eti).trans (snd_pair hM hky hy')
  -- an application of the renamed predicate to a variable after the pairing
  have happ : ∀ {i : ℕ} {Ai g : Tree}, compile G n (Term.app (Term.rename (Term.rename Pr
      Nat.succ) Nat.succ) (Term.var i)) (prod (prod X a) a) (extEnv (prod X a) a (extEnv X a e)) =
        some (Ai, omega) →
      (extEnv (prod X a) a (extEnv X a e))[i]? = some (g, a) →
      eval M ρ (comp Ai (comp (pair (pair k y) y') (idt Y))) =
        eval M ρ (comp (ev a omega) (pair (comp F k) (comp g (comp (pair (pair k y) y')
          (idt Y))))) := fun {i Ai g} hAi hg ↦ by
    obtain ⟨u, w, huw, f, a', b', hf, g', hg', hfg⟩ := compile_app_iff.mp hAi
    simp only [List.cons.injEq, and_true] at huw
    obtain ⟨rfl, rfl⟩ := huw
    obtain ⟨-, hg''⟩ := compile_var_iff.mp hg'
    rw [hg] at hg''
    obtain ⟨hgg, haa⟩ := Prod.mk.inj (Option.some_inj.mp hg'')
    subst g' a'
    rw [hr₄] at hf
    have hr₃f := hr₃'
    rw [Option.some_inj.mp hf] at hr₃f
    obtain ⟨-, hb'⟩ := exp_inj hr₃f.1
    subst b'
    obtain ⟨hAi', -⟩ := Prod.mk.inj hfg
    subst Ai
    have hgh : Hom M ρ g (prod (prod X a) a) a := (he₂.2 _ (List.mem_of_getElem? hg)).1
    have hfh : Hom M ρ f (prod (prod X a) a) (exp a omega) :=
      (hty _ _ _ _ (hr₄.trans hf) he₂).1
    have ef : eval M ρ f = eval M ρ (comp F (comp (fst X a) (fst (prod X a) a))) := hr₃f.2
    refine (comp_assoc hM hti (pair_hom hM hfh hgh) (ev_hom hM hA hO)).symm.trans
      (eval_op₂_congr 3 rfl ((pair_comp hM hfh hgh hti).trans (eval_op₂_congr 9 ?_ rfl)))
    exact (eval_op₂_congr 3 ef rfl).trans ((comp_assoc hM hti (comp_hom hM hfP hfX) hFh).symm.trans
      (eval_op₂_congr 3 rfl ek))
  have hCt := (conj_comp_iff hM hG hρ hps hds hδ hL he₂ hC hA1 hA0 hti).mpr
    ⟨(happ hA1 (by simp [extEnv])).trans ((eval_op₂_congr 3 rfl (eval_op₂_congr 9 rfl ey)).trans
      h₁), (happ hA0 (by simp [extEnv])).trans ((eval_op₂_congr 3 rfl
        (eval_op₂_congr 9 rfl ey')).trans h₂)⟩
  have hQt := (imp_comp_iff hM hG hρ hps hds hδ hL he₂ hI hC hQ ht).mp hI₂ Y (idt Y)
    (idt_hom hM hk.isObj_dom) hCt
  -- the equality of the two elements
  obtain ⟨u, w, huw, f, b, hf, g, hg, hfg⟩ := compile_eq_iff.mp hQ
  simp only [List.cons.injEq, and_true] at huw
  obtain ⟨rfl, rfl⟩ := huw
  obtain ⟨-, hf'⟩ := compile_var_iff.mp hf
  obtain ⟨-, hg'⟩ := compile_var_iff.mp hg
  obtain ⟨hf₁, hb₁⟩ : f = comp (snd X a) (fst (prod X a) a) ∧ b = a := by
    simpa [extEnv] using hf'.symm
  obtain ⟨hg₁, -⟩ : g = snd (prod X a) a ∧ b = a := by simpa [extEnv] using hg'.symm
  subst f b g
  obtain ⟨hQ₁, -⟩ := Prod.mk.inj hfg
  subst Q
  have hvf := comp_hom hM hfP hsX
  have hy₁ := comp_hom hM hti hvf
  have hy₂ := comp_hom hM hti hsP
  refine ey.symm.trans ((eq_of_chi_diag hM hy₁ hy₂ ?_).trans ey')
  exact (eval_op₂_congr 3 rfl (pair_comp hM hvf hsP hti).symm).trans
    ((comp_assoc hM hti (pair_hom hM hvf hsP) (chi_diag_hom hM hA)).trans hQt)

/-- Description: a formula of a new variable of which a unique existential quantification holds
holds at an element of the variable's type, and at no other. -/
theorem description {B : Tree} {φ : Term} {X : Tree} {e : List (Tree × Tree)}
    (he : EnvHom M ρ G n X e) {r : Tree × Tree}
    (h : compile G n (Logic.exu o B (Term.lam B φ)) X e = some r) (hr : Holds M ρ X r) :
    ∃ x, Hom M ρ x X B ∧ (∃ q, compile G n φ X ((x, B) :: e) = some q ∧ Holds M ρ X q) ∧
      ∀ x', Hom M ρ x' X B →
        (∃ q, compile G n φ X ((x', B) :: e) = some q ∧ Holds M ρ X q) →
          eval M ρ x' = eval M ρ x := by
  obtain ⟨F, hB, hF, hex, huniq⟩ := holds_exu hM hG hρ hps hds hδ hL he h hr
  obtain ⟨t, Φ, c, ht, -, hΦ, hFc⟩ := compile_lam_iff.mp hF
  obtain rfl := (List.cons.inj ht).1
  obtain ⟨rfl, hc⟩ := Prod.mk.inj hFc
  obtain ⟨-, rfl⟩ := exp_inj hc
  have hBo := isObj_of_isTy hM hds.2 hρ B hB
  have hΦh : Hom M ρ Φ (prod X B) omega :=
    (compile_hom hM hG hρ hps hds _ _ _ _ hΦ (he.ext hM hBo hB)).1
  have hev : ∀ {Y k y : Tree}, Hom M ρ k Y X → Hom M ρ y Y B →
      eval M ρ (comp (ev B omega) (pair (comp (curry X B Φ) k) y)) =
        eval M ρ (comp Φ (pair k y)) := fun hk hy ↦ ev_curry_pair hM he.1 hBo hΦh hk hy
  obtain ⟨hx, hΦx, hxu⟩ := unique_choice hM he.1 hBo hΦh
    (fun R hR hRΦ ↦ hex R hR fun Y k y hk hy h₁ ↦ hRΦ Y k y hk hy ((hev hk hy).symm.trans h₁))
    (fun Y k y y' hk hy hy' h₁ h₂ ↦
      huniq Y k y y' hk hy hy' ((hev hk hy).trans h₁) ((hev hk hy').trans h₂))
  obtain ⟨q, hq, hqr⟩ := compile_at hM hG hρ hps hds he hB hΦ hx
  refine ⟨desc X B Φ, hx, ⟨q, hq, (holds_congr hqr).mp ⟨rfl, hΦx⟩⟩,
    fun x' hx' ⟨q', hq', hq'h⟩ ↦ hxu x' hx' ?_⟩
  obtain ⟨q'', hq'', hq''r⟩ := compile_at hM hG hρ hps hds he hB hΦ hx'
  rw [hq'] at hq''
  rw [Option.some_inj.mp hq''] at hq'h
  exact ((holds_congr hq''r).mpr hq'h).2

end Connectives

end Geb.FreeTopos.Internal

end
