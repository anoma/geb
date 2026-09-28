/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
-- Modified from geb-mathlib by scripts/geb-mathlib-backport.patch.
module

public import Geb.Prototypes.FreeTopos.Internal.Semantics

set_option doc.verso true in
/-!
# Substitution and the compilation

Substitution is composition, in the internal language's compilation to the combinators. Renaming
a term's variables compiles it in the environment of the renamed variables
({lit}`compile_rename`). A term with terms substituted for its variables has, in every model,
the arrow of the term in the environment of the substituted terms' arrows
({lit}`compile_subst`): under an abstraction the substituted terms are weakened, which renaming
makes the first projection's precomposition and naturality
({name}`Geb.FreeTopos.Internal.compile_comp`) the precomposition of their arrows. Substituting
objects for a term's object variables substitutes them in its arrow and type
({lit}`compile_osubst`).

## Main definitions

* {lit}`SubstEq` — a substitution compiling to the values of an environment.

## Main statements

* {lit}`compile_rename` — renaming is the renamed environment.
* {lit}`compile_subst` — substitution is composition.
* {lit}`compile_osubst` — substitution of objects commutes with the compilation.

## Tags

internal language, substitution, renaming, categorical semantics
-/

set_option doc.verso true

@[expose] public section

namespace Geb.FreeTopos.Internal

open PartialHorn (Tree op eval Model IsModel)
open Sorts
open scoped FinEnum

variable {G : Globals} {n : ℕ}

/-- A renamed term compiles in an environment whose variables at the renamed indices are the
term's environment's: renaming is the renamed environment. -/
theorem compile_rename (s : Term) :
    ∀ (X : Tree) (e e' : List (Tree × Tree)) (f : ℕ → ℕ) (r : Tree × Tree),
      compile G n s X e' = some r → (∀ i < e'.length, e[f i]? = e'[i]?) →
      compile G n (Term.rename s f) X e = some r := by
  refine RoseTree.ind (P := fun s ↦ ∀ (X : Tree) (e e' : List (Tree × Tree)) (f : ℕ → ℕ)
    (r : Tree × Tree), compile G n s X e' = some r → (∀ i < e'.length, e[f i]? = e'[i]?) →
      compile G n (Term.rename s f) X e = some r) (fun l cs ih ↦ ?_) s
  intro X e e' f r h hf
  rw [Term.rename_node]
  cases l with
  | var i =>
    obtain ⟨rfl, hi⟩ := compile_var_iff.mp h
    exact compile_var_iff.mpr ⟨rfl, (hf i (List.getElem?_eq_some_iff.mp hi).1).trans hi⟩
  | star =>
    obtain ⟨rfl, rfl⟩ := compile_star_iff.mp h
    exact compile_star_iff.mpr ⟨rfl, rfl⟩
  | pair =>
    obtain ⟨t, u, g, a, g', b, rfl, ht, hu, rfl⟩ := compile_pair_iff.mp h
    exact compile_pair_iff.mpr ⟨_, _, g, a, g', b, rfl, ih t (by simp) X e e' f _ ht hf,
      ih u (by simp) X e e' f _ hu hf, rfl⟩
  | fst =>
    obtain ⟨t, g, a, b, rfl, ht, rfl⟩ := compile_fst_iff.mp h
    exact compile_fst_iff.mpr ⟨_, g, a, b, rfl, ih t (by simp) X e e' f _ ht hf, rfl⟩
  | snd =>
    obtain ⟨t, g, a, b, rfl, ht, rfl⟩ := compile_snd_iff.mp h
    exact compile_snd_iff.mpr ⟨_, g, a, b, rfl, ih t (by simp) X e e' f _ ht hf, rfl⟩
  | lam a =>
    obtain ⟨t, g, b, rfl, hat, ht, rfl⟩ := compile_lam_iff.mp h
    refine compile_lam_iff.mpr ⟨_, g, b, rfl, hat,
      ih t (by simp) _ (extEnv X a e) (extEnv X a e') (Term.liftR f) _ ht fun i hi ↦ ?_, rfl⟩
    rcases i with _ | j
    · rfl
    · have hj : j < e'.length := by simpa [extEnv] using hi
      simp only [extEnv, Term.liftR, List.getElem?_cons_succ, List.getElem?_map, hf j hj]
  | app =>
    obtain ⟨t, u, rfl, g, a, b, ht, g', hu, rfl⟩ := compile_app_iff.mp h
    exact compile_app_iff.mpr ⟨_, _, rfl, g, a, b, ih t (by simp) X e e' f _ ht hf, g',
      ih u (by simp) X e e' f _ hu hf, rfl⟩
  | arr k θ =>
    obtain ⟨t, rfl, p, hp, g, ht, hl, hθ, rfl⟩ := compile_arr_iff.mp h
    exact compile_arr_iff.mpr ⟨_, rfl, p, hp, g, ih t (by simp) X e e' f _ ht hf, hl, hθ, rfl⟩
  | natRec =>
    obtain ⟨z, s, m, rfl, z', c, hz, s', hs, m', hm, rfl⟩ := compile_natRec_iff.mp h
    exact compile_natRec_iff.mpr ⟨z, s, _, rfl, z', c, hz, s', hs, m',
      ih m (by simp) X e e' f _ hm hf, rfl⟩
  | listRec =>
    obtain ⟨z, s, m, rfl, m', a, hm, z', c, hz, s', hs, rfl⟩ := compile_listRec_iff.mp h
    exact compile_listRec_iff.mpr ⟨z, s, _, rfl, m', a, ih m (by simp) X e e' f _ hm hf, z', c,
      hz, s', hs, rfl⟩
  | roseRec c =>
    obtain ⟨s, m, m', t, a, F, s', rfl, hc, hm, ht, hs, rfl⟩ := compile_roseRec_iff.mp h
    exact compile_roseRec_iff.mpr ⟨s, _, m', t, a, F, s', rfl, hc,
      ih m (by simp) X e e' f _ hm hf, ht, hs, rfl⟩
  | eq =>
    obtain ⟨t, u, rfl, f₁, a, ht, g, hu, rfl⟩ := compile_eq_iff.mp h
    exact compile_eq_iff.mpr ⟨_, _, rfl, f₁, a, ih t (by simp) X e e' f _ ht hf, g,
      ih u (by simp) X e e' f _ hu hf, rfl⟩
  | defn k θ =>
    obtain ⟨d, rs, hd, hrs, hl, hθ, hty, rfl⟩ := compile_defn_iff.mp h
    obtain ⟨rs', h₁, h₂⟩ := mapM_lift (R := Eq)
      (g := fun c ↦ compile G n (Term.rename c f) X e) cs hrs
      fun c hc r hr ↦ ⟨r, ih c hc X e e' f r hr hf, rfl⟩
    rw [List.forall₂_eq_eq_eq] at h₂
    subst h₂
    refine compile_defn_iff.mpr ⟨d, rs, hd, ?_, hl, hθ, hty, rfl⟩
    rw [List.map_map, List.mapM_map]
    exact h₁

/-- A term's type depends on its environment's types alone: in an environment of the same types,
over any object, it compiles to the same type. -/
theorem compile_retype (s : Term) :
    ∀ (X : Tree) (e : List (Tree × Tree)) (r : Tree × Tree), compile G n s X e = some r →
      ∀ (X' : Tree) (e' : List (Tree × Tree)), e'.map Prod.snd = e.map Prod.snd →
      ∃ f, compile G n s X' e' = some (f, r.2) := by
  refine RoseTree.ind (P := fun s ↦ ∀ (X : Tree) (e : List (Tree × Tree)) (r : Tree × Tree),
    compile G n s X e = some r → ∀ (X' : Tree) (e' : List (Tree × Tree)),
      e'.map Prod.snd = e.map Prod.snd → ∃ f, compile G n s X' e' = some (f, r.2))
    (fun l cs ih ↦ ?_) s
  intro X e r h X' e' he
  cases l with
  | var i =>
    obtain ⟨rfl, hi⟩ := compile_var_iff.mp h
    have hm := congrArg (·[i]?) he
    simp only [List.getElem?_map, hi, Option.map_some, Option.map_eq_some_iff] at hm
    obtain ⟨q, hq, hq₂⟩ := hm
    exact ⟨q.1, compile_var_iff.mpr ⟨rfl, by rw [hq, ← hq₂]⟩⟩
  | star =>
    obtain ⟨rfl, rfl⟩ := compile_star_iff.mp h
    exact ⟨_, compile_star_iff.mpr ⟨rfl, rfl⟩⟩
  | pair =>
    obtain ⟨t, u, f, a, g, b, rfl, ht, hu, rfl⟩ := compile_pair_iff.mp h
    obtain ⟨f', hf'⟩ := ih t (by simp) X e _ ht X' e' he
    obtain ⟨g', hg'⟩ := ih u (by simp) X e _ hu X' e' he
    exact ⟨_, compile_pair_iff.mpr ⟨t, u, f', a, g', b, rfl, hf', hg', rfl⟩⟩
  | fst =>
    obtain ⟨t, f, a, b, rfl, ht, rfl⟩ := compile_fst_iff.mp h
    obtain ⟨f', hf'⟩ := ih t (by simp) X e _ ht X' e' he
    exact ⟨_, compile_fst_iff.mpr ⟨t, f', a, b, rfl, hf', rfl⟩⟩
  | snd =>
    obtain ⟨t, f, a, b, rfl, ht, rfl⟩ := compile_snd_iff.mp h
    obtain ⟨f', hf'⟩ := ih t (by simp) X e _ ht X' e' he
    exact ⟨_, compile_snd_iff.mpr ⟨t, f', a, b, rfl, hf', rfl⟩⟩
  | lam a =>
    obtain ⟨t, f, b, rfl, hat, ht, rfl⟩ := compile_lam_iff.mp h
    obtain ⟨f', hf'⟩ := ih t (by simp) _ _ _ ht (prod X' a) (extEnv X' a e')
      (by simp [extEnv, he, Function.comp_def])
    exact ⟨_, compile_lam_iff.mpr ⟨t, f', b, rfl, hat, hf', rfl⟩⟩
  | app =>
    obtain ⟨t, u, rfl, f, a, b, ht, g, hu, rfl⟩ := compile_app_iff.mp h
    obtain ⟨f', hf'⟩ := ih t (by simp) X e _ ht X' e' he
    obtain ⟨g', hg'⟩ := ih u (by simp) X e _ hu X' e' he
    exact ⟨_, compile_app_iff.mpr ⟨t, u, rfl, f', a, b, hf', g', hg', rfl⟩⟩
  | arr k θ =>
    obtain ⟨t, rfl, p, hp, g, ht, hl, hθ, rfl⟩ := compile_arr_iff.mp h
    obtain ⟨g', hg'⟩ := ih t (by simp) X e _ ht X' e' he
    exact ⟨_, compile_arr_iff.mpr ⟨t, rfl, p, hp, g', hg', hl, hθ, rfl⟩⟩
  | natRec =>
    obtain ⟨z, s, m, rfl, z', c, hz, s', hs, m', hm, rfl⟩ := compile_natRec_iff.mp h
    obtain ⟨m'', hm''⟩ := ih m (by simp) X e _ hm X' e' he
    exact ⟨_, compile_natRec_iff.mpr ⟨z, s, m, rfl, z', c, hz, s', hs, m'', hm'', rfl⟩⟩
  | listRec =>
    obtain ⟨z, s, m, rfl, m', a, hm, z', c, hz, s', hs, rfl⟩ := compile_listRec_iff.mp h
    obtain ⟨m'', hm''⟩ := ih m (by simp) X e _ hm X' e' he
    exact ⟨_, compile_listRec_iff.mpr ⟨z, s, m, rfl, m'', a, hm'', z', c, hz, s', hs, rfl⟩⟩
  | roseRec c =>
    obtain ⟨s, m, m', t, a, F, s', rfl, hc, hm, ht, hs, rfl⟩ := compile_roseRec_iff.mp h
    obtain ⟨m'', hm''⟩ := ih m (by simp) X e _ hm X' e' he
    exact ⟨_, compile_roseRec_iff.mpr ⟨s, m, m'', t, a, F, s', rfl, hc, hm'', ht, hs, rfl⟩⟩
  | eq =>
    obtain ⟨t, u, rfl, f, a, ht, g, hu, rfl⟩ := compile_eq_iff.mp h
    obtain ⟨f', hf'⟩ := ih t (by simp) X e _ ht X' e' he
    obtain ⟨g', hg'⟩ := ih u (by simp) X e _ hu X' e' he
    exact ⟨_, compile_eq_iff.mpr ⟨t, u, rfl, f', a, hf', g', hg', rfl⟩⟩
  | defn k θ =>
    obtain ⟨d, rs, hd, hrs, hl, hθ, hty, rfl⟩ := compile_defn_iff.mp h
    obtain ⟨rs', hrs', hR⟩ := mapM_lift (R := fun r r' ↦ r'.2 = r.2)
      (g := fun c ↦ compile G n c X' e') cs hrs fun c hc r hr ↦ by
        obtain ⟨f, hf⟩ := ih c hc X e r hr X' e' he
        exact ⟨(f, r.2), hf, rfl⟩
    have hsnd : rs'.map Prod.snd = rs.map Prod.snd :=
      hR.rec (motive := fun rs rs' _ ↦ rs'.map Prod.snd = rs.map Prod.snd) rfl
        fun hr _ ih ↦ by simp [hr, ih]
    exact ⟨_, compile_defn_iff.mpr ⟨d, rs', hd, hrs', hl, hθ, hsnd.trans hty, rfl⟩⟩

section Substitution

universe v

variable {defs : List PartialHorn.Defn} {M : Model.{v} (ext defs).sig} {ρ : List M.Val}

variable (M ρ) in
/-- A substitution compiles, in an environment, to the values of another environment: each
variable of the other has a term whose arrow has the variable's type and its arrow's value. -/
def SubstEq (G : Globals) (n : ℕ) (X : Tree) (e : List (Tree × Tree)) (σ : ℕ → Term)
    (E : List (Tree × Tree)) : Prop :=
  ∀ (i : ℕ) (p : Tree × Tree), E[i]? = some p →
    ∃ q, compile G n (σ i) X e = some q ∧ ResEq M ρ p q

variable (hM : IsModel (ext defs) M)
include hM

/-- Substitution is composition: a term with terms substituted for its variables has, in an
environment, its type and the value of its arrow in the environment of the substituted terms'
arrows. -/
theorem compile_subst (hG : G.WF) (hρ : ρ.map Sigma.fst = List.replicate n obj)
    (hps : PrimsHom M ρ G n) (hds : DefsHom M ρ G n) (s : Term) :
    ∀ (X : Tree) (E : List (Tree × Tree)) (r : Tree × Tree), compile G n s X E = some r →
      ∀ (e : List (Tree × Tree)) (σ : ℕ → Term), EnvHom M ρ G n X e →
      SubstEq M ρ G n X e σ E →
      ∃ r', compile G n (Term.subst s σ) X e = some r' ∧ ResEq M ρ r r' := by
  refine RoseTree.ind (P := fun s ↦ ∀ (X : Tree) (E : List (Tree × Tree)) (r : Tree × Tree),
    compile G n s X E = some r → ∀ (e : List (Tree × Tree)) (σ : ℕ → Term),
      EnvHom M ρ G n X e → SubstEq M ρ G n X e σ E →
      ∃ r', compile G n (Term.subst s σ) X e = some r' ∧ ResEq M ρ r r')
    (fun l cs ih ↦ ?_) s
  intro X E r h e σ he hσ
  rw [Term.subst_node]
  cases l with
  | var i =>
    obtain ⟨rfl, hi⟩ := compile_var_iff.mp h
    exact hσ i r hi
  | star =>
    obtain ⟨rfl, rfl⟩ := compile_star_iff.mp h
    exact ⟨_, compile_star_iff.mpr ⟨rfl, rfl⟩, rfl, rfl⟩
  | pair =>
    obtain ⟨t, u, f, a, g, b, rfl, ht, hu, rfl⟩ := compile_pair_iff.mp h
    obtain ⟨⟨f', a'⟩, ht', rfl, hf⟩ := ih t (by simp) X E _ ht e σ he hσ
    obtain ⟨⟨g', b'⟩, hu', rfl, hg⟩ := ih u (by simp) X E _ hu e σ he hσ
    exact ⟨_, compile_pair_iff.mpr ⟨_, _, f', a', g', b', rfl, ht', hu', rfl⟩, rfl,
      eval_op₂_congr 9 hf hg⟩
  | fst =>
    obtain ⟨t, f, a, b, rfl, ht, rfl⟩ := compile_fst_iff.mp h
    obtain ⟨⟨f', p⟩, ht', rfl, hf⟩ := ih t (by simp) X E _ ht e σ he hσ
    exact ⟨_, compile_fst_iff.mpr ⟨_, f', a, b, rfl, ht', rfl⟩, rfl, eval_op₂_congr 3 rfl hf⟩
  | snd =>
    obtain ⟨t, f, a, b, rfl, ht, rfl⟩ := compile_snd_iff.mp h
    obtain ⟨⟨f', p⟩, ht', rfl, hf⟩ := ih t (by simp) X E _ ht e σ he hσ
    exact ⟨_, compile_snd_iff.mpr ⟨_, f', a, b, rfl, ht', rfl⟩, rfl, eval_op₂_congr 3 rfl hf⟩
  | lam a =>
    obtain ⟨t, f, b, rfl, hat, ht, rfl⟩ := compile_lam_iff.mp h
    have hA := isObj_of_isTy hM hds.2 hρ a hat
    have fX := fst_hom hM he.1 hA
    -- the lifted substitution compiles, in the extended environment, to the extended values
    have hσ' : SubstEq M ρ G n (prod X a) (extEnv X a e) (Term.liftS σ) (extEnv X a E) := by
      intro i p hp
      rcases i with _ | j
      · obtain rfl : (snd X a, a) = p := by simpa [extEnv] using hp
        exact ⟨(snd X a, a), compile_var_iff.mpr ⟨rfl, rfl⟩, rfl, rfl⟩
      · simp only [extEnv, List.getElem?_cons_succ, List.getElem?_map,
          Option.map_eq_some_iff] at hp
        obtain ⟨p₀, hp₀, rfl⟩ := hp
        obtain ⟨q₀, hq₀, hr₀⟩ := hσ j p₀ hp₀
        obtain ⟨q₁, hq₁, hr₁⟩ :=
          compile_comp hM hG hρ hps hds (σ j) X e q₀ hq₀ he (prod X a) (fst X a) fX
        refine ⟨q₁, compile_rename (σ j) _ _ (precomp (fst X a) e) Nat.succ q₁ hq₁
          fun i _ ↦ ?_, hr₁.1.trans hr₀.1, hr₁.2.trans (eval_op₂_congr 3 hr₀.2 rfl)⟩
        simp [extEnv, precomp]
    obtain ⟨⟨f', b'⟩, ht', rfl, hf⟩ :=
      ih t (by simp) _ _ _ ht _ _ (he.ext hM hA hat) hσ'
    exact ⟨_, compile_lam_iff.mpr ⟨_, f', b', rfl, hat, ht', rfl⟩, rfl,
      eval_op₃_congr 24 rfl rfl hf⟩
  | app =>
    obtain ⟨t, u, rfl, f, a, b, ht, g, hu, rfl⟩ := compile_app_iff.mp h
    obtain ⟨⟨f', p⟩, ht', rfl, hf⟩ := ih t (by simp) X E _ ht e σ he hσ
    obtain ⟨⟨g', a'⟩, hu', rfl, hg⟩ := ih u (by simp) X E _ hu e σ he hσ
    exact ⟨_, compile_app_iff.mpr ⟨_, _, rfl, f', a', b, ht', g', hu', rfl⟩, rfl,
      eval_op₂_congr 3 rfl (eval_op₂_congr 9 hf hg)⟩
  | arr k θ =>
    obtain ⟨t, rfl, p, hp, g, ht, hl, hθ, rfl⟩ := compile_arr_iff.mp h
    obtain ⟨⟨g', d'⟩, ht', rfl, hg⟩ := ih t (by simp) X E _ ht e σ he hσ
    exact ⟨_, compile_arr_iff.mpr ⟨_, rfl, p, hp, g', ht', hl, hθ, rfl⟩, rfl,
      eval_op₂_congr 3 rfl hg⟩
  | natRec =>
    obtain ⟨z, s, m, rfl, z', c, hz, s', hs, m', hm, rfl⟩ := compile_natRec_iff.mp h
    obtain ⟨⟨m'', t⟩, hm', rfl, hmv⟩ := ih m (by simp) X E _ hm e σ he hσ
    exact ⟨_, compile_natRec_iff.mpr ⟨z, s, _, rfl, z', c, hz, s', hs, m'', hm', rfl⟩, rfl,
      eval_op₂_congr 3 rfl hmv⟩
  | listRec =>
    obtain ⟨z, s, m, rfl, m', a, hm, z', c, hz, s', hs, rfl⟩ := compile_listRec_iff.mp h
    obtain ⟨⟨m'', t⟩, hm', rfl, hmv⟩ := ih m (by simp) X E _ hm e σ he hσ
    exact ⟨_, compile_listRec_iff.mpr ⟨z, s, _, rfl, m'', a, hm', z', c, hz, s', hs, rfl⟩, rfl,
      eval_op₂_congr 3 rfl hmv⟩
  | roseRec c =>
    obtain ⟨s, m, m', t, a, F, s', rfl, hc, hm, ht, hs, rfl⟩ := compile_roseRec_iff.mp h
    obtain ⟨⟨m'', t'⟩, hm', rfl, hmv⟩ := ih m (by simp) X E _ hm e σ he hσ
    exact ⟨_, compile_roseRec_iff.mpr ⟨s, _, m'', _, a, F, s', rfl, hc, hm', ht, hs, rfl⟩, rfl,
      eval_op₂_congr 3 rfl hmv⟩
  | eq =>
    obtain ⟨t, u, rfl, f, a, ht, g, hu, rfl⟩ := compile_eq_iff.mp h
    obtain ⟨⟨f', a'⟩, ht', rfl, hf⟩ := ih t (by simp) X E _ ht e σ he hσ
    obtain ⟨⟨g', b'⟩, hu', rfl, hg⟩ := ih u (by simp) X E _ hu e σ he hσ
    exact ⟨_, compile_eq_iff.mpr ⟨_, _, rfl, f', _, ht', g', hu', rfl⟩, rfl,
      eval_op₂_congr 3 rfl (eval_op₂_congr 9 hf hg)⟩
  | defn k θ =>
    obtain ⟨d, rs, hd, hrs, hl, hθ, hty, rfl⟩ := compile_defn_iff.mp h
    obtain ⟨rs', hrs', hR⟩ := mapM_lift (g := fun c ↦ compile G n (Term.subst c σ) X e) cs hrs
      fun c hc r hr ↦ ih c hc X E r hr e σ he hσ
    refine ⟨_, compile_defn_iff.mpr ⟨d, rs', hd, ?_, hl, hθ,
      (map_snd_of_forall₂ hR).trans hty, rfl⟩, rfl,
      eval_op₂_congr 3 rfl (eval_tuple_of_forall₂ X hR)⟩
    rw [List.map_map, List.mapM_map]
    exact hrs'

end Substitution

section Objects

open PartialHorn (Scoped)

/-- The substitution of objects in an arrow and its type. -/
def substPair (θ : List Tree) (p : Tree × Tree) : Tree × Tree :=
  (PartialHorn.subst θ p.1, PartialHorn.subst θ p.2)

/-- A type is in the scope of its object variables. -/
theorem scoped_of_isTy {n : ℕ} : ∀ A : Tree, IsTy G n A = true → Scoped n A = true :=
  RoseTree.ind fun l cs ih hA ↦ by
    rcases l with _ | k
    · rcases cs with _ | ⟨i, _ | ⟨j, cs⟩⟩
      · simp [IsTy] at hA
      rotate_left
      · simp [IsTy] at hA
      exact PartialHorn.scoped_node_zero_iff.mpr (isTy_var_node_iff.mp hA)
    · change IsTy G n (op k cs) = true at hA
      rw [isTy_op, Bool.and_eq_true, List.all_eq_true] at hA
      rw [PartialHorn.scoped_node_succ, List.all_eq_true]
      exact fun c hc ↦ ih c hc (hA.2 c hc)

/-- Results related pointwise by a function are its images. -/
theorem eq_map_of_forall₂ {α : Type} {f : α → α} {rs rs' : List α}
    (h : List.Forall₂ (fun r r' ↦ r' = f r) rs rs') : rs' = rs.map f :=
  h.rec (motive := fun rs rs' _ ↦ rs' = rs.map f) rfl fun hr _ ih ↦ by beta_reduce; rw [hr, ih]; rfl

/-- Substitution in the product of a context's types. -/
theorem subst_ctxObj (θ : List Tree) :
    ∀ Γ : List Tree, PartialHorn.subst θ (ctxObj Γ) = ctxObj (Γ.map (PartialHorn.subst θ)) :=
  List.rec (subst_one θ) fun a Γ ih ↦ by
    rcases Γ with _ | ⟨b, Γ⟩
    · rfl
    · change PartialHorn.subst θ (prod (ctxObj (b :: Γ)) a) =
        prod (ctxObj ((b :: Γ).map (PartialHorn.subst θ))) (PartialHorn.subst θ a)
      rw [subst_prod, ih]

/-- Substitution in an extended environment. -/
theorem map_substPair_extEnv (θ : List Tree) (X a : Tree) (e : List (Tree × Tree)) :
    (extEnv X a e).map (substPair θ) =
      extEnv (PartialHorn.subst θ X) (PartialHorn.subst θ a) (e.map (substPair θ)) := by
  simp [extEnv, substPair, subst_snd, subst_comp, subst_fst]

/-- Substitution in the environment of a context's projections. -/
theorem map_substPair_stdEnv (θ : List Tree) :
    ∀ Γ : List Tree, (stdEnv Γ).map (substPair θ) = stdEnv (Γ.map (PartialHorn.subst θ)) :=
  List.rec rfl fun a Γ ih ↦ by
    rcases Γ with _ | ⟨b, Γ⟩
    · simp [stdEnv, substPair, subst_idt]
    · change (extEnv (ctxObj (b :: Γ)) a (stdEnv (b :: Γ))).map _ =
        extEnv (ctxObj ((b :: Γ).map _)) _ (stdEnv ((b :: Γ).map _))
      rw [map_substPair_extEnv, ih, subst_ctxObj]

/-- Substitution in a tuple. -/
theorem subst_tuple (θ : List Tree) (X : Tree) :
    ∀ fs : List Tree, PartialHorn.subst θ (tuple X fs) =
      tuple (PartialHorn.subst θ X) (fs.map (PartialHorn.subst θ)) :=
  List.rec (subst_bang θ X) fun f fs ih ↦ by
    rcases fs with _ | ⟨g, fs⟩
    · rfl
    · change PartialHorn.subst θ (pair (tuple X (g :: fs)) f) =
        pair (tuple (PartialHorn.subst θ X) ((g :: fs).map (PartialHorn.subst θ)))
          (PartialHorn.subst θ f)
      rw [subst_pair, ih]

/-- The type of labels and the fold of a rose-tree object with objects substituted for its object
variables are its type of labels and its fold with them substituted. -/
theorem roseParts_subst (θ : List Tree) {t a : Tree} {F : Tree → Tree}
    (h : roseParts t = some (a, F)) : ∃ F', roseParts (PartialHorn.subst θ t) =
      some (PartialHorn.subst θ a, F') ∧
        ∀ s, PartialHorn.subst θ (F s) = F' (PartialHorn.subst θ s) := by
  rcases roseParts_eq_some.mp h with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨roseRec, roseParts_eq_some.mpr (.inl ⟨subst_rose θ, subst_nat θ, rfl⟩),
      subst_roseRec θ⟩
  · exact ⟨lroseRec (PartialHorn.subst θ a), by rw [subst_lrose]; exact roseParts_lrose _,
      subst_lroseRec θ a⟩

/-- A term with objects substituted for its object variables compiles, in the substituted
environment, to its arrow and type with them substituted. -/
theorem compile_osubst (hG : G.WF) {m : ℕ} {θ : List Tree} (hl : θ.length = n)
    (hθ : θ.all (IsTy G m) = true) (s : Term) :
    ∀ (X : Tree) (e : List (Tree × Tree)) (r : Tree × Tree), compile G n s X e = some r →
      compile G m (Term.osubst θ s) (PartialHorn.subst θ X) (e.map (substPair θ)) =
        some (substPair θ r) := by
  refine RoseTree.ind (P := fun s ↦ ∀ (X : Tree) (e : List (Tree × Tree)) (r : Tree × Tree),
    compile G n s X e = some r →
      compile G m (Term.osubst θ s) (PartialHorn.subst θ X) (e.map (substPair θ)) =
        some (substPair θ r)) (fun l cs ih ↦ ?_) s
  intro X e r h
  rw [Term.osubst_node]
  have hty := isTy_subst hl hθ
  have hall : ∀ θ' : List Tree, θ'.all (IsTy G n) = true →
      (θ'.map (PartialHorn.subst θ)).all (IsTy G m) = true := fun θ' h' ↦ by
    rw [List.all_map, List.all_eq_true]
    exact fun x hx ↦ hty x (List.all_eq_true.mp h' x hx)
  cases l with
  | var i =>
    obtain ⟨rfl, hi⟩ := compile_var_iff.mp h
    exact compile_var_iff.mpr ⟨rfl, by simp [hi]⟩
  | star =>
    obtain ⟨rfl, rfl⟩ := compile_star_iff.mp h
    exact compile_star_iff.mpr ⟨rfl, by simp [substPair, subst_bang, subst_one]⟩
  | pair =>
    obtain ⟨t, u, f, a, g, b, rfl, ht, hu, rfl⟩ := compile_pair_iff.mp h
    exact compile_pair_iff.mpr ⟨_, _, _, _, _, _, rfl, ih t (by simp) X e _ ht,
      ih u (by simp) X e _ hu, by simp [substPair, subst_pair, subst_prod]⟩
  | fst =>
    obtain ⟨t, f, a, b, rfl, ht, rfl⟩ := compile_fst_iff.mp h
    have h₁ := ih t (by simp) X e _ ht
    simp only [substPair, subst_prod] at h₁
    exact compile_fst_iff.mpr ⟨_, _, _, _, rfl, h₁, by simp [substPair, subst_comp, subst_fst]⟩
  | snd =>
    obtain ⟨t, f, a, b, rfl, ht, rfl⟩ := compile_snd_iff.mp h
    have h₁ := ih t (by simp) X e _ ht
    simp only [substPair, subst_prod] at h₁
    exact compile_snd_iff.mpr ⟨_, _, _, _, rfl, h₁, by simp [substPair, subst_comp, subst_snd]⟩
  | lam a =>
    obtain ⟨t, f, b, rfl, hat, ht, rfl⟩ := compile_lam_iff.mp h
    have h₁ := ih t (by simp) _ _ _ ht
    rw [subst_prod, map_substPair_extEnv] at h₁
    exact compile_lam_iff.mpr ⟨_, _, _, rfl, hty a hat, h₁,
      by simp [substPair, subst_curry, subst_exp]⟩
  | app =>
    obtain ⟨t, u, rfl, f, a, b, ht, g, hu, rfl⟩ := compile_app_iff.mp h
    have h₁ := ih t (by simp) X e _ ht
    simp only [substPair, subst_exp] at h₁
    exact compile_app_iff.mpr ⟨_, _, rfl, _, _, _, h₁, _, ih u (by simp) X e _ hu,
      by simp [substPair, subst_comp, subst_ev, subst_pair]⟩
  | arr k θ' =>
    obtain ⟨t, rfl, p, hp, g, ht, hl', hθ', rfl⟩ := compile_arr_iff.mp h
    obtain ⟨har, hdt, hct⟩ := hG.prims k p hp
    have hsub : ∀ x : Tree, Scoped p.arity x = true →
        PartialHorn.subst θ (PartialHorn.subst θ' x) =
          PartialHorn.subst (θ'.map (PartialHorn.subst θ)) x :=
      fun x hx ↦ subst_subst θ θ' x (hl' ▸ hx)
    have h₁ := ih t (by simp) X e _ ht
    simp only [substPair, hsub _ (scoped_of_isTy _ hdt)] at h₁
    exact compile_arr_iff.mpr ⟨_, rfl, p, hp, _, h₁, by simpa using hl', hall θ' hθ',
      by simp [substPair, subst_comp, hsub _ har, hsub _ (scoped_of_isTy _ hct)]⟩
  | natRec =>
    obtain ⟨z, s, mm, rfl, z', c, hz, s', hs, m', hm, rfl⟩ := compile_natRec_iff.mp h
    have hz₁ := ih z (by simp) _ _ _ hz
    have hs₁ := ih s (by simp) _ _ _ hs
    have hm₁ := ih mm (by simp) X e _ hm
    simp only [substPair, subst_one, List.map_nil, List.map_cons, subst_idt] at hz₁ hs₁
    simp only [substPair, subst_nat] at hm₁
    exact compile_natRec_iff.mpr ⟨_, _, _, rfl, _, _, hz₁, _, hs₁, _, hm₁,
      by simp [substPair, subst_comp, subst_natRec]⟩
  | listRec =>
    obtain ⟨z, s, mm, rfl, m', a, hm, z', c, hz, s', hs, rfl⟩ := compile_listRec_iff.mp h
    have hz₁ := ih z (by simp) _ _ _ hz
    have hs₁ := ih s (by simp) _ _ _ hs
    have hm₁ := ih mm (by simp) X e _ hm
    simp only [substPair, subst_one, List.map_nil, List.map_cons, subst_prod, subst_snd,
      subst_fst] at hz₁ hs₁
    simp only [substPair, subst_list] at hm₁
    exact compile_listRec_iff.mpr ⟨_, _, _, rfl, _, _, hm₁, _, _, hz₁, _, hs₁,
      by simp [substPair, subst_comp, subst_listRec]⟩
  | roseRec c =>
    obtain ⟨s, mm, m', t, a, F, s', rfl, hct, hm, ht, hs, rfl⟩ := compile_roseRec_iff.mp h
    have hs₁ := ih s (by simp) _ _ _ hs
    have hm₁ := ih mm (by simp) X e _ hm
    obtain ⟨F', ht', hF'⟩ := roseParts_subst θ ht
    simp only [substPair, List.map_cons, List.map_nil, subst_idt, subst_prod, subst_list] at hs₁
    simp only [substPair] at hm₁
    exact compile_roseRec_iff.mpr ⟨_, _, _, _, _, _, _, rfl, hty c hct, hm₁, ht', hs₁,
      by simp [substPair, subst_comp, hF']⟩
  | eq =>
    obtain ⟨t, u, rfl, f, a, ht, g, hu, rfl⟩ := compile_eq_iff.mp h
    exact compile_eq_iff.mpr ⟨_, _, rfl, _, _, ih t (by simp) X e (f, a) ht, _,
      ih u (by simp) X e (g, a) hu,
      by simp [substPair, subst_comp, subst_chi, subst_diag, subst_pair, subst_omega]⟩
  | defn k θ' =>
    obtain ⟨d, rs, hd, hrs, hl', hθ', htys, rfl⟩ := compile_defn_iff.mp h
    obtain ⟨hpt, htt⟩ := hG.defs k d hd
    have hsub : ∀ x : Tree, IsTy G d.arity x = true →
        PartialHorn.subst θ (PartialHorn.subst θ' x) =
          PartialHorn.subst (θ'.map (PartialHorn.subst θ)) x :=
      fun x hx ↦ subst_subst θ θ' x (hl' ▸ scoped_of_isTy x hx)
    obtain ⟨rs', hrs', hR⟩ := mapM_lift (R := fun r r' ↦ r' = substPair θ r)
      (g := fun c ↦ compile G m (Term.osubst θ c) (PartialHorn.subst θ X) (e.map (substPair θ)))
      cs hrs fun c hc r hr ↦ ⟨_, ih c hc X e r hr, rfl⟩
    obtain rfl := eq_map_of_forall₂ hR
    refine compile_defn_iff.mpr ⟨d, rs.map (substPair θ), hd, ?_, by simpa using hl',
      hall θ' hθ', ?_, ?_⟩
    · rw [List.mapM_map]
      exact hrs'
    · have hmap := congrArg (List.map (PartialHorn.subst θ)) htys
      simp only [List.map_map] at hmap ⊢
      rw [show (Prod.snd ∘ substPair θ) = PartialHorn.subst θ ∘ Prod.snd from rfl, hmap]
      exact List.map_congr_left fun x hx ↦ hsub x (List.all_eq_true.mp hpt x hx)
    · simp only [substPair, subst_comp, subst_op, subst_tuple, List.map_map, hsub _ htt]
      rfl

end Objects

end Geb.FreeTopos.Internal

end
