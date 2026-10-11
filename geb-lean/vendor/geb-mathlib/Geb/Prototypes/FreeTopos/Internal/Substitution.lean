/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
-- Modified from geb-mathlib by scripts/geb-mathlib-backport.patch.
module

public import Geb.Prototypes.FreeTopos.Internal.Semantics
public import Geb.Prototypes.FreeTopos.Internal.SyntaxLaws

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

/-- Environments related by a renaming at their indices, each extended by a variable, are related
by the renaming lifted under it. -/
theorem extEnv_rename {X a : Tree} {e e' : List (Tree × Tree)} {f : ℕ → ℕ}
    (hf : ∀ i < e'.length, e[f i]? = e'[i]?) :
    ∀ i < (extEnv X a e').length, (extEnv X a e)[Term.liftR f i]? = (extEnv X a e')[i]? := by
  intro i hi
  rcases i with _ | j
  · rfl
  · have hj : j < e'.length := by simpa [extEnv] using hi
    simp only [extEnv, Term.liftR, List.getElem?_cons_succ, List.getElem?_map, hf j hj]

/-- A term renamed by a strictly increasing map compiles in an environment whose variables at the
renamed indices are the term's environment's: renaming is the renamed environment. -/
theorem compile_rename (s : Term) :
    ∀ (X : Tree) (e e' : List (Tree × Tree)) (f : ℕ → ℕ) (r : Tree × Tree),
      compile G n s X e' = some r → (∀ i < e'.length, e[f i]? = e'[i]?) → StrictMono f →
      compile G n (Term.rename s f) X e = some r := by
  refine RoseTree.ind (P := fun s ↦ ∀ (X : Tree) (e e' : List (Tree × Tree)) (f : ℕ → ℕ)
    (r : Tree × Tree), compile G n s X e' = some r → (∀ i < e'.length, e[f i]? = e'[i]?) →
      StrictMono f → compile G n (Term.rename s f) X e = some r) (fun l cs ih ↦ ?_) s
  intro X e e' f r h hf hmono
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
    exact compile_pair_iff.mpr ⟨_, _, g, a, g', b, rfl, ih t (by simp) X e e' f _ ht hf hmono,
      ih u (by simp) X e e' f _ hu hf hmono, rfl⟩
  | fst =>
    obtain ⟨t, g, a, b, rfl, ht, rfl⟩ := compile_fst_iff.mp h
    exact compile_fst_iff.mpr ⟨_, g, a, b, rfl, ih t (by simp) X e e' f _ ht hf hmono, rfl⟩
  | snd =>
    obtain ⟨t, g, a, b, rfl, ht, rfl⟩ := compile_snd_iff.mp h
    exact compile_snd_iff.mpr ⟨_, g, a, b, rfl, ih t (by simp) X e e' f _ ht hf hmono, rfl⟩
  | lam a =>
    obtain ⟨t, g, b, rfl, hat, ht, rfl⟩ := compile_lam_iff.mp h
    exact compile_lam_iff.mpr ⟨_, g, b, rfl, hat,
      ih t (by simp) _ (extEnv X a e) (extEnv X a e') (Term.liftR f) _ ht (extEnv_rename hf)
        (strictMono_liftR hmono), rfl⟩
  | app =>
    obtain ⟨t, u, rfl, g, a, b, ht, g', hu, rfl⟩ := compile_app_iff.mp h
    exact compile_app_iff.mpr ⟨_, _, rfl, g, a, b, ih t (by simp) X e e' f _ ht hf hmono, g',
      ih u (by simp) X e e' f _ hu hf hmono, rfl⟩
  | arr k θ =>
    obtain ⟨t, rfl, p, hp, g, ht, hl, hθ, rfl⟩ := compile_arr_iff.mp h
    exact compile_arr_iff.mpr ⟨_, rfl, p, hp, g, ih t (by simp) X e e' f _ ht hf hmono, hl, hθ, rfl⟩
  | natRec =>
    obtain ⟨z, s, m, rfl, z', c, hz, s', hs, m', hm, rfl⟩ := compile_natRec_iff.mp h
    obtain ⟨hV, hT⟩ := foldParams_rename (k := 1) h (fun i hi ↦ by
        simp only [Term.occurs_node, Term.occursStep, List.map_cons, List.map_nil,
          Bool.or_eq_true] at hi ⊢
        exact .inl hi) hf hmono (Term.rename z f) (Term.rename s (Term.liftR f)) fun j ↦ by
      simp only [Bool.or_eq_true, Term.occurs_rename,
        Term.exists_liftR (fun i ↦ Term.occurs s i = true) f j, or_and_right, exists_or]
    obtain ⟨hP₀, hE₀⟩ := foldEnvIn_rename (bs := []) hmono hV (congrArg _ hT) (by simp)
    obtain ⟨hP₁, hE₁⟩ := foldEnvIn_rename (bs := [c]) (strictMono_liftR hmono) hV
      (congrArg _ hT) (by simp [Term.liftR, Function.comp_def])
    exact compile_natRec_iff.mpr ⟨_, _, _, rfl, z', c,
      hP₀ ▸ ih z (by simp) _ _ _ f _ hz hE₀ hmono, s',
      hP₁ ▸ ih s (by simp) _ _ _ _ _ hs hE₁ (strictMono_liftR hmono), m',
      ih m (by simp) X e e' f _ hm hf hmono, by rw [hT]⟩
  | listRec =>
    obtain ⟨z, s, m, rfl, m', a, hm, z', c, hz, s', hs, rfl⟩ := compile_listRec_iff.mp h
    obtain ⟨hV, hT⟩ := foldParams_rename (k := 2) h (fun i hi ↦ by
        simp only [Term.occurs_node, Term.occursStep, List.map_cons, List.map_nil,
          Bool.or_eq_true] at hi ⊢
        exact .inl hi) hf hmono (Term.rename z f)
      (Term.rename s (Term.liftR (Term.liftR f))) fun j ↦ by
      have hs₂ : (∃ i, Term.occurs s i = true ∧ Term.liftR (Term.liftR f) i = j + 2) ↔
          ∃ i, Term.occurs s (i + 2) = true ∧ f i = j :=
        (Term.exists_liftR _ _ (j + 1)).trans
          (Term.exists_liftR (fun i ↦ Term.occurs s (i + 1) = true) f j)
      simp only [Bool.or_eq_true, Term.occurs_rename, hs₂, or_and_right, exists_or]
    obtain ⟨hP₀, hE₀⟩ := foldEnvIn_rename (bs := []) hmono hV (congrArg _ hT) (by simp)
    obtain ⟨hP₁, hE₁⟩ := foldEnvIn_rename (bs := [c, a])
      (strictMono_liftR (strictMono_liftR hmono)) hV (congrArg _ hT)
      (by simp [Term.liftR, Function.comp_def, List.range_succ])
    exact compile_listRec_iff.mpr ⟨_, _, _, rfl, m', a, ih m (by simp) X e e' f _ hm hf hmono,
      z', c, hP₀ ▸ ih z (by simp) _ _ _ f _ hz hE₀ hmono, s',
      hP₁ ▸ ih s (by simp) _ _ _ _ _ hs hE₁ (strictMono_liftR (strictMono_liftR hmono)),
      by rw [hT]⟩
  | roseRec c =>
    obtain ⟨s, m, m', t, a, F, s', rfl, hc, hm, ht, hs, rfl⟩ := compile_roseRec_iff.mp h
    obtain ⟨hV, hT⟩ := foldParams_rename_of_lt (k := 1)
      (fun i hi ↦ compile_occurs_lt _ X e' _ h i (occurs_roseRec_of_step hi)) hf hmono
      Term.star (Term.rename s (Term.liftR f)) fun j ↦ by
        simp only [occurs_star, Bool.false_or, Term.occurs_rename,
          Term.exists_liftR (fun i ↦ Term.occurs s i = true) f j]
    obtain ⟨hP₁, hE₁⟩ := foldEnvIn_rename (bs := [prod a (list c)]) (strictMono_liftR hmono) hV
      (congrArg _ hT) (by simp [Term.liftR, Function.comp_def])
    exact compile_roseRec_iff.mpr ⟨_, _, m', t, a, F, s', rfl, hc,
      ih m (by simp) X e e' f _ hm hf hmono, ht,
      hP₁ ▸ ih s (by simp) _ _ _ _ _ hs hE₁ (strictMono_liftR hmono), by rw [hT]⟩
  | eq =>
    obtain ⟨t, u, rfl, f₁, a, ht, g, hu, rfl⟩ := compile_eq_iff.mp h
    exact compile_eq_iff.mpr ⟨_, _, rfl, f₁, a, ih t (by simp) X e e' f _ ht hf hmono, g,
      ih u (by simp) X e e' f _ hu hf hmono, rfl⟩
  | defn k θ =>
    obtain ⟨d, rs, hd, hrs, hl, hθ, hty, rfl⟩ := compile_defn_iff.mp h
    obtain ⟨rs', h₁, h₂⟩ := mapM_lift (R := Eq)
      (g := fun c ↦ compile G n (Term.rename c f) X e) cs hrs
      fun c hc r hr ↦ ⟨r, ih c hc X e e' f r hr hf hmono, rfl⟩
    rw [List.forall₂_eq_eq_eq] at h₂
    subst h₂
    refine compile_defn_iff.mpr ⟨d, rs, hd, ?_, hl, hθ, hty, rfl⟩
    rw [List.map_map, List.mapM_map]
    exact h₁

/-- A term's type depends on the types of the variables it mentions alone: in an environment of
the same types at them, over any object, it compiles to the same type. -/
theorem compile_retype_on (s : Term) :
    ∀ (X : Tree) (e : List (Tree × Tree)) (r : Tree × Tree), compile G n s X e = some r →
      ∀ (X' : Tree) (e' : List (Tree × Tree)),
        (∀ i, Term.occurs s i = true → (e'[i]?).map Prod.snd = (e[i]?).map Prod.snd) →
        ∃ f, compile G n s X' e' = some (f, r.2) := by
  refine RoseTree.ind (P := fun s ↦ ∀ (X : Tree) (e : List (Tree × Tree)) (r : Tree × Tree),
    compile G n s X e = some r → ∀ (X' : Tree) (e' : List (Tree × Tree)),
      (∀ i, Term.occurs s i = true → (e'[i]?).map Prod.snd = (e[i]?).map Prod.snd) →
      ∃ f, compile G n s X' e' = some (f, r.2))
    (fun l cs ih ↦ ?_) s
  intro X e r h X' e' he
  -- a child the node's variables include the variables of
  have sub : ∀ c ∈ cs, (∀ i, Term.occurs c i = true →
      Term.occurs (RoseTree.node l cs) i = true) → ∀ r, compile G n c X e = some r →
      ∃ f, compile G n c X' e' = some (f, r.2) :=
    fun c hc hsub r hr ↦ ih c hc X e r hr X' e' fun i hi ↦ he i (hsub i hi)
  cases l with
  | var i =>
    obtain ⟨rfl, hi⟩ := compile_var_iff.mp h
    have hm := he i (by simp [Term.occurs_node, Term.occursStep])
    simp only [hi, Option.map_some, Option.map_eq_some_iff] at hm
    obtain ⟨q, hq, hq₂⟩ := hm
    exact ⟨q.1, compile_var_iff.mpr ⟨rfl, by rw [hq, ← hq₂]⟩⟩
  | star =>
    obtain ⟨rfl, rfl⟩ := compile_star_iff.mp h
    exact ⟨_, compile_star_iff.mpr ⟨rfl, rfl⟩⟩
  | pair =>
    obtain ⟨t, u, f, a, g, b, rfl, ht, hu, rfl⟩ := compile_pair_iff.mp h
    obtain ⟨f', hf'⟩ :=
      sub t (by simp) (fun i hi ↦ by simp [Term.occurs_node, Term.occursStep, hi]) _ ht
    obtain ⟨g', hg'⟩ :=
      sub u (by simp) (fun i hi ↦ by simp [Term.occurs_node, Term.occursStep, hi]) _ hu
    exact ⟨_, compile_pair_iff.mpr ⟨t, u, f', a, g', b, rfl, hf', hg', rfl⟩⟩
  | fst =>
    obtain ⟨t, f, a, b, rfl, ht, rfl⟩ := compile_fst_iff.mp h
    obtain ⟨f', hf'⟩ :=
      sub t (by simp) (fun i hi ↦ by simp [Term.occurs_node, Term.occursStep, hi]) _ ht
    exact ⟨_, compile_fst_iff.mpr ⟨t, f', a, b, rfl, hf', rfl⟩⟩
  | snd =>
    obtain ⟨t, f, a, b, rfl, ht, rfl⟩ := compile_snd_iff.mp h
    obtain ⟨f', hf'⟩ :=
      sub t (by simp) (fun i hi ↦ by simp [Term.occurs_node, Term.occursStep, hi]) _ ht
    exact ⟨_, compile_snd_iff.mpr ⟨t, f', a, b, rfl, hf', rfl⟩⟩
  | lam a =>
    obtain ⟨t, f, b, rfl, hat, ht, rfl⟩ := compile_lam_iff.mp h
    obtain ⟨f', hf'⟩ := ih t (by simp) _ _ _ ht (prod X' a) (extEnv X' a e') fun i hi ↦ by
      rcases i with _ | j
      · rfl
      · simpa [extEnv, Option.map_map, Function.comp_def] using
          he j (by simpa [Term.occurs_node, Term.occursStep] using hi)
    exact ⟨_, compile_lam_iff.mpr ⟨t, f', b, rfl, hat, hf', rfl⟩⟩
  | app =>
    obtain ⟨t, u, rfl, f, a, b, ht, g, hu, rfl⟩ := compile_app_iff.mp h
    obtain ⟨f', hf'⟩ :=
      sub t (by simp) (fun i hi ↦ by simp [Term.occurs_node, Term.occursStep, hi]) _ ht
    obtain ⟨g', hg'⟩ :=
      sub u (by simp) (fun i hi ↦ by simp [Term.occurs_node, Term.occursStep, hi]) _ hu
    exact ⟨_, compile_app_iff.mpr ⟨t, u, rfl, f', a, b, hf', g', hg', rfl⟩⟩
  | arr k θ =>
    obtain ⟨t, rfl, p, hp, g, ht, hl, hθ, rfl⟩ := compile_arr_iff.mp h
    obtain ⟨g', hg'⟩ :=
      sub t (by simp) (fun i hi ↦ by simp [Term.occurs_node, Term.occursStep, hi]) _ ht
    exact ⟨_, compile_arr_iff.mpr ⟨t, rfl, p, hp, g', hg', hl, hθ, rfl⟩⟩
  | natRec =>
    obtain ⟨z, s, m, rfl, z', c, hz, s', hs, m', hm, rfl⟩ := compile_natRec_iff.mp h
    have hE := foldEnvIn_retype (k := 1) (z := z) (s := s)
      (fun i hi ↦ compile_occurs_lt _ X e _ h i (by
        simp only [Term.occurs_node, Term.occursStep, List.map_cons, List.map_nil,
          Bool.or_eq_true] at hi ⊢
        exact .inl hi))
      fun i hi ↦ he i (by
        simp only [Term.occurs_node, Term.occursStep, List.map_cons, List.map_nil,
          Bool.or_eq_true] at hi ⊢
        exact .inl hi)
    obtain ⟨m'', hm''⟩ :=
      sub m (by simp) (fun i hi ↦ by simp [Term.occurs_node, Term.occursStep, hi]) _ hm
    exact ⟨_, compile_natRec_iff.mpr ⟨z, s, m, rfl, z', c, (hE []).symm ▸ hz, s',
      (hE [c]).symm ▸ hs, m'', hm'', rfl⟩⟩
  | listRec =>
    obtain ⟨z, s, m, rfl, m', a, hm, z', c, hz, s', hs, rfl⟩ := compile_listRec_iff.mp h
    have hE := foldEnvIn_retype (k := 2) (z := z) (s := s)
      (fun i hi ↦ compile_occurs_lt _ X e _ h i (by
        simp only [Term.occurs_node, Term.occursStep, List.map_cons, List.map_nil,
          Bool.or_eq_true] at hi ⊢
        exact .inl hi))
      fun i hi ↦ he i (by
        simp only [Term.occurs_node, Term.occursStep, List.map_cons, List.map_nil,
          Bool.or_eq_true] at hi ⊢
        exact .inl hi)
    obtain ⟨m'', hm''⟩ :=
      sub m (by simp) (fun i hi ↦ by simp [Term.occurs_node, Term.occursStep, hi]) _ hm
    exact ⟨_, compile_listRec_iff.mpr ⟨z, s, m, rfl, m'', a, hm'', z', c, (hE []).symm ▸ hz, s',
      (hE [c, a]).symm ▸ hs, rfl⟩⟩
  | roseRec c =>
    obtain ⟨s, m, m', t, a, F, s', rfl, hc, hm, ht, hs, rfl⟩ := compile_roseRec_iff.mp h
    have hE := foldEnvIn_retype (k := 1) (z := Term.star) (s := s)
      (fun i hi ↦ compile_occurs_lt _ X e _ h i (occurs_roseRec_of_step hi))
      fun i hi ↦ he i (occurs_roseRec_of_step hi)
    obtain ⟨m'', hm''⟩ :=
      sub m (by simp) (fun i hi ↦ by simp [Term.occurs_node, Term.occursStep, hi]) _ hm
    exact ⟨_, compile_roseRec_iff.mpr ⟨s, m, m'', t, a, F, s', rfl, hc, hm'', ht,
      (hE _).symm ▸ hs, rfl⟩⟩
  | eq =>
    obtain ⟨t, u, rfl, f, a, ht, g, hu, rfl⟩ := compile_eq_iff.mp h
    obtain ⟨f', hf'⟩ :=
      sub t (by simp) (fun i hi ↦ by simp [Term.occurs_node, Term.occursStep, hi]) _ ht
    obtain ⟨g', hg'⟩ :=
      sub u (by simp) (fun i hi ↦ by simp [Term.occurs_node, Term.occursStep, hi]) _ hu
    exact ⟨_, compile_eq_iff.mpr ⟨t, u, rfl, f', a, hf', g', hg', rfl⟩⟩
  | defn k θ =>
    obtain ⟨d, rs, hd, hrs, hl, hθ, hty, rfl⟩ := compile_defn_iff.mp h
    obtain ⟨rs', hrs', hR⟩ := mapM_lift (R := fun r r' ↦ r'.2 = r.2)
      (g := fun c ↦ compile G n c X' e') cs hrs fun c hc r hr ↦ by
        obtain ⟨f, hf⟩ := sub c hc (fun i hi ↦ by
          simp only [Term.occurs_node, Term.occursStep, List.any_map, List.any_eq_true,
            Function.comp_apply]
          exact ⟨c, hc, hi⟩) r hr
        exact ⟨(f, r.2), hf, rfl⟩
    have hsnd : rs'.map Prod.snd = rs.map Prod.snd :=
      hR.rec (motive := fun rs rs' _ ↦ rs'.map Prod.snd = rs.map Prod.snd) rfl
        fun hr _ ih ↦ by simp [hr, ih]
    exact ⟨_, compile_defn_iff.mpr ⟨d, rs', hd, hrs', hl, hθ, hsnd.trans hty, rfl⟩⟩

/-- A term's type depends on its environment's types alone: in an environment of the same types,
over any object, it compiles to the same type. -/
theorem compile_retype (s : Term) (X : Tree) (e : List (Tree × Tree)) (r : Tree × Tree)
    (h : compile G n s X e = some r) (X' : Tree) (e' : List (Tree × Tree))
    (he : e'.map Prod.snd = e.map Prod.snd) : ∃ f, compile G n s X' e' = some (f, r.2) :=
  compile_retype_on s X e r h X' e' fun i _ ↦ by rw [← List.getElem?_map, ← List.getElem?_map, he]

/-- A fold of the natural numbers that compiles has its start compiled in the environment, and
its step in the environment extended by the value, to the fold's type, and its datum compiled in
the environment. -/
theorem compile_natRec_parts {z s m : Term} {X : Tree} {e : List (Tree × Tree)}
    {r : Tree × Tree} (h : compile G n (Term.natRec z s m) X e = some r) :
    (∃ zf, compile G n z X e = some (zf, r.2)) ∧
      (∃ sf, compile G n s (prod X r.2) (extEnv X r.2 e) = some (sf, r.2)) ∧
      ∃ mf, compile G n m X e = some (mf, nat) := by
  obtain ⟨z₀, s₀, m₀, hcs, z', c, hz, s', hs, m', hm, rfl⟩ := compile_natRec_iff.mp h
  obtain ⟨rfl, rfl, rfl⟩ : z = z₀ ∧ s = s₀ ∧ m = m₀ := by simpa [Term.natRec] using hcs
  -- the parameters are the variables of the environment the start or the step mentions
  have hP : ∀ i, (Term.occurs z i || Term.occurs s (i + 1)) = true →
      i ∈ foldParams 1 e.length z s := fun i hi ↦ mem_foldParams.mpr
    ⟨compile_occurs_lt _ X e _ h i (by
      simp only [Term.natRec, Term.occurs_node, Term.occursStep, List.map_cons, List.map_nil,
        Bool.or_eq_true] at hi ⊢
      exact .inl hi), hi⟩
  refine ⟨compile_retype_on z _ _ _ hz X e fun i hi ↦ (foldEnvIn_types (foldWs_start_lt 1 e z s)
      (foldWs_start_filterMap 1 e z s) (by simp) i (by simpa using hP i (by simp [hi]))).symm,
    compile_retype_on s _ _ _ hs (prod X c) (extEnv X c e) fun i hi ↦ (foldEnvIn_types
      (foldWs_nat_lt X c e z s) (foldWs_nat_filterMap X c e z s) (by simp [extEnv]) i (by
        rcases i with _ | i
        · simp
        · simpa using hP i (by simp [hi]))).symm, m', hm⟩

/-- A fold of a list whose datum compiles in the environment to a list type, whose start compiles
in the environment and whose step compiles in the environment extended by the element and the
value, both to one type, compiles, to that type. -/
theorem compile_listRec_of_parts {z s m : Term} {X mf a zf c sf : Tree} {e : List (Tree × Tree)}
    (hm : compile G n m X e = some (mf, list a)) (hz : compile G n z X e = some (zf, c))
    (hs : compile G n s (prod (prod X a) c) (extEnv (prod X a) c (extEnv X a e)) =
      some (sf, c)) :
    ∃ r, compile G n (Term.listRec z s m) X e = some r ∧ r.2 = c := by
  -- the variables the start and the step mention are the fold's parameters
  have hP : ∀ i, (Term.occurs z i || Term.occurs s (i + 2)) = true →
      i ∈ foldParams 2 e.length z s := fun i hi ↦ by
    refine mem_foldParams.mpr ⟨?_, hi⟩
    rcases Bool.or_eq_true _ _ ▸ hi with hi | hi
    · exact compile_occurs_lt z X e _ hz i hi
    · simpa [extEnv] using compile_occurs_lt s _ _ _ hs (i + 2) hi
  obtain ⟨z', hz'⟩ := compile_retype_on z X e _ hz (foldEnvIn [] 2 e z s).1
    (foldEnvIn [] 2 e z s).2 fun i hi ↦ foldEnvIn_types (foldWs_start_lt 2 e z s)
      (foldWs_start_filterMap 2 e z s) (by simp) i (by simpa using hP i (by simp [hi]))
  obtain ⟨s', hs'⟩ := compile_retype_on s _ _ _ hs (foldEnvIn [c, a] 2 e z s).1
    (foldEnvIn [c, a] 2 e z s).2 fun i hi ↦ foldEnvIn_types (foldWs_list_lt X a c e z s)
      (foldWs_list_filterMap X a c e z s) (by simp [extEnv]) i (by
        rcases i with _ | _ | i
        · exact List.mem_append_left _ (List.mem_range.mpr (by simp))
        · exact List.mem_append_left _ (List.mem_range.mpr (by simp))
        · exact List.mem_append_right _ (List.mem_map.mpr ⟨i, hP i (by simp [hi]), rfl⟩))
  have hnode : compile G n (Term.listRec z s m) X e = some _ :=
    compile_listRec_iff.mpr ⟨z, s, m, rfl, mf, a, hm, z', c, hz', s', hs', rfl⟩
  exact ⟨_, hnode, rfl⟩

/-- A fold of the natural numbers whose start compiles in the environment, whose step compiles
in the environment extended by the value, both to one type, and whose datum compiles in the
environment to the natural numbers compiles, to that type. -/
theorem compile_natRec_of_parts {z s m : Term} {X zf c sf mf : Tree} {e : List (Tree × Tree)}
    (hz : compile G n z X e = some (zf, c))
    (hs : compile G n s (prod X c) (extEnv X c e) = some (sf, c))
    (hm : compile G n m X e = some (mf, nat)) :
    ∃ r, compile G n (Term.natRec z s m) X e = some r ∧ r.2 = c := by
  -- the variables the start and the step mention are the fold's parameters
  have hP : ∀ i, (Term.occurs z i || Term.occurs s (i + 1)) = true →
      i ∈ foldParams 1 e.length z s := fun i hi ↦ by
    refine mem_foldParams.mpr ⟨?_, hi⟩
    rcases Bool.or_eq_true _ _ ▸ hi with hi | hi
    · exact compile_occurs_lt z X e _ hz i hi
    · simpa [extEnv] using compile_occurs_lt s _ _ _ hs (i + 1) hi
  obtain ⟨z', hz'⟩ := compile_retype_on z X e _ hz (foldEnvIn [] 1 e z s).1
    (foldEnvIn [] 1 e z s).2 fun i hi ↦ foldEnvIn_types (foldWs_start_lt 1 e z s)
      (foldWs_start_filterMap 1 e z s) (by simp) i (by simpa using hP i (by simp [hi]))
  obtain ⟨s', hs'⟩ := compile_retype_on s _ _ _ hs (foldEnvIn [c] 1 e z s).1
    (foldEnvIn [c] 1 e z s).2 fun i hi ↦ foldEnvIn_types (foldWs_nat_lt X c e z s)
      (foldWs_nat_filterMap X c e z s) (by simp [extEnv]) i (by
        rcases i with _ | i
        · simp
        · simpa using hP i (by simp [hi]))
  have hnode : compile G n (Term.natRec z s m) X e = some _ :=
    compile_natRec_iff.mpr ⟨z, s, m, rfl, z', c, hz', s', hs', mf, hm, rfl⟩
  exact ⟨_, hnode, rfl⟩

/-- A fold of a list that compiles has its datum compiled in the environment, to a list type, its
start in the environment, and its step in the environment extended by the element and the value,
to the fold's type. -/
theorem compile_listRec_parts {z s m : Term} {X : Tree} {e : List (Tree × Tree)}
    {r : Tree × Tree} (h : compile G n (Term.listRec z s m) X e = some r) :
    ∃ mf a, compile G n m X e = some (mf, list a) ∧ (∃ zf, compile G n z X e = some (zf, r.2)) ∧
      ∃ sf, compile G n s (prod (prod X a) r.2) (extEnv (prod X a) r.2 (extEnv X a e)) =
        some (sf, r.2) := by
  obtain ⟨z₀, s₀, m₀, hcs, m', a, hm, z', c, hz, s', hs, rfl⟩ := compile_listRec_iff.mp h
  obtain ⟨rfl, rfl, rfl⟩ : z = z₀ ∧ s = s₀ ∧ m = m₀ := by simpa [Term.listRec] using hcs
  -- the parameters are the variables of the environment the start or the step mentions
  have hP : ∀ i, (Term.occurs z i || Term.occurs s (i + 2)) = true →
      i ∈ foldParams 2 e.length z s := fun i hi ↦ mem_foldParams.mpr
    ⟨compile_occurs_lt _ X e _ h i (by
      simp only [Term.listRec, Term.occurs_node, Term.occursStep, List.map_cons, List.map_nil,
        Bool.or_eq_true] at hi ⊢
      exact .inl hi), hi⟩
  refine ⟨m', a, hm, compile_retype_on z _ _ _ hz X e fun i hi ↦ (foldEnvIn_types
      (foldWs_start_lt 2 e z s) (foldWs_start_filterMap 2 e z s) (by simp) i
      (by simpa using hP i (by simp [hi]))).symm,
    compile_retype_on s _ _ _ hs _ _ fun i hi ↦ (foldEnvIn_types (foldWs_list_lt X a c e z s)
      (foldWs_list_filterMap X a c e z s) (by simp [extEnv]) i (by
        rcases i with _ | _ | i
        · exact List.mem_append_left _ (List.mem_range.mpr (by simp))
        · exact List.mem_append_left _ (List.mem_range.mpr (by simp))
        · exact List.mem_append_right _ (List.mem_map.mpr ⟨i, hP i (by simp [hi]), rfl⟩))).symm⟩

/-- A fold of a rose tree that compiles has its annotation a type and the fold's type, its datum
compiled in the environment to a rose-tree object, and its step compiled in the environment
extended by the pair of a label and the list of the children's values, to the fold's type. -/
theorem compile_roseRec_parts {c : Tree} {s m : Term} {X : Tree} {e : List (Tree × Tree)}
    {r : Tree × Tree} (h : compile G n (Term.roseRec c s m) X e = some r) :
    IsTy G n c = true ∧ r.2 = c ∧ ∃ mf t a F, compile G n m X e = some (mf, t) ∧
      roseParts t = some (a, F) ∧ ∃ sf, compile G n s (prod X (prod a (list c)))
        (extEnv X (prod a (list c)) e) = some (sf, c) := by
  obtain ⟨s₀, m₀, m', t, a, F, s', hcs, hct, hm, ht, hs, rfl⟩ := compile_roseRec_iff.mp h
  obtain ⟨rfl, rfl⟩ : s = s₀ ∧ m = m₀ := by simpa [Term.roseRec] using hcs
  -- the parameters are the variables of the environment the step mentions
  have hP : ∀ i, (Term.occurs Term.star i || Term.occurs s (i + 1)) = true →
      i ∈ foldParams 1 e.length Term.star s := fun i hi ↦
    mem_foldParams.mpr ⟨compile_occurs_lt _ X e _ h i (occurs_roseRec_of_step hi), hi⟩
  exact ⟨hct, rfl, m', t, a, F, hm, ht, compile_retype_on s _ _ _ hs _ _ fun i hi ↦
    (foldEnvIn_types (foldWs_nat_lt X _ e Term.star s) (foldWs_nat_filterMap X _ e Term.star s)
      (by simp [extEnv]) i (by
        rcases i with _ | i
        · simp
        · simpa using hP i (by simp [occurs_star, hi]))).symm⟩

/-- A fold of a rose tree whose annotation is a type, whose datum compiles in the environment to a
rose-tree object and whose step compiles in the environment extended by the pair of a label and
the list of the children's values, to the annotation, compiles, to the annotation. -/
theorem compile_roseRec_of_parts {c : Tree} {s m : Term} {X mf t a sf : Tree}
    {F : Tree → Tree} {e : List (Tree × Tree)} (hct : IsTy G n c = true)
    (hm : compile G n m X e = some (mf, t)) (ht : roseParts t = some (a, F))
    (hs : compile G n s (prod X (prod a (list c))) (extEnv X (prod a (list c)) e) =
      some (sf, c)) :
    ∃ r, compile G n (Term.roseRec c s m) X e = some r ∧ r.2 = c := by
  -- the variables the step mentions are the fold's parameters
  have hP : ∀ i, (Term.occurs Term.star i || Term.occurs s (i + 1)) = true →
      i ∈ foldParams 1 e.length Term.star s := fun i hi ↦ by
    refine mem_foldParams.mpr ⟨?_, hi⟩
    simp only [occurs_star, Bool.false_or] at hi
    simpa [extEnv] using compile_occurs_lt s _ _ _ hs (i + 1) hi
  obtain ⟨s', hs'⟩ := compile_retype_on s _ _ _ hs (foldEnvIn [prod a (list c)] 1 e Term.star s).1
    (foldEnvIn [prod a (list c)] 1 e Term.star s).2 fun i hi ↦
      foldEnvIn_types (foldWs_nat_lt X _ e Term.star s) (foldWs_nat_filterMap X _ e Term.star s)
        (by simp [extEnv]) i (by
          rcases i with _ | i
          · simp
          · simpa using hP i (by simp [occurs_star, hi]))
  exact ⟨_, compile_roseRec_iff.mpr ⟨s, m, mf, t, a, F, s', rfl, hct, hm, ht, hs', rfl⟩, rfl⟩

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

/-- An environment's entries at increasing indices of it are, at those indices, the values of
the environment over the product of their types whose variables there are its projections, after
the tuple of the entries. -/
theorem selEnv_envEqOn (hO : ObjsHom M G) (hρ : ρ.map Sigma.fst = List.replicate n obj)
    {X : Tree} {E : List (Tree × Tree)} (he : EnvHom M ρ G n X E) {ws : List ℕ}
    (hw : ws.Pairwise (· < ·)) (hlt : ∀ w ∈ ws, w < E.length) :
    EnvEqOn M ρ (· ∈ ws) (precomp (tuple X ((ws.filterMap fun w : ℕ ↦ E[w]?).map Prod.fst))
      (selEnv ws (ctxObj ((ws.filterMap fun w : ℕ ↦ E[w]?).map Prod.snd))
        (stdEnv ((ws.filterMap fun w : ℕ ↦ E[w]?).map Prod.snd)))) E := by
  intro i p hi hp
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hi
  have hqj : (ws.filterMap fun w : ℕ ↦ E[w]?)[j]? = E[ws[j]]? := by
    rw [getElem?_filterMap_getElem? ws hlt j, List.getElem?_eq_getElem hj, Option.bind_some]
  have hqs : ∀ q ∈ ws.filterMap (fun w : ℕ ↦ E[w]?), Hom M ρ q.1 X q.2 ∧ IsTy G n q.2 = true :=
    fun q hq ↦ by
      obtain ⟨v, -, hv⟩ := List.mem_filterMap.mp hq
      exact he.2 q (List.mem_of_getElem? hv)
  obtain ⟨p₀, hp₀⟩ : ∃ p₀, (stdEnv ((ws.filterMap fun w : ℕ ↦ E[w]?).map Prod.snd))[j]? =
      some p₀ := by
    have h₁ := congrArg (·[j]?) (map_snd_stdEnv ((ws.filterMap fun w : ℕ ↦ E[w]?).map Prod.snd))
    simp only [List.getElem?_map, hqj,
      List.getElem?_eq_getElem (hlt _ (List.getElem_mem hj)), Option.map_some] at h₁
    obtain ⟨p₀, hp₀, -⟩ := Option.map_eq_some_iff.mp h₁
    exact ⟨p₀, hp₀⟩
  simp only [precomp, List.getElem?_map, getElem?_selEnv_of_mem hw _ _ hj, hp₀,
    Option.getD_some, Option.map_some, Option.some.injEq] at hp
  subst hp
  obtain ⟨q, hq, hr⟩ := proj_tuple hM hO hρ he.1 _ hqs j
    (comp p₀.1 (tuple X ((ws.filterMap fun w : ℕ ↦ E[w]?).map Prod.fst)), p₀.2)
    (by simp [precomp, hp₀])
  exact ⟨q, hqj ▸ hq, hr⟩

/-- The environment of a fold's start or step, after the tuple of the entries of an environment
at its indices, has those entries' values at its indices, when the entries' types are the bound
types before the parameters' types. -/
theorem foldEnvIn_envEqOn (hO : ObjsHom M G) (hρ : ρ.map Sigma.fst = List.replicate n obj)
    {Y : Tree} {E : List (Tree × Tree)} (hE : EnvHom M ρ G n Y E) {bs : List Tree} {k : ℕ}
    {e : List (Tree × Tree)} {z s : Term} {Q : List (Tree × Tree)}
    (hlt : ∀ w ∈ List.range bs.length ++ (foldParams k e.length z s).map (· + bs.length),
      w < E.length)
    (hQ : (List.range bs.length ++ (foldParams k e.length z s).map (· + bs.length)).filterMap
      (fun w : ℕ ↦ E[w]?) = Q)
    (hT : Q.map Prod.snd = bs ++ (foldPs k e z s).map Prod.snd) :
    EnvEqOn M ρ (· ∈ List.range bs.length ++ (foldParams k e.length z s).map (· + bs.length))
      (precomp (tuple Y (Q.map Prod.fst)) (foldEnvIn bs k e z s).2) E := by
  have h := selEnv_envEqOn hM hO hρ hE
    (ws := List.range bs.length ++ (foldParams k e.length z s).map (· + bs.length))
    (pairwise_foldWs bs.length _ ((pairwise_lt_range _).filter _)) hlt
  rw [hQ, hT] at h
  exact h

/-- A term that compiles in the environment of a fold's start or step, mentioning only its
indices, compiles in an environment whose entries at the indices are of the bound types before the
parameters' types, to its arrow after the tuple of those entries. -/
theorem compile_foldEnv_full (hG : G.WF) (hρ : ρ.map Sigma.fst = List.replicate n obj)
    (hps : PrimsHom M ρ G n) (hds : DefsHom M ρ G n) {X : Tree} {e : List (Tree × Tree)}
    (he : EnvHom M ρ G n X e) {bs : List Tree} (hbs : ∀ b ∈ bs, IsTy G n b = true) {k : ℕ}
    {z s : Term} {Y : Tree} {E Q : List (Tree × Tree)} (hE : EnvHom M ρ G n Y E)
    (hlt : ∀ w ∈ List.range bs.length ++ (foldParams k e.length z s).map (· + bs.length),
      w < E.length)
    (hQ : (List.range bs.length ++ (foldParams k e.length z s).map (· + bs.length)).filterMap
      (fun w : ℕ ↦ E[w]?) = Q)
    (hT : Q.map Prod.snd = bs ++ (foldPs k e z s).map Prod.snd) {w : Term} {W c : Tree}
    (hw : compile G n w (foldEnvIn bs k e z s).1 (foldEnvIn bs k e z s).2 = some (W, c))
    (hocc : ∀ i, Term.occurs w i = true →
      i ∈ List.range bs.length ++ (foldParams k e.length z s).map (· + bs.length)) :
    ∃ W', compile G n w Y E = some (W', c) ∧
      eval M ρ W' = eval M ρ (comp W (tuple Y (Q.map Prod.fst))) := by
  have hEf := envHom_foldEnvIn hM hds.2 hρ (k := k) (z := z) (s := s) he hbs
  have hTh : Hom M ρ (tuple Y (Q.map Prod.fst)) Y (foldEnvIn bs k e z s).1 := by
    have h₁ := tuple_hom hM hE.1 Q fun q hq ↦ by
      rw [← hQ] at hq
      obtain ⟨v, -, hv⟩ := List.mem_filterMap.mp hq
      exact (hE.2 q (List.mem_of_getElem? hv)).1
    rwa [hT] at h₁
  obtain ⟨q, hq, hqr⟩ := compile_comp hM hG hρ hps hds w _ _ _ hw hEf Y _ hTh
  obtain ⟨⟨W', c'⟩, hW', hc', hWv⟩ := compile_envEq_on w Y _ q hq E
    ((foldEnvIn_envEqOn hM hds.2 hρ hE hlt hQ hT).mono hocc)
  obtain rfl : c' = c := hc'.trans hqr.1
  exact ⟨W', hW', hWv.trans hqr.2⟩

/-- A fold of the natural numbers that compiles has its start compiled in the environment, its
step in the environment extended by the value and its datum in the environment, and the value of
the fold with the environment's object as parameter at the identity and the datum. -/
theorem compile_natRec_full (hG : G.WF) (hρ : ρ.map Sigma.fst = List.replicate n obj)
    (hps : PrimsHom M ρ G n) (hds : DefsHom M ρ G n) {z s m : Term} {X : Tree}
    {e : List (Tree × Tree)} {r : Tree × Tree} (h : compile G n (Term.natRec z s m) X e = some r)
    (he : EnvHom M ρ G n X e) :
    ∃ zf c sf mf, compile G n z X e = some (zf, c) ∧
      compile G n s (prod X c) (extEnv X c e) = some (sf, c) ∧
      compile G n m X e = some (mf, nat) ∧
      ResEq M ρ (comp (natRecP X c zf sf) (pair (idt X) mf), c) r := by
  obtain ⟨z₀, s₀, m₀, hcs, z', c, hz, s', hs, m', hm, rfl⟩ := compile_natRec_iff.mp h
  obtain ⟨rfl, rfl, rfl⟩ : z = z₀ ∧ s = s₀ ∧ m = m₀ := by simpa [Term.natRec] using hcs
  have hty := compile_hom hM hG hρ hps hds
  -- the parameters are the variables of the environment the start or the step mentions
  have hP : ∀ i, (Term.occurs z i || Term.occurs s (i + 1)) = true →
      i ∈ foldParams 1 e.length z s := fun i hi ↦ mem_foldParams.mpr
    ⟨compile_occurs_lt _ X e _ h i (by
      simp only [Term.natRec, Term.occurs_node, Term.occursStep, List.map_cons, List.map_nil,
        Bool.or_eq_true] at hi ⊢
      exact .inl hi), hi⟩
  have hz' : Hom M ρ z' (ctxObj ((foldPs 1 e z s).map Prod.snd)) c :=
    (hty z _ _ _ hz (envHom_foldEnvIn hM hds.2 hρ (bs := []) he (by simp))).1
  have hct := (hty z _ _ _ hz (envHom_foldEnvIn hM hds.2 hρ (bs := []) he (by simp))).2
  have hC := isObj_of_isTy hM hds.2 hρ c hct
  have hs' : Hom M ρ s' (ctxObj (c :: (foldPs 1 e z s).map Prod.snd)) c :=
    (hty s _ _ _ hs (envHom_foldEnvIn hM hds.2 hρ he (by simpa using hct))).1
  have hmt := (hty m X e _ hm he).1
  have ht := foldPs_hom hM (k := 1) (z := z) (s := s) he
  -- the start and the step in the environment
  obtain ⟨zf, hzf, hzv⟩ := compile_foldEnv_full hM hG hρ hps hds he (bs := []) (by simp) he
    (foldWs_start_lt 1 e z s) (foldWs_start_filterMap 1 e z s) (by simp) hz fun i hi ↦ by
      simpa using hP i (by simp [hi])
  obtain ⟨sf, hsf, hsv⟩ := compile_foldEnv_full hM hG hρ hps hds he (bs := [c])
    (by simpa using hct) (he.ext hM hC hct) (foldWs_nat_lt X c e z s)
    (foldWs_nat_filterMap X c e z s) (by simp [extEnv]) hs fun i hi ↦ by
      rcases i with _ | i
      · simp
      · simpa using hP i (by simp [hi])
  refine ⟨zf, c, sf, m', hzf, hsf, hm, rfl, ?_⟩
  change eval M ρ (natFold ((foldPs 1 e z s).map Prod.snd) c z' s'
    (tuple X ((foldPs 1 e z s).map Prod.fst)) m') =
    eval M ρ (comp (natRecP X c zf sf) (pair (idt X) m'))
  have hpsh : ∀ r ∈ foldPs 1 e z s, Hom M ρ r.1 X r.2 := fun r hr ↦ by
    obtain ⟨v, -, hv⟩ := List.mem_filterMap.mp hr
    exact (he.2 r (List.mem_of_getElem? hv)).1
  generalize foldPs 1 e z s = ps at hz' hs' ht hzv hsv hpsh ⊢
  rcases ps with _ | ⟨p, ps⟩
  · -- no parameters: the fold itself
    exact (natRecP_const hM he.1 hz' hs' hmt).symm.trans
      (eval_op₂_congr 3 (eval_natRecP_congr X c hzv.symm hsv.symm) rfl)
  · -- parameters: the fold with them, natural in the parameter
    have hT : eval M ρ (tuple (prod X c) ((extEnv X c (p :: ps)).map Prod.fst)) =
        eval M ρ (pair (comp (tuple X ((p :: ps).map Prod.fst)) (fst X c)) (snd X c)) :=
      eval_op₂_congr 9 (eval_tuple_comp hM (fst_hom hM he.1 hC) (List.forall₂_map_right_iff.mpr
        (List.forall₂_same.mpr fun _ _ ↦ ⟨rfl, rfl⟩)) hpsh).1 rfl
    exact (natRecP_pair hM ht.isObj_cod hz' hs' ht hmt).trans
      (eval_op₂_congr 3 (eval_natRecP_congr X c hzv.symm
        (hsv.trans (eval_op₂_congr 3 rfl hT)).symm) rfl)


/-- A fold of a list that compiles has its datum compiled in the environment, its start in the
environment, its step in the environment extended by the element and the value, and the value of
the fold with the environment's object as parameter at the identity and the datum. -/
theorem compile_listRec_full (hG : G.WF) (hρ : ρ.map Sigma.fst = List.replicate n obj)
    (hps : PrimsHom M ρ G n) (hds : DefsHom M ρ G n) {z s m : Term} {X : Tree}
    {e : List (Tree × Tree)} {r : Tree × Tree} (h : compile G n (Term.listRec z s m) X e = some r)
    (he : EnvHom M ρ G n X e) :
    ∃ mf a zf c sf, compile G n m X e = some (mf, list a) ∧ compile G n z X e = some (zf, c) ∧
      compile G n s (prod (prod X a) c) (extEnv (prod X a) c (extEnv X a e)) = some (sf, c) ∧
      ResEq M ρ (comp (listRecP X a c zf sf) (pair (idt X) mf), c) r := by
  obtain ⟨z₀, s₀, m₀, hcs, m', a, hm, z', c, hz, s', hs, rfl⟩ := compile_listRec_iff.mp h
  obtain ⟨rfl, rfl, rfl⟩ : z = z₀ ∧ s = s₀ ∧ m = m₀ := by simpa [Term.listRec] using hcs
  have hty := compile_hom hM hG hρ hps hds
  -- the parameters are the variables of the environment the start or the step mentions
  have hP : ∀ i, (Term.occurs z i || Term.occurs s (i + 2)) = true →
      i ∈ foldParams 2 e.length z s := fun i hi ↦ mem_foldParams.mpr
    ⟨compile_occurs_lt _ X e _ h i (by
      simp only [Term.listRec, Term.occurs_node, Term.occursStep, List.map_cons, List.map_nil,
        Bool.or_eq_true] at hi ⊢
      exact .inl hi), hi⟩
  obtain ⟨hmt, hlt⟩ := hty m X e _ hm he
  rw [isTy_list] at hlt
  have hA := isObj_of_isTy hM hds.2 hρ a hlt
  have hz' : Hom M ρ z' (ctxObj ((foldPs 2 e z s).map Prod.snd)) c :=
    (hty z _ _ _ hz (envHom_foldEnvIn hM hds.2 hρ (bs := []) he (by simp))).1
  have hct := (hty z _ _ _ hz (envHom_foldEnvIn hM hds.2 hρ (bs := []) he (by simp))).2
  have hC := isObj_of_isTy hM hds.2 hρ c hct
  have hs' : Hom M ρ s' (ctxObj (c :: a :: (foldPs 2 e z s).map Prod.snd)) c :=
    (hty s _ _ _ hs (envHom_foldEnvIn hM hds.2 hρ he (by simp [hct, hlt]))).1
  have ht := foldPs_hom hM (k := 2) (z := z) (s := s) he
  have heA := he.ext hM hA hlt
  -- the start and the step in the environment
  obtain ⟨zf, hzf, hzv⟩ := compile_foldEnv_full hM hG hρ hps hds he (bs := []) (by simp) he
    (foldWs_start_lt 2 e z s) (foldWs_start_filterMap 2 e z s) (by simp) hz fun i hi ↦ by
      simpa using hP i (by simp [hi])
  obtain ⟨sf, hsf, hsv⟩ := compile_foldEnv_full hM hG hρ hps hds he (bs := [c, a])
    (by simp [hct, hlt]) (heA.ext hM hC hct) (foldWs_list_lt X a c e z s)
    (foldWs_list_filterMap X a c e z s) (by simp [extEnv]) hs fun i hi ↦ by
      rcases i with _ | _ | i
      · exact List.mem_append_left _ (List.mem_range.mpr (by simp))
      · exact List.mem_append_left _ (List.mem_range.mpr (by simp))
      · exact List.mem_append_right _ (List.mem_map.mpr ⟨i, hP i (by simp [hi]), rfl⟩)
  refine ⟨m', a, zf, c, sf, hm, hzf, hsf, rfl, ?_⟩
  change eval M ρ (listFold ((foldPs 2 e z s).map Prod.snd) a c z' s'
    (tuple X ((foldPs 2 e z s).map Prod.fst)) m') =
    eval M ρ (comp (listRecP X a c zf sf) (pair (idt X) m'))
  have hpsh : ∀ r ∈ foldPs 2 e z s, Hom M ρ r.1 X r.2 := fun r hr ↦ by
    obtain ⟨v, -, hv⟩ := List.mem_filterMap.mp hr
    exact (he.2 r (List.mem_of_getElem? hv)).1
  generalize foldPs 2 e z s = ps at hz' hs' ht hzv hsv hpsh ⊢
  rcases ps with _ | ⟨p, ps⟩
  · -- no parameters: the fold itself
    exact (listRecP_const hM he.1 hA hz' hs' hmt).symm.trans
      (eval_op₂_congr 3 (eval_listRecP_congr X a c hzv.symm hsv.symm) rfl)
  · -- parameters: the fold with them, natural in the parameter
    have hXA := isObj_prod hM he.1 hA
    have hfA := fst_hom hM he.1 hA
    have hfC := fst_hom hM hXA hC
    have hpsh' : ∀ r ∈ (p :: ps).map fun q ↦ (comp q.1 (fst X a), q.2),
        Hom M ρ r.1 (prod X a) r.2 := fun r hr ↦ by
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hr
      exact comp_hom hM hfA (hpsh q hq)
    have h₁ := (eval_tuple_comp hM hfA (List.forall₂_map_right_iff.mpr
      (List.forall₂_same.mpr fun _ _ ↦ ⟨rfl, rfl⟩)) hpsh).1
    have h₂ := (eval_tuple_comp hM hfC (List.forall₂_map_right_iff.mpr
      (List.forall₂_same.mpr fun _ _ ↦ ⟨rfl, rfl⟩)) hpsh').1
    have hsA := snd_hom hM he.1 hA
    have hT : eval M ρ (tuple (prod (prod X a) c)
        ((extEnv (prod X a) c (extEnv X a (p :: ps))).map Prod.fst)) =
        eval M ρ (pair (comp (pair (comp (tuple X ((p :: ps).map Prod.fst)) (fst X a))
          (snd X a)) (fst (prod X a) c)) (snd (prod X a) c)) :=
      eval_op₂_congr 9 ((eval_op₂_congr 9 (h₂.trans (eval_op₂_congr 3 h₁ rfl)) rfl).trans
        (pair_comp hM (comp_hom hM hfA ht) hsA hfC).symm) rfl
    exact (listRecP_pair hM ht.isObj_cod hA hz' hs' ht hmt).trans
      (eval_op₂_congr 3 (eval_listRecP_congr X a c hzv.symm
        (hsv.trans (eval_op₂_congr 3 rfl hT)).symm) rfl)

/-- A fold of the natural numbers whose start compiles in the environment, whose step compiles
in the environment extended by the value and whose datum compiles in the environment compiles, to
the value of the fold with the environment's object as parameter at the identity and the
datum. -/
theorem compile_natRec_of_full (hG : G.WF) (hρ : ρ.map Sigma.fst = List.replicate n obj)
    (hps : PrimsHom M ρ G n) (hds : DefsHom M ρ G n) {z s m : Term} {X zf c sf mf : Tree}
    {e : List (Tree × Tree)} (he : EnvHom M ρ G n X e) (hz : compile G n z X e = some (zf, c))
    (hs : compile G n s (prod X c) (extEnv X c e) = some (sf, c))
    (hm : compile G n m X e = some (mf, nat)) :
    ∃ r, compile G n (Term.natRec z s m) X e = some r ∧
      ResEq M ρ (comp (natRecP X c zf sf) (pair (idt X) mf), c) r := by
  obtain ⟨_, hnode, -⟩ := compile_natRec_of_parts hz hs hm
  obtain ⟨zf₂, c₂, sf₂, mf₂, hz₂, hs₂, hm₂, hr⟩ :=
    compile_natRec_full hM hG hρ hps hds hnode he
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (hz.symm.trans hz₂))
  obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj (hs.symm.trans hs₂))
  obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj (hm.symm.trans hm₂))
  exact ⟨_, hnode, hr⟩

/-- A fold of a list whose datum compiles in the environment, whose start compiles in the
environment and whose step compiles in the environment extended by the element and the value
compiles, to the value of the fold with the environment's object as parameter at the identity
and the datum. -/
theorem compile_listRec_of_full (hG : G.WF) (hρ : ρ.map Sigma.fst = List.replicate n obj)
    (hps : PrimsHom M ρ G n) (hds : DefsHom M ρ G n) {z s m : Term} {X mf a zf c sf : Tree}
    {e : List (Tree × Tree)} (he : EnvHom M ρ G n X e)
    (hm : compile G n m X e = some (mf, list a)) (hz : compile G n z X e = some (zf, c))
    (hs : compile G n s (prod (prod X a) c) (extEnv (prod X a) c (extEnv X a e)) =
      some (sf, c)) :
    ∃ r, compile G n (Term.listRec z s m) X e = some r ∧
      ResEq M ρ (comp (listRecP X a c zf sf) (pair (idt X) mf), c) r := by
  obtain ⟨_, hnode, -⟩ := compile_listRec_of_parts hm hz hs
  obtain ⟨mf₂, a₂, zf₂, c₂, sf₂, hm₂, hz₂, hs₂, hr⟩ :=
    compile_listRec_full hM hG hρ hps hds hnode he
  obtain ⟨rfl, ha⟩ := Prod.mk.inj (Option.some.inj (hm.symm.trans hm₂))
  obtain rfl := list_inj ha
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (hz.symm.trans hz₂))
  obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj (hs.symm.trans hs₂))
  exact ⟨_, hnode, hr⟩

/-- A fold of a rose tree that compiles has its datum compiled in the environment, to a rose-tree
object, its step in the environment extended by the pair of a label and the list of the children's
values, and the value of the fold with the environment's object as parameter at the identity and
the datum. -/
theorem compile_roseRec_full (hG : G.WF) (hρ : ρ.map Sigma.fst = List.replicate n obj)
    (hps : PrimsHom M ρ G n) (hds : DefsHom M ρ G n) {c : Tree} {s m : Term} {X : Tree}
    {e : List (Tree × Tree)} {r : Tree × Tree}
    (h : compile G n (Term.roseRec c s m) X e = some r) (he : EnvHom M ρ G n X e) :
    ∃ mf t a F sf, IsTy G n c = true ∧ compile G n m X e = some (mf, t) ∧
      roseParts t = some (a, F) ∧
      compile G n s (prod X (prod a (list c))) (extEnv X (prod a (list c)) e) = some (sf, c) ∧
      ResEq M ρ (comp (roseRecP F X a t c sf) (pair (idt X) mf), c) r := by
  obtain ⟨s₀, m₀, m', t, a, F, s', hcs, hct, hm, ht, hs, rfl⟩ := compile_roseRec_iff.mp h
  obtain ⟨rfl, rfl⟩ : s = s₀ ∧ m = m₀ := by simpa [Term.roseRec] using hcs
  have hty := compile_hom hM hG hρ hps hds
  have hobj := isObj_of_isTy hM hds.2 hρ
  -- the parameters are the variables of the environment the step mentions
  have hP : ∀ i, (Term.occurs Term.star i || Term.occurs s (i + 1)) = true →
      i ∈ foldParams 1 e.length Term.star s := fun i hi ↦
    mem_foldParams.mpr ⟨compile_occurs_lt _ X e _ h i (occurs_roseRec_of_step hi), hi⟩
  obtain ⟨hmt, htt⟩ := hty m X e _ hm he
  have hat := isTy_of_roseParts ht htt
  have hPt : IsTy G n (prod a (list c)) = true := by simp [isTy_prod, isTy_list, hat, hct]
  have hPo := hobj _ hPt
  obtain ⟨nd, hF⟩ := roseFold_of_roseParts hM ht (hobj a hat)
  have hs' : Hom M ρ s' (ctxObj (prod a (list c) :: (foldPs 1 e Term.star s).map Prod.snd)) c :=
    (hty s _ _ _ hs (envHom_foldEnvIn hM hds.2 hρ he (by simpa using hPt))).1
  have htp := foldPs_hom hM (k := 1) (z := Term.star) (s := s) he
  -- the step in the environment
  obtain ⟨sf, hsf, hsv⟩ := compile_foldEnv_full hM hG hρ hps hds he (bs := [prod a (list c)])
    (by simpa using hPt) (he.ext hM hPo hPt) (foldWs_nat_lt X _ e Term.star s)
    (foldWs_nat_filterMap X _ e Term.star s) (by simp [extEnv]) hs fun i hi ↦ by
      rcases i with _ | i
      · simp
      · simpa using hP i (by simp [occurs_star, hi])
  refine ⟨m', t, a, F, sf, hct, hm, ht, hsf, rfl, ?_⟩
  change eval M ρ (roseFold F ((foldPs 1 e Term.star s).map Prod.snd) a t c s'
    (tuple X ((foldPs 1 e Term.star s).map Prod.fst)) m') =
    eval M ρ (comp (roseRecP F X a t c sf) (pair (idt X) m'))
  have hpsh : ∀ r ∈ foldPs 1 e Term.star s, Hom M ρ r.1 X r.2 := fun r hr ↦ by
    obtain ⟨v, -, hv⟩ := List.mem_filterMap.mp hr
    exact (he.2 r (List.mem_of_getElem? hv)).1
  have hFc : ∀ {u u' : Tree}, eval M ρ u = eval M ρ u' → eval M ρ (F u) = eval M ρ (F u') :=
    fun hu ↦ eval_roseParts_congr ht hu
  generalize foldPs 1 e Term.star s = ps at hs' htp hsv hpsh ⊢
  rcases ps with _ | ⟨p, ps⟩
  · -- no parameters: the fold itself
    exact (roseRecP_const hM hF he.1 hs' (idt_hom hM he.1) hmt).symm.trans
      (eval_op₂_congr 3 (eval_roseRecP_congr hFc X a t c hsv.symm) rfl)
  · -- parameters: the fold with them, natural in the parameter
    have hT : eval M ρ (tuple (prod X (prod a (list c)))
        ((extEnv X (prod a (list c)) (p :: ps)).map Prod.fst)) =
        eval M ρ (pair (comp (tuple X ((p :: ps).map Prod.fst)) (fst X (prod a (list c))))
          (snd X (prod a (list c)))) :=
      eval_op₂_congr 9 (eval_tuple_comp hM (fst_hom hM he.1 hPo) (List.forall₂_map_right_iff.mpr
        (List.forall₂_same.mpr fun _ _ ↦ ⟨rfl, rfl⟩)) hpsh).1 rfl
    exact (roseRecP_pair hM hF htp.isObj_cod hs' htp hmt).trans
      (eval_op₂_congr 3 (eval_roseRecP_congr hFc X a t c
        (hsv.trans (eval_op₂_congr 3 rfl hT)).symm) rfl)

/-- A fold of a rose tree whose datum compiles in the environment, to a rose-tree object, and
whose step compiles in the environment extended by the pair of a label and the list of the
children's values compiles, to the value of the fold with the environment's object as parameter
at the identity and the datum. -/
theorem compile_roseRec_of_full (hG : G.WF) (hρ : ρ.map Sigma.fst = List.replicate n obj)
    (hps : PrimsHom M ρ G n) (hds : DefsHom M ρ G n) {c : Tree} {s m : Term}
    {X mf t a sf : Tree} {F : Tree → Tree} {e : List (Tree × Tree)} (he : EnvHom M ρ G n X e)
    (hct : IsTy G n c = true) (hm : compile G n m X e = some (mf, t))
    (ht : roseParts t = some (a, F))
    (hs : compile G n s (prod X (prod a (list c))) (extEnv X (prod a (list c)) e) =
      some (sf, c)) :
    ∃ r, compile G n (Term.roseRec c s m) X e = some r ∧
      ResEq M ρ (comp (roseRecP F X a t c sf) (pair (idt X) mf), c) r := by
  obtain ⟨_, hnode, -⟩ := compile_roseRec_of_parts hct hm ht hs
  obtain ⟨mf₂, t₂, a₂, F₂, sf₂, -, hm₂, ht₂, hs₂, hr⟩ :=
    compile_roseRec_full hM hG hρ hps hds hnode he
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (hm.symm.trans hm₂))
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (ht.symm.trans ht₂))
  obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj (hs.symm.trans hs₂))
  exact ⟨_, hnode, hr⟩

/-- A substitution whose terms compile to the values of an environment, lifted under a variable,
compiles in the extended environment to the values of the extended environment. -/
theorem SubstEq.lift (hG : G.WF) (hρ : ρ.map Sigma.fst = List.replicate n obj)
    (hps : PrimsHom M ρ G n) (hds : DefsHom M ρ G n) {X a : Tree} {e E : List (Tree × Tree)}
    {σ : ℕ → Term} (he : EnvHom M ρ G n X e) (hA : IsObj M ρ a) (hσ : SubstEq M ρ G n X e σ E) :
    SubstEq M ρ G n (prod X a) (extEnv X a e) (Term.liftS σ) (extEnv X a E) := by
  have fX := fst_hom hM he.1 hA
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
      (fun i _ ↦ ?_) fun _ _ ↦ Nat.succ_lt_succ, hr₁.1.trans hr₀.1,
      hr₁.2.trans (eval_op₂_congr 3 hr₀.2 rfl)⟩
    simp [extEnv, precomp]

/-- The values a substitution compiles to, in an environment of arrows, are an environment of
arrows. -/
theorem SubstEq.envHom (hG : G.WF) (hρ : ρ.map Sigma.fst = List.replicate n obj)
    (hps : PrimsHom M ρ G n) (hds : DefsHom M ρ G n) {X : Tree} {e E : List (Tree × Tree)}
    {σ : ℕ → Term} (he : EnvHom M ρ G n X e) (hσ : SubstEq M ρ G n X e σ E) :
    EnvHom M ρ G n X E := by
  refine ⟨he.1, fun p hp ↦ ?_⟩
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hp
  obtain ⟨q, hq, h₂, h₁⟩ := hσ i _ (List.getElem?_eq_getElem hi)
  obtain ⟨hqh, hqt⟩ := compile_hom hM hG hρ hps hds _ X e q hq he
  exact ⟨hqh.congr h₁.symm rfl (congrArg _ h₂.symm), h₂ ▸ hqt⟩

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
    obtain ⟨⟨f', b'⟩, ht', rfl, hf⟩ :=
      ih t (by simp) _ _ _ ht _ _ (he.ext hM hA hat) (SubstEq.lift hM hG hρ hps hds he hA hσ)
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
    obtain ⟨z, s, m, rfl, -⟩ := compile_natRec_iff.mp h
    have hE := SubstEq.envHom hM hG hρ hps hds he hσ
    obtain ⟨zf, c, sf, mf, hz, hs, hm, hr⟩ := compile_natRec_full hM hG hρ hps hds h hE
    obtain ⟨⟨zf', c₁⟩, hz₁, hc₁, hzv⟩ := ih z (by simp) X E _ hz e σ he hσ
    subst hc₁
    have hct := (compile_hom hM hG hρ hps hds z X E _ hz hE).2
    have hC := isObj_of_isTy hM hds.2 hρ _ hct
    obtain ⟨⟨sf', c₂⟩, hs₁, hc₂, hsv⟩ := ih s (by simp) _ _ _ hs _ _ (he.ext hM hC hct)
      (SubstEq.lift hM hG hρ hps hds he hC hσ)
    subst hc₂
    obtain ⟨⟨mf', t⟩, hm₁, rfl, hmv⟩ := ih m (by simp) X E _ hm e σ he hσ
    obtain ⟨r', hr', hrr⟩ := compile_natRec_of_full hM hG hρ hps hds he hz₁ hs₁ hm₁
    exact ⟨r', hr', hrr.1.trans hr.1.symm, hrr.2.trans ((eval_op₂_congr 3
      (eval_natRecP_congr X _ hzv hsv) (eval_op₂_congr 9 rfl hmv)).trans hr.2.symm)⟩
  | listRec =>
    obtain ⟨z, s, m, rfl, -⟩ := compile_listRec_iff.mp h
    have hE := SubstEq.envHom hM hG hρ hps hds he hσ
    obtain ⟨mf, a, zf, c, sf, hm, hz, hs, hr⟩ := compile_listRec_full hM hG hρ hps hds h hE
    obtain ⟨⟨mf', t⟩, hm₁, rfl, hmv⟩ := ih m (by simp) X E _ hm e σ he hσ
    have hlt := (compile_hom hM hG hρ hps hds m X E _ hm hE).2
    rw [isTy_list] at hlt
    have hA := isObj_of_isTy hM hds.2 hρ _ hlt
    obtain ⟨⟨zf', c₁⟩, hz₁, hc₁, hzv⟩ := ih z (by simp) X E _ hz e σ he hσ
    subst hc₁
    have hct := (compile_hom hM hG hρ hps hds z X E _ hz hE).2
    have hC := isObj_of_isTy hM hds.2 hρ _ hct
    have heA := he.ext hM hA hlt
    obtain ⟨⟨sf', c₂⟩, hs₁, hc₂, hsv⟩ := ih s (by simp) _ _ _ hs _ _ (heA.ext hM hC hct)
      (SubstEq.lift hM hG hρ hps hds heA hC (SubstEq.lift hM hG hρ hps hds he hA hσ))
    subst hc₂
    obtain ⟨r', hr', hrr⟩ := compile_listRec_of_full hM hG hρ hps hds he hm₁ hz₁ hs₁
    exact ⟨r', hr', hrr.1.trans hr.1.symm, hrr.2.trans ((eval_op₂_congr 3
      (eval_listRecP_congr X a _ hzv hsv) (eval_op₂_congr 9 rfl hmv)).trans hr.2.symm)⟩
  | roseRec c =>
    obtain ⟨s, m, -, -, -, -, -, rfl, -⟩ := compile_roseRec_iff.mp h
    have hE := SubstEq.envHom hM hG hρ hps hds he hσ
    obtain ⟨mf, t, a, F, sf, hct, hm, ht, hs, hr⟩ := compile_roseRec_full hM hG hρ hps hds h hE
    obtain ⟨⟨mf', t'⟩, hm₁, rfl, hmv⟩ := ih m (by simp) X E _ hm e σ he hσ
    have htt := (compile_hom hM hG hρ hps hds m X E _ hm hE).2
    have hat := isTy_of_roseParts ht htt
    have hPt : IsTy G n (prod a (list c)) = true := by simp [isTy_prod, isTy_list, hat, hct]
    have hP := isObj_of_isTy hM hds.2 hρ _ hPt
    obtain ⟨⟨sf', c₂⟩, hs₁, hc₂, hsv⟩ := ih s (by simp) _ _ _ hs _ _ (he.ext hM hP hPt)
      (SubstEq.lift hM hG hρ hps hds he hP hσ)
    subst hc₂
    obtain ⟨r', hr', hrr⟩ := compile_roseRec_of_full hM hG hρ hps hds he hct hm₁ ht hs₁
    exact ⟨r', hr', hrr.1.trans hr.1.symm, hrr.2.trans ((eval_op₂_congr 3
      (eval_roseRecP_congr (fun hu ↦ eval_roseParts_congr ht hu) X a _ _ hsv)
        (eval_op₂_congr 9 rfl hmv)).trans hr.2.symm)⟩
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

/-- The substitution of objects in a parameters' environment substitutes in its object and
entries. -/
theorem selEnv_substPair (θ : List Tree) (ws : List ℕ) (P : Tree) (E : List (Tree × Tree)) :
    selEnv ws (PartialHorn.subst θ P) (E.map (substPair θ)) =
      (selEnv ws P E).map (substPair θ) := by
  simp only [selEnv, List.map_map]
  refine List.map_congr_left fun i _ ↦ ?_
  cases hx : ws.idxOf? i with
  | none => simp [hx, substPair, subst_idt]
  | some j => cases hE : E[j]? <;> simp [hx, hE, substPair, subst_idt]

/-- The substitution of objects in a fold leaves its parameters. -/
theorem foldParams_osubst (θ : List Tree) (k N : ℕ) (z s : Term) :
    foldParams k N (Term.osubst θ z) (Term.osubst θ s) = foldParams k N z s := by
  simp [foldParams, occurs_osubst]

/-- The substitution of objects in a fold and its environment substitutes in its parameters'
entries. -/
theorem foldPs_osubst (θ : List Tree) (k : ℕ) (e : List (Tree × Tree)) (z s : Term) :
    foldPs k (e.map (substPair θ)) (Term.osubst θ z) (Term.osubst θ s) =
      (foldPs k e z s).map (substPair θ) := by
  simp only [foldPs, List.length_map, foldParams_osubst, List.map_filterMap, List.getElem?_map]

/-- The substitution of objects in a fold's start's or step's environment substitutes in its
object and entries. -/
theorem foldEnvIn_osubst (θ : List Tree) (bs : List Tree) (k : ℕ) (e : List (Tree × Tree))
    (z s : Term) :
    foldEnvIn (bs.map (PartialHorn.subst θ)) k (e.map (substPair θ)) (Term.osubst θ z)
        (Term.osubst θ s) =
      (PartialHorn.subst θ (foldEnvIn bs k e z s).1,
        (foldEnvIn bs k e z s).2.map (substPair θ)) := by
  simp only [foldEnvIn, foldEnv, foldParams_osubst, foldPs_osubst, List.length_map, List.map_map,
    Prod.mk.injEq]
  refine ⟨?_, ?_⟩
  · rw [subst_ctxObj]
    simp [Function.comp_def, substPair]
  · rw [← selEnv_substPair, map_substPair_stdEnv, subst_ctxObj]
    simp [Function.comp_def, substPair]

/-- The substitution of objects in a fold of the natural numbers object at the parameters
substitutes in its parts. -/
theorem subst_natFold (θ Γ : List Tree) (c z s t m : Tree) :
    PartialHorn.subst θ (natFold Γ c z s t m) =
      natFold (Γ.map (PartialHorn.subst θ)) (PartialHorn.subst θ c) (PartialHorn.subst θ z)
        (PartialHorn.subst θ s) (PartialHorn.subst θ t) (PartialHorn.subst θ m) := by
  rcases Γ with _ | ⟨a, Γ⟩
  · simp [natFold, subst_comp, subst_natRec]
  · simp only [natFold, List.map_cons, subst_comp, subst_natRecP, subst_pair]
    rw [subst_ctxObj]
    rfl

/-- The substitution of objects in a fold of a list object at the parameters substitutes in its
parts. -/
theorem subst_listFold (θ Γ : List Tree) (a c z s t m : Tree) :
    PartialHorn.subst θ (listFold Γ a c z s t m) =
      listFold (Γ.map (PartialHorn.subst θ)) (PartialHorn.subst θ a) (PartialHorn.subst θ c)
        (PartialHorn.subst θ z) (PartialHorn.subst θ s) (PartialHorn.subst θ t)
        (PartialHorn.subst θ m) := by
  rcases Γ with _ | ⟨b, Γ⟩
  · simp [listFold, subst_comp, subst_listRec]
  · simp only [listFold, List.map_cons, subst_comp, subst_listRecP, subst_pair]
    rw [subst_ctxObj]
    rfl

/-- The substitution of objects in a fold of a rose-tree object at the parameters substitutes in
its parts, by a fold without the parameter that commutes with the substitution. -/
theorem subst_roseFold (θ Γ : List Tree) {F F' : Tree → Tree}
    (hF : ∀ s, PartialHorn.subst θ (F s) = F' (PartialHorn.subst θ s)) (a t c s u m : Tree) :
    PartialHorn.subst θ (roseFold F Γ a t c s u m) =
      roseFold F' (Γ.map (PartialHorn.subst θ)) (PartialHorn.subst θ a) (PartialHorn.subst θ t)
        (PartialHorn.subst θ c) (PartialHorn.subst θ s) (PartialHorn.subst θ u)
        (PartialHorn.subst θ m) := by
  rcases Γ with _ | ⟨b, Γ⟩
  · simp only [roseFold, List.map_nil, subst_comp, hF]
  · simp only [roseFold, List.map_cons, subst_comp, subst_roseRecP θ hF, subst_pair]
    rw [subst_ctxObj]
    rfl

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
    have hhz₁ := foldEnvIn_osubst θ [] 1 e z s
    simp only [Prod.ext_iff] at hhz₁
    rw [← hhz₁.1, ← hhz₁.2] at hz₁
    have hhs₁ := foldEnvIn_osubst θ [c] 1 e z s
    simp only [Prod.ext_iff] at hhs₁
    rw [← hhs₁.1, ← hhs₁.2] at hs₁
    simp only [substPair, subst_nat] at hm₁
    refine compile_natRec_iff.mpr ⟨_, _, _, rfl, _, _, hz₁, _, hs₁, _, hm₁, ?_⟩
    simp only [substPair, subst_natFold, subst_tuple, foldPs_osubst, List.map_map]
    rfl
  | listRec =>
    obtain ⟨z, s, mm, rfl, m', a, hm, z', c, hz, s', hs, rfl⟩ := compile_listRec_iff.mp h
    have hz₁ := ih z (by simp) _ _ _ hz
    have hs₁ := ih s (by simp) _ _ _ hs
    have hm₁ := ih mm (by simp) X e _ hm
    have hhz₁ := foldEnvIn_osubst θ [] 2 e z s
    simp only [Prod.ext_iff] at hhz₁
    rw [← hhz₁.1, ← hhz₁.2] at hz₁
    have hhs₁ := foldEnvIn_osubst θ [c, a] 2 e z s
    simp only [Prod.ext_iff] at hhs₁
    rw [← hhs₁.1, ← hhs₁.2] at hs₁
    simp only [substPair, subst_list] at hm₁
    refine compile_listRec_iff.mpr ⟨_, _, _, rfl, _, _, hm₁, _, _, hz₁, _, hs₁, ?_⟩
    simp only [substPair, subst_listFold, subst_tuple, foldPs_osubst, List.map_map]
    rfl
  | roseRec c =>
    obtain ⟨s, mm, m', t, a, F, s', rfl, hct, hm, ht, hs, rfl⟩ := compile_roseRec_iff.mp h
    have hs₁ := ih s (by simp) _ _ _ hs
    have hm₁ := ih mm (by simp) X e _ hm
    obtain ⟨F', ht', hF'⟩ := roseParts_subst θ ht
    have hhs₁ := foldEnvIn_osubst θ [prod a (list c)] 1 e Term.star s
    simp only [List.map_cons, List.map_nil, subst_prod, subst_list, osubst_star,
      Prod.ext_iff] at hhs₁
    rw [← hhs₁.1, ← hhs₁.2] at hs₁
    have hP := foldPs_osubst θ 1 e Term.star s
    rw [osubst_star] at hP
    simp only [substPair] at hm₁
    refine compile_roseRec_iff.mpr ⟨_, _, _, _, _, _, _, rfl, hty c hct, hm₁, ht', hs₁, ?_⟩
    simp only [substPair, subst_roseFold θ _ hF', subst_tuple, hP, List.map_map]
    rfl
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
