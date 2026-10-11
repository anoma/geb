/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.FreeTopos.Coproducts
public import Geb.Prototypes.FreeTopos.Internal.Params
public import Geb.Prototypes.FreeTopos.RoseRecursion

set_option doc.verso true in
/-!
# The semantics of the compilation

The compilation of the internal language's terms is compositional, sound and natural in every
model of the theory extended by definitions. The value of a term's arrow depends only on the
values of its environment's arrows ({lit}`compile_envEq`). A term's arrow is an arrow from the
environment's object to the term's type when the environment's arrows, the primitive arrows and
the definitions' operations are arrows ({lit}`compile_hom`). In an environment whose arrows are
precomposed with an arrow, a term's arrow is precomposed with it ({lit}`compile_comp`), the
naturality of the interpretation of Part I of \[LambekScott1986\]; its case of abstraction is
the naturality of currying ({name}`Geb.FreeTopos.curry_comp`).

## Main definitions

* {lit}`EnvEq` — two environments of the same types whose arrows have equal values.
* {lit}`EnvHom` — an environment of arrows from an object.
* {lit}`PrimsHom`, {lit}`DefsHom`, {lit}`ObjsHom` — the primitive arrows and the definitions'
  operations are arrows, and the object definitions' operations take objects to objects.

## Main statements

* {lit}`compile_envEq` — the compilation respects environments of equal values.
* {lit}`compile_hom` — the compilation is sound for typing.
* {lit}`compile_comp` — the compilation is natural.

## References

* \[LambekScott1986\], Part I, for the interpretation of the typed λ-calculus in a
  cartesian closed category.

## Tags

internal language, categorical semantics, compositionality
-/

set_option doc.verso true

@[expose] public section

namespace Geb.FreeTopos.Internal

open PartialHorn (Tree op eval Model IsModel)
open Sorts
open scoped FinEnum

universe v

/-- A result of a second partial function at each element of a list, related to the first's,
lifts to the lists of results. -/
theorem mapM_lift {α β γ : Type} {f : α → Option β} {g : α → Option γ} {R : β → γ → Prop}
    (l : List α) : ∀ {rs : List β}, l.mapM f = some rs →
      (∀ a ∈ l, ∀ r, f a = some r → ∃ r', g a = some r' ∧ R r r') →
      ∃ rs', l.mapM g = some rs' ∧ List.Forall₂ R rs rs' :=
  l.rec (motive := fun l ↦ ∀ {rs : List β}, l.mapM f = some rs →
      (∀ a ∈ l, ∀ r, f a = some r → ∃ r', g a = some r' ∧ R r r') →
      ∃ rs', l.mapM g = some rs' ∧ List.Forall₂ R rs rs')
    (fun h _ ↦ by
      obtain rfl : [] = _ := by simpa using h
      exact ⟨[], rfl, .nil⟩)
    (fun a l ih rs h hfg ↦ by
      simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.pure_def, Option.some.injEq] at h
      obtain ⟨r, hr, rs₀, hrs₀, rfl⟩ := h
      obtain ⟨r', hr', hR⟩ := hfg a List.mem_cons_self r hr
      obtain ⟨rs', hrs', hR'⟩ := ih hrs₀ fun a' ha' ↦ hfg a' (List.mem_cons_of_mem _ ha')
      exact ⟨r' :: rs', by simp [List.mapM_cons, hr', hrs'], .cons hR hR'⟩)

section Congruence

variable {defs : List PartialHorn.Defn} {M : Model.{v} (ext defs).sig} {ρ : List M.Val}

variable (M ρ) in
/-- Two results of the same type whose arrows have equal values. -/
def ResEq (r r' : Tree × Tree) : Prop := r'.2 = r.2 ∧ eval M ρ r'.1 = eval M ρ r.1

variable (M ρ) in
/-- Two environments, each variable of the first of the same type in the second, with an arrow
of equal value. -/
def EnvEq (e e' : List (Tree × Tree)) : Prop :=
  ∀ (i : ℕ) (p : Tree × Tree), e[i]? = some p → ∃ q, e'[i]? = some q ∧ ResEq M ρ p q

/-- Results related pointwise have the same types. -/
theorem map_snd_of_forall₂ {rs rs' : List (Tree × Tree)} (h : List.Forall₂ (ResEq M ρ) rs rs') :
    rs'.map Prod.snd = rs.map Prod.snd :=
  h.rec (motive := fun rs rs' _ ↦ rs'.map Prod.snd = rs.map Prod.snd) rfl
    fun hr _ ih ↦ by simp [hr.1, ih]

/-- Tuples of arrows related pointwise have equal values. -/
theorem eval_tuple_of_forall₂ (X : Tree) {rs rs' : List (Tree × Tree)}
    (h : List.Forall₂ (ResEq M ρ) rs rs') :
    eval M ρ (tuple X (rs'.map Prod.fst)) = eval M ρ (tuple X (rs.map Prod.fst)) :=
  h.rec (motive := fun rs rs' _ ↦
      eval M ρ (tuple X (rs'.map Prod.fst)) = eval M ρ (tuple X (rs.map Prod.fst))) rfl
    fun hr hrs ih ↦ by
      rcases hrs with _ | ⟨_, _⟩
      · exact hr.2
      · exact eval_op₂_congr 9 ih hr.2

/-- A rose-tree object's fold respects the value of its step. -/
theorem eval_roseParts_congr {t a s s' : Tree} {F : Tree → Tree} (h : roseParts t = some (a, F))
    (hs : eval M ρ s = eval M ρ s') : eval M ρ (F s) = eval M ρ (F s') := by
  rcases roseParts_eq_some.mp h with ⟨-, -, rfl⟩ | ⟨-, rfl⟩
  · exact eval_op₁_congr 39 hs
  · exact eval_op₂_congr 42 rfl hs

/-- Extending environments of equal values by a variable keeps their values equal. -/
theorem EnvEq.ext {e e' : List (Tree × Tree)} (h : EnvEq M ρ e e') (X a : Tree) :
    EnvEq M ρ (extEnv X a e) (extEnv X a e') := by
  intro i p hp
  rcases i with _ | j
  · exact ⟨p, by simpa [extEnv] using hp, rfl, rfl⟩
  · simp only [extEnv, List.getElem?_cons_succ, List.getElem?_map, Option.map_eq_some_iff] at hp
    obtain ⟨p₀, hp₀, rfl⟩ := hp
    obtain ⟨q₀, hq₀, h₂, h₁⟩ := h j p₀ hp₀
    exact ⟨(comp q₀.1 (fst X a), q₀.2), by simp [extEnv, hq₀], h₂, eval_op₂_congr 3 h₁ rfl⟩

variable (M ρ) in
/-- Two environments, each variable of the first that a predicate holds of of the same type in
the second, with an arrow of equal value. -/
def EnvEqOn (P : ℕ → Prop) (e e' : List (Tree × Tree)) : Prop :=
  ∀ (i : ℕ) (p : Tree × Tree), P i → e[i]? = some p → ∃ q, e'[i]? = some q ∧ ResEq M ρ p q

/-- Environments of equal values at the variables a predicate holds of are so at those another
holds of, when the second implies the first. -/
theorem EnvEqOn.mono {P Q : ℕ → Prop} {e e' : List (Tree × Tree)} (h : EnvEqOn M ρ P e e')
    (hQ : ∀ i, Q i → P i) : EnvEqOn M ρ Q e e' :=
  fun i p hi ↦ h i p (hQ i hi)

/-- Extending environments of equal values at the successors of the variables a predicate holds
of by a variable keeps their values equal at those variables. -/
theorem EnvEqOn.ext {P : ℕ → Prop} {e e' : List (Tree × Tree)}
    (h : EnvEqOn M ρ (fun i ↦ P (i + 1)) e e') (X a : Tree) :
    EnvEqOn M ρ P (extEnv X a e) (extEnv X a e') := by
  intro i p hi hp
  rcases i with _ | j
  · exact ⟨p, by simpa [extEnv] using hp, rfl, rfl⟩
  · simp only [extEnv, List.getElem?_cons_succ, List.getElem?_map, Option.map_eq_some_iff] at hp
    obtain ⟨p₀, hp₀, rfl⟩ := hp
    obtain ⟨q₀, hq₀, h₂, h₁⟩ := h j p₀ hi hp₀
    exact ⟨(comp q₀.1 (fst X a), q₀.2), by simp [extEnv, hq₀], h₂, eval_op₂_congr 3 h₁ rfl⟩

/-- The fold of the natural numbers object respects the values of the parameters' tuple and of
the datum. -/
theorem eval_natFold_congr (Γ : List Tree) (c z s : Tree) {t t' m m' : Tree}
    (ht : eval M ρ t = eval M ρ t') (hm : eval M ρ m = eval M ρ m') :
    eval M ρ (natFold Γ c z s t m) = eval M ρ (natFold Γ c z s t' m') := by
  rcases Γ with _ | ⟨a, Γ⟩
  · exact eval_op₂_congr 3 rfl hm
  · exact eval_op₂_congr 3 rfl (eval_op₂_congr 9 ht hm)

/-- The fold of a list object respects the values of the parameters' tuple and of the datum. -/
theorem eval_listFold_congr (Γ : List Tree) (a c z s : Tree) {t t' m m' : Tree}
    (ht : eval M ρ t = eval M ρ t') (hm : eval M ρ m = eval M ρ m') :
    eval M ρ (listFold Γ a c z s t m) = eval M ρ (listFold Γ a c z s t' m') := by
  rcases Γ with _ | ⟨b, Γ⟩
  · exact eval_op₂_congr 3 rfl hm
  · exact eval_op₂_congr 3 rfl (eval_op₂_congr 9 ht hm)

/-- The fold of a rose-tree object respects the values of the parameters' tuple and of the
datum. -/
theorem eval_roseFold_congr (F : Tree → Tree) (Γ : List Tree) (a t₀ c s : Tree) {t t' m m' : Tree}
    (ht : eval M ρ t = eval M ρ t') (hm : eval M ρ m = eval M ρ m') :
    eval M ρ (roseFold F Γ a t₀ c s t m) = eval M ρ (roseFold F Γ a t₀ c s t' m') := by
  rcases Γ with _ | ⟨b, Γ⟩
  · exact eval_op₂_congr 3 rfl hm
  · exact eval_op₂_congr 3 rfl (eval_op₂_congr 9 ht hm)

/-- A fold's parameters in an environment and the entries there are those in an environment of
equal values at the variables the fold mentions, when the fold compiles in the first. -/
theorem foldPs_envEqOn {k : ℕ} {z s : Term} {e e' : List (Tree × Tree)}
    (hlt : ∀ i, (Term.occurs z i || Term.occurs s (i + k)) = true → i < e.length)
    (he : EnvEqOn M ρ (fun i ↦ (Term.occurs z i || Term.occurs s (i + k)) = true) e e') :
    foldParams k e'.length z s = foldParams k e.length z s ∧
      List.Forall₂ (ResEq M ρ) (foldPs k e z s) (foldPs k e' z s) := by
  have hV : foldParams k e'.length z s = foldParams k e.length z s :=
    filter_range_congr fun i hi ↦ by
      obtain ⟨q, hq, -⟩ := he i _ hi (List.getElem?_eq_getElem (hlt i hi))
      exact ⟨fun _ ↦ hlt i hi, fun _ ↦ (List.getElem?_eq_some_iff.mp hq).1⟩
  refine ⟨hV, ?_⟩
  simp only [foldPs, hV]
  exact forall₂_filterMap _ (fun v hv ↦ (mem_foldParams.mp hv).1)
    fun v hv p hp ↦ he v p (mem_foldParams.mp hv).2 hp

/-- The compilation respects environments of equal values at the variables a term mentions: in
one whose arrows at them have the values of another's, the term has the same type and an arrow of
the same value. -/
theorem compile_envEq_on {G : Globals} {n : ℕ} (s : Term) :
    ∀ (X : Tree) (e : List (Tree × Tree)) (r : Tree × Tree), compile G n s X e = some r →
      ∀ e', EnvEqOn M ρ (fun i ↦ Term.occurs s i = true) e e' →
        ∃ r', compile G n s X e' = some r' ∧ ResEq M ρ r r' := by
  refine RoseTree.ind (P := fun s ↦ ∀ (X : Tree) (e : List (Tree × Tree)) (r : Tree × Tree),
    compile G n s X e = some r → ∀ e', EnvEqOn M ρ (fun i ↦ Term.occurs s i = true) e e' →
      ∃ r', compile G n s X e' = some r' ∧ ResEq M ρ r r')
    (fun l cs ih ↦ ?_) s
  intro X e r h e' he
  -- a child the node's variables include the variables of
  have sub : ∀ c ∈ cs, (∀ i, Term.occurs c i = true →
      Term.occurs (RoseTree.node l cs) i = true) → ∀ r, compile G n c X e = some r →
      ∃ r', compile G n c X e' = some r' ∧ ResEq M ρ r r' :=
    fun c hc hsub r hr ↦ ih c hc X e r hr e' (he.mono hsub)
  cases l with
  | var i =>
    obtain ⟨rfl, hi⟩ := compile_var_iff.mp h
    obtain ⟨q, hq, hr⟩ := he i r (by simp [Term.occurs_node, Term.occursStep]) hi
    exact ⟨q, compile_var_iff.mpr ⟨rfl, hq⟩, hr⟩
  | star =>
    obtain ⟨rfl, rfl⟩ := compile_star_iff.mp h
    exact ⟨_, compile_star_iff.mpr ⟨rfl, rfl⟩, rfl, rfl⟩
  | pair =>
    obtain ⟨t, u, f, a, g, b, rfl, ht, hu, rfl⟩ := compile_pair_iff.mp h
    obtain ⟨⟨f', a'⟩, ht', rfl, hf⟩ :=
      sub t (by simp) (fun i hi ↦ by simp [Term.occurs_node, Term.occursStep, hi]) _ ht
    obtain ⟨⟨g', b'⟩, hu', rfl, hg⟩ :=
      sub u (by simp) (fun i hi ↦ by simp [Term.occurs_node, Term.occursStep, hi]) _ hu
    exact ⟨_, compile_pair_iff.mpr ⟨t, u, f', a', g', b', rfl, ht', hu', rfl⟩, rfl,
      eval_op₂_congr 9 hf hg⟩
  | fst =>
    obtain ⟨t, f, a, b, rfl, ht, rfl⟩ := compile_fst_iff.mp h
    obtain ⟨⟨f', p⟩, ht', rfl, hf⟩ :=
      sub t (by simp) (fun i hi ↦ by simp [Term.occurs_node, Term.occursStep, hi]) _ ht
    exact ⟨_, compile_fst_iff.mpr ⟨t, f', a, b, rfl, ht', rfl⟩, rfl, eval_op₂_congr 3 rfl hf⟩
  | snd =>
    obtain ⟨t, f, a, b, rfl, ht, rfl⟩ := compile_snd_iff.mp h
    obtain ⟨⟨f', p⟩, ht', rfl, hf⟩ :=
      sub t (by simp) (fun i hi ↦ by simp [Term.occurs_node, Term.occursStep, hi]) _ ht
    exact ⟨_, compile_snd_iff.mpr ⟨t, f', a, b, rfl, ht', rfl⟩, rfl, eval_op₂_congr 3 rfl hf⟩
  | lam a =>
    obtain ⟨t, f, b, rfl, hty, ht, rfl⟩ := compile_lam_iff.mp h
    obtain ⟨⟨f', b'⟩, ht', rfl, hf⟩ := ih t (by simp) _ _ _ ht _
      ((he.mono (Q := fun i ↦ Term.occurs t (i + 1) = true) fun i hi ↦ by
        simpa [Term.occurs_node, Term.occursStep] using hi).ext X a)
    exact ⟨_, compile_lam_iff.mpr ⟨t, f', b', rfl, hty, ht', rfl⟩, rfl,
      eval_op₃_congr 24 rfl rfl hf⟩
  | app =>
    obtain ⟨t, u, rfl, f, a, b, ht, g, hu, rfl⟩ := compile_app_iff.mp h
    obtain ⟨⟨f', p⟩, ht', rfl, hf⟩ :=
      sub t (by simp) (fun i hi ↦ by simp [Term.occurs_node, Term.occursStep, hi]) _ ht
    obtain ⟨⟨g', a'⟩, hu', rfl, hg⟩ :=
      sub u (by simp) (fun i hi ↦ by simp [Term.occurs_node, Term.occursStep, hi]) _ hu
    exact ⟨_, compile_app_iff.mpr ⟨t, u, rfl, f', a', b, ht', g', hu', rfl⟩, rfl,
      eval_op₂_congr 3 rfl (eval_op₂_congr 9 hf hg)⟩
  | arr k θ =>
    obtain ⟨t, rfl, p, hp, g, ht, hl, hθ, rfl⟩ := compile_arr_iff.mp h
    obtain ⟨⟨g', d'⟩, ht', rfl, hg⟩ :=
      sub t (by simp) (fun i hi ↦ by simp [Term.occurs_node, Term.occursStep, hi]) _ ht
    exact ⟨_, compile_arr_iff.mpr ⟨t, rfl, p, hp, g', ht', hl, hθ, rfl⟩, rfl,
      eval_op₂_congr 3 rfl hg⟩
  | natRec =>
    obtain ⟨z, s, m, rfl, z', c, hz, s', hs, m', hm, rfl⟩ := compile_natRec_iff.mp h
    obtain ⟨hV, hPs⟩ := foldPs_envEqOn
      (fun i hi ↦ compile_occurs_lt _ X e _ h i (by
        simp only [Term.occurs_node, Term.occursStep, List.map_cons, List.map_nil,
          Bool.or_eq_true] at hi ⊢
        exact .inl hi))
      (he.mono fun i hi ↦ by
        simp only [Term.occurs_node, Term.occursStep, List.map_cons, List.map_nil,
          Bool.or_eq_true] at hi ⊢
        exact .inl hi)
    have hE : ∀ bs, foldEnvIn bs 1 e' z s = foldEnvIn bs 1 e z s := fun bs ↦ by
      simp only [foldEnvIn, hV, map_snd_of_forall₂ hPs]
    obtain ⟨⟨m'', t⟩, hm', rfl, hmv⟩ :=
      sub m (by simp) (fun i hi ↦ by simp [Term.occurs_node, Term.occursStep, hi]) _ hm
    refine ⟨_, compile_natRec_iff.mpr ⟨z, s, m, rfl, z', c, (hE []).symm ▸ hz, s',
      (hE [c]).symm ▸ hs, m'', hm', rfl⟩, rfl, ?_⟩
    rw [map_snd_of_forall₂ hPs]
    exact eval_natFold_congr _ _ _ _ (eval_tuple_of_forall₂ X hPs) hmv
  | listRec =>
    obtain ⟨z, s, m, rfl, m', a, hm, z', c, hz, s', hs, rfl⟩ := compile_listRec_iff.mp h
    obtain ⟨hV, hPs⟩ := foldPs_envEqOn
      (fun i hi ↦ compile_occurs_lt _ X e _ h i (by
        simp only [Term.occurs_node, Term.occursStep, List.map_cons, List.map_nil,
          Bool.or_eq_true] at hi ⊢
        exact .inl hi))
      (he.mono fun i hi ↦ by
        simp only [Term.occurs_node, Term.occursStep, List.map_cons, List.map_nil,
          Bool.or_eq_true] at hi ⊢
        exact .inl hi)
    have hE : ∀ bs, foldEnvIn bs 2 e' z s = foldEnvIn bs 2 e z s := fun bs ↦ by
      simp only [foldEnvIn, hV, map_snd_of_forall₂ hPs]
    obtain ⟨⟨m'', t⟩, hm', rfl, hmv⟩ :=
      sub m (by simp) (fun i hi ↦ by simp [Term.occurs_node, Term.occursStep, hi]) _ hm
    refine ⟨_, compile_listRec_iff.mpr ⟨z, s, m, rfl, m'', a, hm', z', c, (hE []).symm ▸ hz,
      s', (hE [c, a]).symm ▸ hs, rfl⟩, rfl, ?_⟩
    rw [map_snd_of_forall₂ hPs]
    exact eval_listFold_congr _ _ _ _ _ (eval_tuple_of_forall₂ X hPs) hmv
  | roseRec c =>
    obtain ⟨s, m, m', t, a, F, s', rfl, hc, hm, ht, hs, rfl⟩ := compile_roseRec_iff.mp h
    -- the step's variables of the environment are the node's
    have hstep : ∀ i, (Term.occurs Term.star i || Term.occurs s (i + 1)) = true →
        Term.occurs (RoseTree.node (.roseRec c) [s, m]) i = true := fun i hi ↦ by
      simp only [occurs_star, Bool.false_or] at hi
      simp only [Term.occurs_node, Term.occursStep, List.map_cons, List.map_nil, hi,
        Bool.true_or]
    obtain ⟨hV, hPs⟩ := foldPs_envEqOn (fun i hi ↦ compile_occurs_lt _ X e _ h i (hstep i hi))
      (he.mono fun i hi ↦ hstep i hi)
    have hE : ∀ bs, foldEnvIn bs 1 e' Term.star s = foldEnvIn bs 1 e Term.star s := fun bs ↦ by
      simp only [foldEnvIn, hV, map_snd_of_forall₂ hPs]
    obtain ⟨⟨m'', t'⟩, hm', rfl, hmv⟩ :=
      sub m (by simp) (fun i hi ↦ by simp [Term.occurs_node, Term.occursStep, hi]) _ hm
    refine ⟨_, compile_roseRec_iff.mpr ⟨s, m, m'', _, a, F, s', rfl, hc, hm', ht,
      (hE _).symm ▸ hs, rfl⟩, rfl, ?_⟩
    rw [map_snd_of_forall₂ hPs]
    exact eval_roseFold_congr _ _ _ _ _ _ (eval_tuple_of_forall₂ X hPs) hmv
  | eq =>
    obtain ⟨t, u, rfl, f, a, ht, g, hu, rfl⟩ := compile_eq_iff.mp h
    obtain ⟨⟨f', a'⟩, ht', rfl, hf⟩ :=
      sub t (by simp) (fun i hi ↦ by simp [Term.occurs_node, Term.occursStep, hi]) _ ht
    obtain ⟨⟨g', b'⟩, hu', rfl, hg⟩ :=
      sub u (by simp) (fun i hi ↦ by simp [Term.occurs_node, Term.occursStep, hi]) _ hu
    exact ⟨_, compile_eq_iff.mpr ⟨_, _, rfl, f', _, ht', g', hu', rfl⟩, rfl,
      eval_op₂_congr 3 rfl (eval_op₂_congr 9 hf hg)⟩
  | defn k θ =>
    obtain ⟨d, rs, hd, hrs, hl, hθ, hty, rfl⟩ := compile_defn_iff.mp h
    obtain ⟨rs', hrs', hR⟩ := mapM_lift (g := fun c ↦ compile G n c X e') cs hrs
      fun c hc r hr ↦ sub c hc (fun i hi ↦ by
        simp only [Term.occurs_node, Term.occursStep, List.any_map, List.any_eq_true,
          Function.comp_apply]
        exact ⟨c, hc, hi⟩) r hr
    exact ⟨_, compile_defn_iff.mpr ⟨d, rs', hd, hrs', hl, hθ,
      (map_snd_of_forall₂ hR).trans hty, rfl⟩, rfl,
      eval_op₂_congr 3 rfl (eval_tuple_of_forall₂ X hR)⟩

/-- The compilation respects environments of equal values: in one whose arrows have the values
of another's, a term has the same type and an arrow of the same value. -/
theorem compile_envEq {G : Globals} {n : ℕ} (s : Term) (X : Tree) (e : List (Tree × Tree))
    (r : Tree × Tree) (h : compile G n s X e = some r) (e' : List (Tree × Tree))
    (he : EnvEq M ρ e e') : ∃ r', compile G n s X e' = some r' ∧ ResEq M ρ r r' :=
  compile_envEq_on s X e r h e' fun i p _ ↦ he i p

end Congruence

/-- An element of a list of results of a partial function over a list is its value at an
element. -/
theorem exists_of_mapM {α β : Type} {f : α → Option β} {l : List α} {rs : List β}
    (h : l.mapM f = some rs) {r : β} (hr : r ∈ rs) : ∃ a ∈ l, f a = some r := by
  rw [PartialHorn.mapM_eq_some_iff] at h
  obtain ⟨a, ha, he⟩ := List.mem_map.mp (h ▸ List.mem_map_of_mem hr : some r ∈ l.map f)
  exact ⟨a, ha, he⟩

section Types

variable {G : Globals}

/-- Whether a type is one: the equation of the type operations. -/
theorem isTy_op (n k : ℕ) (cs : List Tree) :
    IsTy G n (op k cs) = (G.isTyOp k cs.length && cs.all (IsTy G n)) := by
  simp only [IsTy, op, RoseTree.para_node, List.length_map]
  rw [List.all_map]
  rfl

/-- A node of label zero over one child is a type exactly when the child is a leaf whose label
is below the number of object variables. -/
theorem isTy_var_node_iff {n : ℕ} {i : Tree} :
    IsTy G n (RoseTree.node 0 [i]) = true ↔ i.children = [] ∧ i.label < n := by
  simp [IsTy]

/-- A variable is a type when its index is below the number of object variables. -/
theorem isTy_var {n i : ℕ} : IsTy G n (PartialHorn.var i) = true ↔ i < n :=
  isTy_var_node_iff.trans (by simp)

/-- A product of types is a type. -/
theorem isTy_prod {n : ℕ} {a b : Tree} : IsTy G n (prod a b) = (IsTy G n a && IsTy G n b) := by
  simp [prod, isTy_op, Globals.isTyOp, tyOps]

/-- A coproduct of types is a type. -/
theorem isTy_coprod {n : ℕ} {a b : Tree} : IsTy G n (coprod a b) = (IsTy G n a && IsTy G n b) := by
  simp [coprod, isTy_op, Globals.isTyOp, tyOps]

/-- An exponential of types is a type. -/
theorem isTy_exp {n : ℕ} {a b : Tree} : IsTy G n (exp a b) = (IsTy G n a && IsTy G n b) := by
  simp [exp, isTy_op, Globals.isTyOp, tyOps]

/-- A list object of a type is a type. -/
theorem isTy_list {n : ℕ} {a : Tree} : IsTy G n (list a) = IsTy G n a := by
  simp [list, isTy_op, Globals.isTyOp, tyOps]

/-- A rose-tree object over a type of labels is a type. -/
theorem isTy_lrose {n : ℕ} {a : Tree} : IsTy G n (lrose a) = IsTy G n a := by
  simp [lrose, isTy_op, Globals.isTyOp, tyOps]

/-- A rose-tree object's type of labels is a type where the object is. -/
theorem isTy_of_roseParts {n : ℕ} {t a : Tree} {F : Tree → Tree} (h : roseParts t = some (a, F))
    (ht : IsTy G n t = true) : IsTy G n a = true := by
  rcases roseParts_eq_some.mp h with ⟨-, rfl, -⟩ | ⟨rfl, -⟩
  · simp [nat, isTy_op, Globals.isTyOp, tyOps]
  · simpa [isTy_lrose] using ht

/-- The terminal object is a type. -/
theorem isTy_one {n : ℕ} : IsTy G n one = true := by simp [one, isTy_op, Globals.isTyOp, tyOps]

/-- The initial object is a type. -/
theorem isTy_zero {n : ℕ} : IsTy G n zero = true := by simp [zero, isTy_op, Globals.isTyOp, tyOps]

/-- The subobject classifier is a type. -/
theorem isTy_omega {n : ℕ} : IsTy G n omega = true := by
  simp [omega, isTy_op, Globals.isTyOp, tyOps]

/-- The natural numbers object is a type. -/
theorem isTy_nat {n : ℕ} : IsTy G n nat = true := by simp [nat, isTy_op, Globals.isTyOp, tyOps]

/-- The rose-tree object is a type. -/
theorem isTy_rose {n : ℕ} : IsTy G n rose = true := by simp [rose, isTy_op, Globals.isTyOp, tyOps]

/-- A type in {lit}`m` object variables, with types in {lit}`n` substituted for them, is a type in
{lit}`n`. -/
theorem isTy_subst {m n : ℕ} {θ : List Tree} (hl : θ.length = m) (hθ : θ.all (IsTy G n) = true) :
    ∀ A : Tree, IsTy G m A = true → IsTy G n (PartialHorn.subst θ A) = true :=
  RoseTree.ind fun l cs ih hA ↦ by
    rcases l with _ | k
    · rcases cs with _ | ⟨i, _ | ⟨j, cs⟩⟩
      · simp [IsTy] at hA
      rotate_left
      · simp [IsTy] at hA
      obtain ⟨hc, hA⟩ := isTy_var_node_iff.mp hA
      rw [PartialHorn.subst_node_zero _ hc]
      have hi : i.label < θ.length := hl ▸ hA
      rw [List.getElem?_eq_getElem hi, Option.getD_some]
      exact List.all_eq_true.mp hθ _ (List.getElem_mem hi)
    · change IsTy G m (op k cs) = true at hA
      rw [isTy_op, Bool.and_eq_true, List.all_eq_true] at hA
      change IsTy G n (PartialHorn.subst θ (op k cs)) = true
      rw [subst_op, isTy_op, Bool.and_eq_true, List.all_eq_true, List.length_map]
      exact ⟨hA.1, fun c hc ↦ by
        obtain ⟨c', hc', rfl⟩ := List.mem_map.mp hc
        exact ih c' hc' (hA.2 c' hc')⟩

/-- A type is a type of the product of a context of types. -/
theorem isTy_ctxObj {G : Globals} {n : ℕ} :
    ∀ Γ : List Tree, Γ.all (IsTy G n) = true → IsTy G n (ctxObj Γ) = true :=
  List.rec (fun _ ↦ isTy_one) fun a Γ ih h ↦ by
    simp only [List.all_cons, Bool.and_eq_true] at h
    rcases Γ with _ | ⟨b, Γ⟩
    · exact h.1
    · change IsTy G n (prod (ctxObj (b :: Γ)) a) = true
      simp [isTy_prod, ih h.2, h.1]

end Types

section Typing

variable {defs : List PartialHorn.Defn} {M : Model.{v} (ext defs).sig} {ρ : List M.Val}

variable (M) in
/-- Each object definition's operation takes objects to an object. -/
def ObjsHom (G : Globals) : Prop :=
  ∀ (k m : ℕ) (b : Tree), G.defs[k]? = some (.object m b) →
    ∀ ws : List M.Val, ws.map Sigma.fst = List.replicate m obj →
      ∃ w, M.op (G.base + k) ws = Part.some w ∧ w.1 = obj

/-- Objects have values, objects. -/
theorem exists_vals_of_isObj :
    ∀ cs : List Tree, (∀ c ∈ cs, IsObj M ρ c) → ∃ ws : List M.Val,
      cs.map (eval M ρ) = ws.map Part.some ∧ ws.map Sigma.fst = List.replicate cs.length obj :=
  List.rec (fun _ ↦ ⟨[], rfl, rfl⟩) fun c cs ih h ↦ by
    obtain ⟨w, hw, hws⟩ := h c List.mem_cons_self
    obtain ⟨ws, h₁, h₂⟩ := ih fun c' hc' ↦ h c' (List.mem_cons_of_mem _ hc')
    exact ⟨w :: ws, by simp [hw, h₁], by simp [hws, h₂, List.replicate_succ]⟩

/-- A type denotes an object at an assignment of objects to its variables. -/
theorem isObj_of_isTy (hM : IsModel (ext defs) M) {G : Globals} (hO : ObjsHom M G) {n : ℕ}
    (hρ : ρ.map Sigma.fst = List.replicate n obj) :
    ∀ A : Tree, IsTy G n A = true → IsObj M ρ A :=
  RoseTree.ind fun l cs ih hA ↦ by
    rcases l with _ | k
    · rcases cs with _ | ⟨i, _ | ⟨j, cs⟩⟩
      · simp [IsTy] at hA
      rotate_left
      · simp [IsTy] at hA
      obtain ⟨hc, hA⟩ := isTy_var_node_iff.mp hA
      have hlen : ρ.length = n := by simpa using congrArg List.length hρ
      have hi : i.label < ρ.length := hlen ▸ hA
      refine ⟨ρ[i.label], ?_, ?_⟩
      · rw [PartialHorn.eval_node_zero hc, List.getElem?_eq_getElem hi]
        rfl
      · have := congrArg (·[i.label]?) hρ
        simp only [List.getElem?_map, List.getElem?_eq_getElem hi,
          List.getElem?_replicate] at this
        simpa [hA] using this
    · change IsTy G n (op k cs) = true at hA
      rw [isTy_op, Bool.and_eq_true, List.all_eq_true] at hA
      have hc : ∀ c ∈ cs, IsObj M ρ c := fun c hc ↦ ih c hc (hA.2 c hc)
      change IsObj M ρ (op k cs)
      have h₁ := hA.1
      simp only [Globals.isTyOp, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true] at h₁
      rcases h₁ with h₁ | ⟨hk, hm⟩
      rotate_left
      · -- an object definition
        split at hm
        · rename_i m' b hdef
          obtain rfl : m' = cs.length := by simpa using hm
          obtain ⟨ws, hws, hwsort⟩ := exists_vals_of_isObj cs hc
          obtain ⟨w, hw, hwo⟩ := hO _ _ b hdef ws hwsort
          rw [Nat.add_sub_cancel' hk] at hw
          exact ⟨w, (eval_op_of_values hws k).trans hw, hwo⟩
        · simp at hm
      simp only [tyOps, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at h₁
      rcases h₁ with ⟨rfl, hl⟩ | ⟨rfl, hl⟩ | ⟨rfl, hl⟩ | ⟨rfl, hl⟩ | ⟨rfl, hl⟩ | ⟨rfl, hl⟩ |
          ⟨rfl, hl⟩ | ⟨rfl, hl⟩ | ⟨rfl, hl⟩ | ⟨rfl, hl⟩
      · obtain rfl := List.length_eq_zero_iff.mp hl
        exact isObj_one hM
      · obtain ⟨a, b, rfl⟩ := List.length_eq_two.mp hl
        exact isObj_prod hM (hc a (by simp)) (hc b (by simp))
      · obtain rfl := List.length_eq_zero_iff.mp hl
        exact isObj_zero hM
      · obtain ⟨a, b, rfl⟩ := List.length_eq_two.mp hl
        exact isObj_coprod hM (hc a (by simp)) (hc b (by simp))
      · obtain ⟨a, b, rfl⟩ := List.length_eq_two.mp hl
        exact isObj_exp hM (hc a (by simp)) (hc b (by simp))
      · obtain rfl := List.length_eq_zero_iff.mp hl
        exact isObj_omega hM
      · obtain rfl := List.length_eq_zero_iff.mp hl
        exact isObj_nat hM
      · obtain ⟨a, rfl⟩ := List.length_eq_one_iff.mp hl
        exact isObj_list hM (hc a (by simp))
      · obtain rfl := List.length_eq_zero_iff.mp hl
        exact isObj_rose hM
      · obtain ⟨a, rfl⟩ := List.length_eq_one_iff.mp hl
        exact isObj_lrose hM (hc a (by simp))


variable (M ρ) in
/-- An environment over an object, each of whose variables' types is a type and whose arrow is
an arrow from the object to it. -/
def EnvHom (G : Globals) (n : ℕ) (X : Tree) (e : List (Tree × Tree)) : Prop :=
  IsObj M ρ X ∧ ∀ p ∈ e, Hom M ρ p.1 X p.2 ∧ IsTy G n p.2 = true

variable (M ρ) in
/-- Each primitive arrow, at types, is an arrow between its domain and its codomain. -/
def PrimsHom (G : Globals) (n : ℕ) : Prop :=
  ∀ (k : ℕ) (p : Prim), G.prims[k]? = some p →
    ∀ θ : List Tree, θ.length = p.arity → θ.all (IsTy G n) = true →
      Hom M ρ (PartialHorn.subst θ p.arrow) (PartialHorn.subst θ p.dom)
        (PartialHorn.subst θ p.cod)

variable (M ρ) in
/-- Each definition of the language's operation, at types, is an arrow from the product of its
parameters' types to its value's type, and each object definition's operation takes objects to an
object. -/
def DefsHom (G : Globals) (n : ℕ) : Prop :=
  (∀ (k : ℕ) (d : Defn), G.defs[k]? = some (.language d) →
    ∀ θ : List Tree, θ.length = d.arity → θ.all (IsTy G n) = true →
      Hom M ρ (op (G.base + k) θ) (ctxObj (d.params.map (PartialHorn.subst θ)))
        (PartialHorn.subst θ d.type)) ∧ ObjsHom M G

section

variable (hM : IsModel (ext defs) M)
include hM

/-- Extending an environment by a variable of a type keeps it an environment of arrows. -/
theorem EnvHom.ext {G : Globals} {n : ℕ} {X a : Tree} {e : List (Tree × Tree)}
    (h : EnvHom M ρ G n X e) (ha : IsObj M ρ a) (hat : IsTy G n a = true) :
    EnvHom M ρ G n (prod X a) (extEnv X a e) := by
  refine ⟨isObj_prod hM h.1 ha, fun p hp ↦ ?_⟩
  simp only [extEnv, List.mem_cons, List.mem_map] at hp
  rcases hp with rfl | ⟨q, hq, rfl⟩
  · exact ⟨snd_hom hM h.1 ha, hat⟩
  · exact ⟨comp_hom hM (fst_hom hM h.1 ha) (h.2 q hq).1, (h.2 q hq).2⟩

/-- A tuple of arrows from an object is an arrow to the product of their codomains. -/
theorem tuple_hom {X : Tree} (hX : IsObj M ρ X) :
    ∀ rs : List (Tree × Tree), (∀ r ∈ rs, Hom M ρ r.1 X r.2) →
      Hom M ρ (tuple X (rs.map Prod.fst)) X (ctxObj (rs.map Prod.snd)) :=
  List.rec (fun _ ↦ bang_hom hM hX) fun r rs ih h ↦ by
    rcases rs with _ | ⟨r', rs⟩
    · exact h r List.mem_cons_self
    · exact pair_hom hM (ih fun q hq ↦ h q (List.mem_cons_of_mem _ hq)) (h r List.mem_cons_self)

/-- A rose-tree object's fold by a step is an arrow from the object. -/
theorem roseParts_hom {t a s C : Tree} {F : Tree → Tree}
    (h : roseParts t = some (a, F)) (ha : IsObj M ρ a) (hs : Hom M ρ s (prod a (list C)) C) :
    Hom M ρ (F s) t C := by
  rcases roseParts_eq_some.mp h with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact roseRec_hom hM hs
  · exact lroseRec_hom hM ha hs

/-- A context's environment of projections is an environment of arrows. -/
theorem stdEnv_hom {G : Globals} (hO : ObjsHom M G) {n : ℕ}
    (hρ : ρ.map Sigma.fst = List.replicate n obj) :
    ∀ Γ : List Tree, Γ.all (IsTy G n) = true → EnvHom M ρ G n (ctxObj Γ) (stdEnv Γ) :=
  List.rec (fun _ ↦ ⟨isObj_one hM, by simp [stdEnv]⟩) fun a Γ ih h ↦ by
    simp only [List.all_cons, Bool.and_eq_true] at h
    have hA := isObj_of_isTy hM hO hρ a h.1
    rcases Γ with _ | ⟨b, Γ⟩
    · exact ⟨hA, by simpa [stdEnv] using ⟨idt_hom hM hA, h.1⟩⟩
    · exact (ih h.2).ext hM hA h.1

/-- The environment of a fold's start or step, the bound variables of types, is an environment of
arrows when the fold's environment is. -/
theorem envHom_foldEnvIn {G : Globals} (hO : ObjsHom M G) {n : ℕ}
    (hρ : ρ.map Sigma.fst = List.replicate n obj) {X : Tree} {bs : List Tree} {k : ℕ}
    {e : List (Tree × Tree)} {z s : Term} (he : EnvHom M ρ G n X e)
    (hbs : ∀ b ∈ bs, IsTy G n b = true) :
    EnvHom M ρ G n (foldEnvIn bs k e z s).1 (foldEnvIn bs k e z s).2 := by
  have hmem : ∀ p ∈ foldPs k e z s, p ∈ e := fun p hp ↦ by
    obtain ⟨v, -, hv⟩ := List.mem_filterMap.mp hp
    exact List.mem_of_getElem? hv
  have hΔ : (bs ++ (foldPs k e z s).map Prod.snd).all (IsTy G n) = true :=
    List.all_eq_true.mpr fun b hb ↦ by
      rcases List.mem_append.mp hb with hb | hb
      · exact hbs b hb
      · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hb
        exact (he.2 p (hmem p hp)).2
  have hstd := stdEnv_hom hM hO hρ _ hΔ
  refine ⟨hstd.1, fun p hp ↦ ?_⟩
  simp only [foldEnvIn, foldEnv, selEnv, List.mem_map, List.mem_range] at hp
  obtain ⟨i, -, rfl⟩ := hp
  cases hq : (List.idxOf? i (List.range bs.length ++
      (foldParams k e.length z s).map (· + bs.length))).bind
      (fun j ↦ (stdEnv (bs ++ (foldPs k e z s).map Prod.snd))[j]?) with
  | none => exact ⟨idt_hom hM hstd.1, isTy_ctxObj _ hΔ⟩
  | some q =>
    obtain ⟨j, -, hj⟩ := Option.bind_eq_some_iff.mp hq
    exact hstd.2 q (List.mem_of_getElem? hj)

/-- The fold of the natural numbers object at the parameters is an arrow from the environment's
object. -/
theorem natFold_hom {Γ : List Tree} {X c z s t m : Tree} (hz : Hom M ρ z (ctxObj Γ) c)
    (hs : Hom M ρ s (ctxObj (c :: Γ)) c) (ht : Hom M ρ t X (ctxObj Γ)) (hm : Hom M ρ m X nat) :
    Hom M ρ (natFold Γ c z s t m) X c := by
  rcases Γ with _ | ⟨a, Γ⟩
  · exact comp_hom hM hm (natRec_hom hM hz hs)
  · exact comp_hom hM (pair_hom hM ht hm) (natRecP_spec hM ht.isObj_cod hz hs).1

/-- The fold of a list object at the parameters is an arrow from the environment's object. -/
theorem listFold_hom {Γ : List Tree} {X a c z s t m : Tree} (ha : IsObj M ρ a)
    (hz : Hom M ρ z (ctxObj Γ) c) (hs : Hom M ρ s (ctxObj (c :: a :: Γ)) c)
    (ht : Hom M ρ t X (ctxObj Γ)) (hm : Hom M ρ m X (list a)) :
    Hom M ρ (listFold Γ a c z s t m) X c := by
  rcases Γ with _ | ⟨b, Γ⟩
  · exact comp_hom hM hm (listRec_hom hM ha hz hs)
  · exact comp_hom hM (pair_hom hM ht hm) (listRecP_spec hM ht.isObj_cod ha hz hs).1

/-- The parts of a rose-tree object are the labels and the fold of a fold with the laws of a
rose-tree object. -/
theorem roseFold_of_roseParts {t a : Tree} {F : Tree → Tree} (h : roseParts t = some (a, F))
    (ha : IsObj M ρ a) : ∃ nd, RoseFold M ρ F nd t a := by
  rcases roseParts_eq_some.mp h with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨_, roseFold_rose hM⟩
  · exact ⟨_, roseFold_lrose hM ha⟩

/-- The fold of a rose-tree object at the parameters is an arrow from the environment's
object. -/
theorem roseFold_hom {F : Tree → Tree} {nd t₀ a : Tree} (hF : RoseFold M ρ F nd t₀ a)
    {Γ : List Tree} {X c s u m : Tree} (hs : Hom M ρ s (ctxObj (prod a (list c) :: Γ)) c)
    (hu : Hom M ρ u X (ctxObj Γ)) (hm : Hom M ρ m X t₀) :
    Hom M ρ (roseFold F Γ a t₀ c s u m) X c := by
  rcases Γ with _ | ⟨b, Γ⟩
  · exact comp_hom hM hm (hF.hom hs)
  · exact comp_hom hM (pair_hom hM hu hm) (roseRecP_hom hM hF hu.isObj_cod hs)

/-- The entries of an environment at a fold's parameters are arrows of their types when the
environment's are. -/
theorem foldPs_hom {G : Globals} {n : ℕ} {X : Tree} {k : ℕ} {e : List (Tree × Tree)}
    {z s : Term} (he : EnvHom M ρ G n X e) :
    Hom M ρ (tuple X ((foldPs k e z s).map Prod.fst)) X (ctxObj ((foldPs k e z s).map Prod.snd)) :=
  tuple_hom hM he.1 _ fun r hr ↦ by
    obtain ⟨v, -, hv⟩ := List.mem_filterMap.mp hr
    exact (he.2 r (List.mem_of_getElem? hv)).1

/-- The compilation is sound: a term's arrow is an arrow from the environment's object to the
term's type, which is a type, when the environment's arrows, the primitive arrows and the
definitions' operations are arrows. -/
theorem compile_hom {G : Globals} {n : ℕ} (hG : G.WF)
    (hρ : ρ.map Sigma.fst = List.replicate n obj) (hps : PrimsHom M ρ G n)
    (hds : DefsHom M ρ G n) (s : Term) :
    ∀ (X : Tree) (e : List (Tree × Tree)) (r : Tree × Tree), compile G n s X e = some r →
      EnvHom M ρ G n X e → Hom M ρ r.1 X r.2 ∧ IsTy G n r.2 = true := by
  refine RoseTree.ind (P := fun s ↦ ∀ (X : Tree) (e : List (Tree × Tree)) (r : Tree × Tree),
    compile G n s X e = some r → EnvHom M ρ G n X e →
      Hom M ρ r.1 X r.2 ∧ IsTy G n r.2 = true) (fun l cs ih ↦ ?_) s
  intro X e r h he
  have hobj := isObj_of_isTy hM hds.2 hρ
  cases l with
  | var i =>
    obtain ⟨rfl, hi⟩ := compile_var_iff.mp h
    exact he.2 r (List.mem_of_getElem? hi)
  | star =>
    obtain ⟨rfl, rfl⟩ := compile_star_iff.mp h
    exact ⟨bang_hom hM he.1, isTy_one⟩
  | pair =>
    obtain ⟨t, u, f, a, g, b, rfl, ht, hu, rfl⟩ := compile_pair_iff.mp h
    obtain ⟨hf, hat⟩ := ih t (by simp) X e _ ht he
    obtain ⟨hg, hbt⟩ := ih u (by simp) X e _ hu he
    exact ⟨pair_hom hM hf hg, by simp [isTy_prod, hat, hbt]⟩
  | fst =>
    obtain ⟨t, f, a, b, rfl, ht, rfl⟩ := compile_fst_iff.mp h
    obtain ⟨hf, hpt⟩ := ih t (by simp) X e _ ht he
    simp only [isTy_prod, Bool.and_eq_true] at hpt
    exact ⟨comp_hom hM hf (fst_hom hM (hobj a hpt.1) (hobj b hpt.2)), hpt.1⟩
  | snd =>
    obtain ⟨t, f, a, b, rfl, ht, rfl⟩ := compile_snd_iff.mp h
    obtain ⟨hf, hpt⟩ := ih t (by simp) X e _ ht he
    simp only [isTy_prod, Bool.and_eq_true] at hpt
    exact ⟨comp_hom hM hf (snd_hom hM (hobj a hpt.1) (hobj b hpt.2)), hpt.2⟩
  | lam a =>
    obtain ⟨t, f, b, rfl, hat, ht, rfl⟩ := compile_lam_iff.mp h
    obtain ⟨hf, hbt⟩ := ih t (by simp) _ _ _ ht (he.ext hM (hobj a hat) hat)
     
    exact ⟨curry_hom hM he.1 (hobj a hat) hf, by simp [isTy_exp, hat, hbt]⟩
  | app =>
    obtain ⟨t, u, rfl, f, a, b, ht, g, hu, rfl⟩ := compile_app_iff.mp h
    obtain ⟨hf, hpt⟩ := ih t (by simp) X e _ ht he
    obtain ⟨hg, -⟩ := ih u (by simp) X e _ hu he
    simp only [isTy_exp, Bool.and_eq_true] at hpt
    exact ⟨comp_hom hM (pair_hom hM hf hg) (ev_hom hM (hobj a hpt.1) (hobj b hpt.2)), hpt.2⟩
  | arr k θ =>
    obtain ⟨t, rfl, p, hp, g, ht, hl, hθ, rfl⟩ := compile_arr_iff.mp h
    obtain ⟨hg, -⟩ := ih t (by simp) X e _ ht he
    exact ⟨comp_hom hM hg (hps k p hp θ hl hθ), isTy_subst hl hθ _ (hG.prims k p hp).2.2⟩
  | natRec =>
    obtain ⟨z, s, m, rfl, z', c, hz, s', hs, m', hm, rfl⟩ := compile_natRec_iff.mp h
    obtain ⟨hz', hct⟩ := ih z (by simp) _ _ _ hz
      (envHom_foldEnvIn hM hds.2 hρ (bs := []) he (by simp))
    obtain ⟨hs', -⟩ := ih s (by simp) _ _ _ hs
      (envHom_foldEnvIn hM hds.2 hρ he (by simpa using hct))
    obtain ⟨hm', -⟩ := ih m (by simp) X e _ hm he
    exact ⟨natFold_hom hM hz' hs' (foldPs_hom hM he) hm', hct⟩
  | listRec =>
    obtain ⟨z, s, m, rfl, m', a, hm, z', c, hz, s', hs, rfl⟩ := compile_listRec_iff.mp h
    obtain ⟨hm', hlt⟩ := ih m (by simp) X e _ hm he
    rw [isTy_list] at hlt
    obtain ⟨hz', hct⟩ := ih z (by simp) _ _ _ hz
      (envHom_foldEnvIn hM hds.2 hρ (bs := []) he (by simp))
    obtain ⟨hs', -⟩ := ih s (by simp) _ _ _ hs
      (envHom_foldEnvIn hM hds.2 hρ he (by simp [hct, hlt]))
    exact ⟨listFold_hom hM (hobj a hlt) hz' hs' (foldPs_hom hM he) hm', hct⟩
  | roseRec c =>
    obtain ⟨s, m, m', t, a, F, s', rfl, hct, hm, ht, hs, rfl⟩ := compile_roseRec_iff.mp h
    obtain ⟨hm', htt⟩ := ih m (by simp) X e _ hm he
    have hat := isTy_of_roseParts ht htt
    have hPt : IsTy G n (prod a (list c)) = true := by simp [isTy_prod, isTy_list, hat, hct]
    obtain ⟨hs', -⟩ := ih s (by simp) _ _ _ hs
      (envHom_foldEnvIn hM hds.2 hρ he (by simpa using hPt))
    obtain ⟨nd, hF⟩ := roseFold_of_roseParts hM ht (hobj a hat)
    exact ⟨roseFold_hom hM hF hs' (foldPs_hom hM he) hm', hct⟩
  | eq =>
    obtain ⟨t, u, rfl, f, a, ht, g, hu, rfl⟩ := compile_eq_iff.mp h
    obtain ⟨hf, hat⟩ := ih t (by simp) X e _ ht he
    obtain ⟨hg, -⟩ := ih u (by simp) X e _ hu he
    exact ⟨comp_hom hM (pair_hom hM hf hg) (chi_diag_hom hM (hobj a hat)), isTy_omega⟩
  | defn k θ =>
    obtain ⟨d, rs, hd, hrs, hl, hθ, hty, rfl⟩ := compile_defn_iff.mp h
    have hr : ∀ r ∈ rs, Hom M ρ r.1 X r.2 := fun r hr ↦ by
      obtain ⟨c, hc, hcr⟩ := exists_of_mapM hrs hr
      exact (ih c hc X e r hcr he).1
    have ht := tuple_hom hM he.1 rs hr
    rw [hty] at ht
    exact ⟨comp_hom hM ht (hds.1 k d hd θ hl hθ), isTy_subst hl hθ _ (hG.defs k d hd).2⟩

end

/-- The environment whose arrows are an environment's precomposed with an arrow. -/
def precomp (h : Tree) (e : List (Tree × Tree)) : List (Tree × Tree) :=
  e.map fun p ↦ (comp p.1 h, p.2)

/-- A fold's parameters' entries in an environment after an arrow are their entries after it. -/
theorem foldPs_precomp (k : ℕ) (h : Tree) (e : List (Tree × Tree)) (z s : Term) :
    foldPs k (precomp h e) z s = precomp h (foldPs k e z s) := by
  simp [foldPs, precomp, List.map_filterMap]

/-- The environments of a fold's start and step are those in an environment after an arrow. -/
theorem foldEnvIn_precomp (bs : List Tree) (k : ℕ) (h : Tree) (e : List (Tree × Tree))
    (z s : Term) : foldEnvIn bs k (precomp h e) z s = foldEnvIn bs k e z s := by
  simp only [foldEnvIn]
  rw [foldPs_precomp]
  simp [precomp, Function.comp_def]

section

variable (hM : IsModel (ext defs) M)
include hM

/-- A tuple of arrows related pointwise to precomposites with an arrow is the tuple
precomposed with it. -/
theorem eval_tuple_comp {X Y h : Tree} (hh : Hom M ρ h Y X) {rs rs' : List (Tree × Tree)}
    (hR : List.Forall₂ (fun r r' ↦ ResEq M ρ (comp r.1 h, r.2) r') rs rs')
    (hr : ∀ r ∈ rs, Hom M ρ r.1 X r.2) :
    eval M ρ (tuple Y (rs'.map Prod.fst)) = eval M ρ (comp (tuple X (rs.map Prod.fst)) h) ∧
      rs'.map Prod.snd = rs.map Prod.snd :=
  hR.rec (motive := fun rs rs' _ ↦ (∀ r ∈ rs, Hom M ρ r.1 X r.2) →
      eval M ρ (tuple Y (rs'.map Prod.fst)) = eval M ρ (comp (tuple X (rs.map Prod.fst)) h) ∧
        rs'.map Prod.snd = rs.map Prod.snd)
    (fun _ ↦ ⟨(comp_bang hM hh).symm, rfl⟩)
    (fun {r r' rs rs'} hrr hrest ih hr ↦ by
      have hrs : ∀ q ∈ rs, Hom M ρ q.1 X q.2 := fun q hq ↦ hr q (List.mem_cons_of_mem _ hq)
      obtain ⟨ih₁, ih₂⟩ := ih hrs
      refine ⟨?_, by simp [ih₂, hrr.1]⟩
      rcases hrest with _ | ⟨_, _⟩
      · exact hrr.2
      · exact (eval_op₂_congr 9 ih₁ hrr.2).trans (pair_comp hM
          (tuple_hom hM hh.isObj_cod _ hrs) (hr r List.mem_cons_self) hh).symm) hr

/-- An environment extended by a variable and precomposed with the product of an arrow with the
identity has the values of the precomposed environment extended by the variable. -/
theorem precomp_extEnv {G : Globals} {n : ℕ} {X Y h a : Tree} {e : List (Tree × Tree)}
    (he : EnvHom M ρ G n X e) (hh : Hom M ρ h Y X) (hA : IsObj M ρ a) :
    EnvEq M ρ (precomp (pair (comp h (fst Y a)) (snd Y a)) (extEnv X a e))
      (extEnv Y a (precomp h e)) := by
  have fY := fst_hom hM hh.isObj_dom hA
  have sY := snd_hom hM hh.isObj_dom hA
  have fX := fst_hom hM he.1 hA
  have hhf := comp_hom hM fY hh
  have hx := pair_hom hM hhf sY
  intro i p hp
  rcases i with _ | j
  · obtain rfl : (comp (snd X a) (pair (comp h (fst Y a)) (snd Y a)), a) = p := by
      simpa [precomp, extEnv] using hp
    exact ⟨(snd Y a, a), by simp [extEnv], rfl, (snd_pair hM hhf sY).symm⟩
  · simp only [precomp, extEnv, List.map_cons, List.getElem?_cons_succ, List.map_map,
      List.getElem?_map, Option.map_eq_some_iff, Function.comp_apply] at hp
    obtain ⟨q, hq, rfl⟩ := hp
    have hqh := (he.2 q (List.mem_of_getElem? hq)).1
    refine ⟨(comp (comp q.1 h) (fst Y a), q.2), by simp [precomp, extEnv, hq], rfl, ?_⟩
    exact ((comp_assoc hM fY hh hqh).symm.trans
      (eval_op₂_congr 3 rfl (fst_pair hM hhf sY).symm)).trans (comp_assoc hM hx fX hqh)

/-- The fold of the natural numbers object at the parameters, after an arrow, is the fold at the
tuple and the datum after it. -/
theorem eval_natFold_comp {Γ : List Tree} {X Y c z s t m h : Tree} (hz : Hom M ρ z (ctxObj Γ) c)
    (hs : Hom M ρ s (ctxObj (c :: Γ)) c) (ht : Hom M ρ t X (ctxObj Γ)) (hm : Hom M ρ m X nat)
    (hh : Hom M ρ h Y X) :
    eval M ρ (comp (natFold Γ c z s t m) h) = eval M ρ (natFold Γ c z s (comp t h) (comp m h)) := by
  rcases Γ with _ | ⟨a, Γ⟩
  · exact (comp_assoc hM hh hm (natRec_hom hM hz hs)).symm
  · exact (comp_assoc hM hh (pair_hom hM ht hm) (natRecP_spec hM ht.isObj_cod hz hs).1).symm.trans
      (eval_op₂_congr 3 rfl (pair_comp hM ht hm hh))

/-- The fold of a list object at the parameters, after an arrow, is the fold at the tuple and the
datum after it. -/
theorem eval_listFold_comp {Γ : List Tree} {X Y a c z s t m h : Tree} (ha : IsObj M ρ a)
    (hz : Hom M ρ z (ctxObj Γ) c) (hs : Hom M ρ s (ctxObj (c :: a :: Γ)) c)
    (ht : Hom M ρ t X (ctxObj Γ)) (hm : Hom M ρ m X (list a)) (hh : Hom M ρ h Y X) :
    eval M ρ (comp (listFold Γ a c z s t m) h) =
      eval M ρ (listFold Γ a c z s (comp t h) (comp m h)) := by
  rcases Γ with _ | ⟨b, Γ⟩
  · exact (comp_assoc hM hh hm (listRec_hom hM ha hz hs)).symm
  · exact (comp_assoc hM hh (pair_hom hM ht hm)
      (listRecP_spec hM ht.isObj_cod ha hz hs).1).symm.trans
      (eval_op₂_congr 3 rfl (pair_comp hM ht hm hh))

/-- The fold of a rose-tree object at the parameters, after an arrow, is the fold at the tuple
and the datum after it. -/
theorem eval_roseFold_comp {F : Tree → Tree} {nd t₀ a : Tree} (hF : RoseFold M ρ F nd t₀ a)
    {Γ : List Tree} {X Y c s u m h : Tree} (hs : Hom M ρ s (ctxObj (prod a (list c) :: Γ)) c)
    (hu : Hom M ρ u X (ctxObj Γ)) (hm : Hom M ρ m X t₀) (hh : Hom M ρ h Y X) :
    eval M ρ (comp (roseFold F Γ a t₀ c s u m) h) =
      eval M ρ (roseFold F Γ a t₀ c s (comp u h) (comp m h)) := by
  rcases Γ with _ | ⟨b, Γ⟩
  · exact (comp_assoc hM hh hm (hF.hom hs)).symm
  · exact (comp_assoc hM hh (pair_hom hM hu hm)
      (roseRecP_hom hM hF hu.isObj_cod hs)).symm.trans
      (eval_op₂_congr 3 rfl (pair_comp hM hu hm hh))

/-- The tuple of a fold's parameters' entries in an environment after an arrow is their tuple
after it, of the same types. -/
theorem eval_foldPs_precomp {G : Globals} {n : ℕ} {X Y h : Tree} {k : ℕ}
    {e : List (Tree × Tree)} {z s : Term} (he : EnvHom M ρ G n X e) (hh : Hom M ρ h Y X) :
    eval M ρ (tuple Y ((foldPs k (precomp h e) z s).map Prod.fst)) =
      eval M ρ (comp (tuple X ((foldPs k e z s).map Prod.fst)) h) ∧
      (foldPs k (precomp h e) z s).map Prod.snd = (foldPs k e z s).map Prod.snd := by
  rw [foldPs_precomp]
  refine eval_tuple_comp hM hh (List.forall₂_map_right_iff.mpr
    (List.forall₂_same.mpr fun _ _ ↦ ⟨rfl, rfl⟩)) fun r hr ↦ ?_
  obtain ⟨v, -, hv⟩ := List.mem_filterMap.mp hr
  exact (he.2 r (List.mem_of_getElem? hv)).1

/-- The compilation is natural: in an environment whose arrows are precomposed with an arrow, a
term has the same type and its arrow precomposed with it. -/
theorem compile_comp {G : Globals} {n : ℕ} (hG : G.WF)
    (hρ : ρ.map Sigma.fst = List.replicate n obj) (hps : PrimsHom M ρ G n)
    (hds : DefsHom M ρ G n) (s : Term) :
    ∀ (X : Tree) (e : List (Tree × Tree)) (r : Tree × Tree), compile G n s X e = some r →
      EnvHom M ρ G n X e → ∀ Y h, Hom M ρ h Y X →
      ∃ r', compile G n s Y (precomp h e) = some r' ∧ ResEq M ρ (comp r.1 h, r.2) r' := by
  refine RoseTree.ind (P := fun s ↦ ∀ (X : Tree) (e : List (Tree × Tree)) (r : Tree × Tree),
    compile G n s X e = some r → EnvHom M ρ G n X e → ∀ Y h, Hom M ρ h Y X →
      ∃ r', compile G n s Y (precomp h e) = some r' ∧ ResEq M ρ (comp r.1 h, r.2) r')
    (fun l cs ih ↦ ?_) s
  intro X e r hc he Y h hh
  have hobj := isObj_of_isTy hM hds.2 hρ
  have hty := compile_hom hM hG hρ hps hds
  cases l with
  | var i =>
    obtain ⟨rfl, hi⟩ := compile_var_iff.mp hc
    exact ⟨_, compile_var_iff.mpr ⟨rfl, by simp [precomp, hi]⟩, rfl, rfl⟩
  | star =>
    obtain ⟨rfl, rfl⟩ := compile_star_iff.mp hc
    exact ⟨_, compile_star_iff.mpr ⟨rfl, rfl⟩, rfl, (comp_bang hM hh).symm⟩
  | pair =>
    obtain ⟨t, u, f, a, g, b, rfl, ht, hu, rfl⟩ := compile_pair_iff.mp hc
    obtain ⟨⟨f', a'⟩, ht', rfl, hf⟩ := ih t (by simp) X e _ ht he Y h hh
    obtain ⟨⟨g', b'⟩, hu', rfl, hg⟩ := ih u (by simp) X e _ hu he Y h hh
    exact ⟨_, compile_pair_iff.mpr ⟨t, u, f', a', g', b', rfl, ht', hu', rfl⟩, rfl,
      (eval_op₂_congr 9 hf hg).trans (pair_comp hM (hty t X e _ ht he).1
        (hty u X e _ hu he).1 hh).symm⟩
  | fst =>
    obtain ⟨t, f, a, b, rfl, ht, rfl⟩ := compile_fst_iff.mp hc
    obtain ⟨⟨f', p⟩, ht', rfl, hf⟩ := ih t (by simp) X e _ ht he Y h hh
    obtain ⟨hft, hpt⟩ := hty t X e _ ht he
    simp only [isTy_prod, Bool.and_eq_true] at hpt
    exact ⟨_, compile_fst_iff.mpr ⟨t, f', a, b, rfl, ht', rfl⟩, rfl,
      (eval_op₂_congr 3 rfl hf).trans
        (comp_assoc hM hh hft (fst_hom hM (hobj a hpt.1) (hobj b hpt.2)))⟩
  | snd =>
    obtain ⟨t, f, a, b, rfl, ht, rfl⟩ := compile_snd_iff.mp hc
    obtain ⟨⟨f', p⟩, ht', rfl, hf⟩ := ih t (by simp) X e _ ht he Y h hh
    obtain ⟨hft, hpt⟩ := hty t X e _ ht he
    simp only [isTy_prod, Bool.and_eq_true] at hpt
    exact ⟨_, compile_snd_iff.mpr ⟨t, f', a, b, rfl, ht', rfl⟩, rfl,
      (eval_op₂_congr 3 rfl hf).trans
        (comp_assoc hM hh hft (snd_hom hM (hobj a hpt.1) (hobj b hpt.2)))⟩
  | lam a =>
    obtain ⟨t, f, b, rfl, hat, ht, rfl⟩ := compile_lam_iff.mp hc
    have hA := hobj a hat
    have hX := he.1
    have hY := hh.isObj_dom
    have heA := he.ext hM hA hat
    have fY := fst_hom hM hY hA
    have sY := snd_hom hM hY hA
    have fX := fst_hom hM hX hA
    have hhf := comp_hom hM fY hh
    have hx := pair_hom hM hhf sY
    obtain ⟨⟨f₁, b₁⟩, ht₁, rfl, hf₁⟩ :=
      ih t (by simp) _ _ _ ht heA _ _ hx
    obtain ⟨⟨f₂, b₂⟩, ht₂, rfl, hf₂⟩ := compile_envEq t _ _ _ ht₁ _ (precomp_extEnv hM he hh hA)
    obtain ⟨hft, -⟩ := hty t _ _ _ ht heA
    exact ⟨_, compile_lam_iff.mpr ⟨t, f₂, b₂, rfl, hat, ht₂, rfl⟩, rfl,
      (eval_op₃_congr 24 rfl rfl (hf₂.trans hf₁)).trans (curry_comp hM hA hft hh).symm⟩
  | app =>
    obtain ⟨t, u, rfl, f, a, b, ht, g, hu, rfl⟩ := compile_app_iff.mp hc
    obtain ⟨⟨f', p⟩, ht', rfl, hf⟩ := ih t (by simp) X e _ ht he Y h hh
    obtain ⟨⟨g', a'⟩, hu', rfl, hg⟩ := ih u (by simp) X e _ hu he Y h hh
    obtain ⟨hft, hpt⟩ := hty t X e _ ht he
    obtain ⟨hgt, -⟩ := hty u X e _ hu he
    simp only [isTy_exp, Bool.and_eq_true] at hpt
    have hp := pair_hom hM hft hgt
    exact ⟨_, compile_app_iff.mpr ⟨t, u, rfl, f', a', b, ht', g', hu', rfl⟩, rfl,
      ((eval_op₂_congr 3 rfl ((eval_op₂_congr 9 hf hg).trans
        (pair_comp hM hft hgt hh).symm)).trans
        (comp_assoc hM hh hp (ev_hom hM (hobj a' hpt.1) (hobj b hpt.2))))⟩
  | arr k θ =>
    obtain ⟨t, rfl, p, hp, g, ht, hl, hθ, rfl⟩ := compile_arr_iff.mp hc
    obtain ⟨⟨g', d'⟩, ht', rfl, hg⟩ := ih t (by simp) X e _ ht he Y h hh
    obtain ⟨hgt, -⟩ := hty t X e _ ht he
    exact ⟨_, compile_arr_iff.mpr ⟨t, rfl, p, hp, g', ht', hl, hθ, rfl⟩, rfl,
      (eval_op₂_congr 3 rfl hg).trans (comp_assoc hM hh hgt (hps k p hp θ hl hθ))⟩
  | natRec =>
    obtain ⟨z, s, m, rfl, z', c, hz, s', hs, m', hm, rfl⟩ := compile_natRec_iff.mp hc
    obtain ⟨hz', hct⟩ := hty z _ _ _ hz (envHom_foldEnvIn hM hds.2 hρ (bs := []) he (by simp))
    obtain ⟨hs', -⟩ := hty s _ _ _ hs (envHom_foldEnvIn hM hds.2 hρ he (by simpa using hct))
    obtain ⟨hmt, -⟩ := hty m X e _ hm he
    obtain ⟨⟨m'', t⟩, hm', rfl, hmv⟩ := ih m (by simp) X e _ hm he Y h hh
    obtain ⟨hT, hΓ⟩ := eval_foldPs_precomp hM (k := 1) (z := z) (s := s) he hh
    refine ⟨_, compile_natRec_iff.mpr ⟨z, s, m, rfl, z', c, (foldEnvIn_precomp [] 1 h e z s) ▸ hz,
      s', (foldEnvIn_precomp [c] 1 h e z s) ▸ hs, m'', hm', rfl⟩, rfl, ?_⟩
    rw [hΓ]
    exact (eval_natFold_congr _ _ _ _ hT hmv).trans
      (eval_natFold_comp hM hz' hs' (foldPs_hom hM he) hmt hh).symm
  | listRec =>
    obtain ⟨z, s, m, rfl, m', a, hm, z', c, hz, s', hs, rfl⟩ := compile_listRec_iff.mp hc
    obtain ⟨hmt, hlt⟩ := hty m X e _ hm he
    rw [isTy_list] at hlt
    obtain ⟨hz', hct⟩ := hty z _ _ _ hz (envHom_foldEnvIn hM hds.2 hρ (bs := []) he (by simp))
    obtain ⟨hs', -⟩ := hty s _ _ _ hs (envHom_foldEnvIn hM hds.2 hρ he (by simp [hct, hlt]))
    obtain ⟨⟨m'', t⟩, hm', rfl, hmv⟩ := ih m (by simp) X e _ hm he Y h hh
    obtain ⟨hT, hΓ⟩ := eval_foldPs_precomp hM (k := 2) (z := z) (s := s) he hh
    refine ⟨_, compile_listRec_iff.mpr ⟨z, s, m, rfl, m'', a, hm', z', c,
      (foldEnvIn_precomp [] 2 h e z s) ▸ hz, s', (foldEnvIn_precomp [c, a] 2 h e z s) ▸ hs, rfl⟩,
      rfl, ?_⟩
    rw [hΓ]
    exact (eval_listFold_congr _ _ _ _ _ hT hmv).trans
      (eval_listFold_comp hM (hobj a hlt) hz' hs' (foldPs_hom hM he) hmt hh).symm
  | roseRec c =>
    obtain ⟨s, m, m', t, a, F, s', rfl, hct, hm, ht, hs, rfl⟩ := compile_roseRec_iff.mp hc
    obtain ⟨hmt, htt⟩ := hty m X e _ hm he
    have hat := isTy_of_roseParts ht htt
    have hPt : IsTy G n (prod a (list c)) = true := by simp [isTy_prod, isTy_list, hat, hct]
    obtain ⟨hs', -⟩ := hty s _ _ _ hs (envHom_foldEnvIn hM hds.2 hρ he (by simpa using hPt))
    obtain ⟨nd, hF⟩ := roseFold_of_roseParts hM ht (hobj a hat)
    obtain ⟨⟨m'', t'⟩, hm', rfl, hmv⟩ := ih m (by simp) X e _ hm he Y h hh
    obtain ⟨hT, hΓ⟩ := eval_foldPs_precomp hM (k := 1) (z := Term.star) (s := s) he hh
    refine ⟨_, compile_roseRec_iff.mpr ⟨s, m, m'', _, a, F, s', rfl, hct, hm', ht,
      (foldEnvIn_precomp [prod a (list c)] 1 h e Term.star s) ▸ hs, rfl⟩, rfl, ?_⟩
    rw [hΓ]
    exact (eval_roseFold_congr _ _ _ _ _ _ hT hmv).trans
      (eval_roseFold_comp hM hF hs' (foldPs_hom hM he) hmt hh).symm
  | eq =>
    obtain ⟨t, u, rfl, f, a, ht, g, hu, rfl⟩ := compile_eq_iff.mp hc
    obtain ⟨hft, hat⟩ := hty t X e _ ht he
    obtain ⟨hgt, -⟩ := hty u X e _ hu he
    obtain ⟨⟨f', a'⟩, ht', rfl, hf⟩ := ih t (by simp) X e _ ht he Y h hh
    obtain ⟨⟨g', b'⟩, hu', rfl, hg⟩ := ih u (by simp) X e _ hu he Y h hh
    have hp := pair_hom hM hft hgt
    exact ⟨_, compile_eq_iff.mpr ⟨_, _, rfl, f', _, ht', g', hu', rfl⟩, rfl,
      (eval_op₂_congr 3 rfl ((eval_op₂_congr 9 hf hg).trans (pair_comp hM hft hgt hh).symm)).trans
        (comp_assoc hM hh hp (chi_diag_hom hM (hobj _ hat)))⟩
  | defn k θ =>
    obtain ⟨d, rs, hd, hrs, hl, hθ, htys, rfl⟩ := compile_defn_iff.mp hc
    have hr : ∀ r ∈ rs, Hom M ρ r.1 X r.2 := fun r hr ↦ by
      obtain ⟨c, hc, hcr⟩ := exists_of_mapM hrs hr
      exact (hty c X e r hcr he).1
    obtain ⟨rs', hrs', hR⟩ := mapM_lift (g := fun c ↦ compile G n c Y (precomp h e)) cs hrs
      fun c hc r hr ↦ ih c hc X e r hr he Y h hh
    obtain ⟨htu, hsn⟩ := eval_tuple_comp hM hh hR hr
    have ht := tuple_hom hM he.1 rs hr
    rw [htys] at ht
    exact ⟨_, compile_defn_iff.mpr ⟨d, rs', hd, hrs', hl, hθ, hsn.trans htys, rfl⟩, rfl,
      (eval_op₂_congr 3 rfl htu).trans
        (comp_assoc hM hh ht (hds.1 k d hd θ hl hθ))⟩

/-- The projections of a context after a tuple of arrows of its types are the arrows. -/
theorem proj_tuple {G : Globals} (hO : ObjsHom M G) {n : ℕ}
    (hρ : ρ.map Sigma.fst = List.replicate n obj) {X : Tree} (hX : IsObj M ρ X) :
    ∀ qs : List (Tree × Tree), (∀ q ∈ qs, Hom M ρ q.1 X q.2 ∧ IsTy G n q.2 = true) →
      EnvEq M ρ (precomp (tuple X (qs.map Prod.fst)) (stdEnv (qs.map Prod.snd))) qs :=
  List.rec (fun _ i p hp ↦ by simp [precomp, stdEnv] at hp) fun q qs ih hqs i p hp ↦ by
    have hq := (hqs q List.mem_cons_self).1
    rcases qs with _ | ⟨q', qs⟩
    · -- a single arrow: the identity after it
      rcases i with _ | j
      · obtain rfl : (comp (idt q.2) q.1, q.2) = p := by simpa [precomp, stdEnv, tuple] using hp
        exact ⟨q, rfl, rfl, (idt_comp hM hq).symm⟩
      · simp [precomp, stdEnv] at hp
    have hqs' : ∀ r ∈ q' :: qs, Hom M ρ r.1 X r.2 ∧ IsTy G n r.2 = true :=
      fun r hr ↦ hqs r (List.mem_cons_of_mem _ hr)
    have hT := tuple_hom hM hX (q' :: qs) fun r hr ↦ (hqs' r hr).1
    have hΓ : ((q' :: qs).map Prod.snd).all (IsTy G n) = true := by
      rw [List.all_map, List.all_eq_true]
      exact fun r hr ↦ (hqs' r hr).2
    have hstd := stdEnv_hom hM hO hρ _ hΓ
    rcases i with _ | j
    · obtain rfl : (comp (snd (ctxObj ((q' :: qs).map Prod.snd)) q.2)
          (pair (tuple X ((q' :: qs).map Prod.fst)) q.1), q.2) = p := by
        simpa [precomp, stdEnv, extEnv, tuple] using hp
      exact ⟨q, rfl, rfl, (snd_pair hM hT hq).symm⟩
    · change (precomp (pair (tuple X ((q' :: qs).map Prod.fst)) q.1)
          (extEnv (ctxObj ((q' :: qs).map Prod.snd)) q.2
            (stdEnv ((q' :: qs).map Prod.snd))))[j + 1]? = some p at hp
      simp only [precomp, extEnv, List.map_cons, List.getElem?_cons_succ, List.map_map,
        List.getElem?_map, Option.map_eq_some_iff, Function.comp_apply] at hp
      obtain ⟨p₀, hp₀, rfl⟩ := hp
      obtain ⟨q₀, hq₀, h₂, h₁⟩ :=
        ih hqs' j (comp p₀.1 (tuple X ((q' :: qs).map Prod.fst)), p₀.2)
          (by simp only [precomp, List.map_cons] at hp₀ ⊢; simp [hp₀])
      have hp₀h := (hstd.2 p₀ (List.mem_of_getElem? hp₀)).1
      refine ⟨q₀, by simpa using hq₀, h₂, h₁.trans ?_⟩
      exact (eval_op₂_congr 3 rfl (fst_pair hM hT hq).symm).trans
        (comp_assoc hM (pair_hom hM hT hq) (fst_hom hM hT.isObj_cod hq.isObj_cod) hp₀h)

end

end Typing

end Geb.FreeTopos.Internal

end
