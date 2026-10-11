/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
-- Modified from geb-mathlib by scripts/geb-mathlib-backport.patch.
module

public import Geb.Prototypes.FreeTopos.Internal.Inversion

set_option doc.verso true in
/-!
# The parameters of folds

A fold of the natural numbers or of a list compiles its start and its step over the product of
the types of its parameters, the variables of its context either mentions
({name}`Geb.FreeTopos.Internal.foldParams`), in an environment whose parameters are the
projections of that product and whose other variables below them are placeholders
({name}`Geb.FreeTopos.Internal.selEnv`). This module states the syntactic facts the compilation's
laws rest on: a term that compiles mentions only variables of its environment
({lit}`compile_occurs_lt`); a renaming by a strictly increasing map renames a fold's parameters
({lit}`foldParams_rename`), and the substitution of objects leaves the variables a term mentions
({lit}`occurs_osubst`); the environment of a fold's start and step has a parameter's projection at
its index and a placeholder at each other index below them ({lit}`getElem?_selEnv_of_mem`,
{lit}`getElem?_selEnv_of_not_mem`), and is the environment of the projections of the bound
variables' types when the fold has no parameters ({lit}`foldEnvIn_closed`). A rose-tree fold has a
step and no start, and its parameters are those of a fold whose start is the element of the
terminal object, which mentions no variable ({lit}`occurs_star`).

## Main statements

* {lit}`compile_occurs_lt` — a term that compiles mentions only variables of its environment.
* {lit}`foldParams_rename`, {lit}`occurs_osubst` — a fold's parameters after a strictly increasing
  renaming, and the variables a term mentions after a substitution of objects.
* {lit}`getElem?_selEnv_of_mem`, {lit}`getElem?_selEnv_of_not_mem` — the entries of a
  parameters' environment.
* {lit}`foldEnvIn_closed` — the environments of a fold without parameters.

## Tags

internal language, fold, parameter, free variable
-/

set_option doc.verso true

@[expose] public section

namespace Geb.FreeTopos.Internal

open PartialHorn (Tree)

/-- The types of a context's environment of projections are the context's. -/
theorem map_snd_stdEnv : ∀ Γ : List Tree, (stdEnv Γ).map Prod.snd = Γ :=
  List.rec rfl fun a Γ ih ↦ by
    rcases Γ with _ | ⟨b, Γ⟩
    · rfl
    · change (extEnv (ctxObj (b :: Γ)) a (stdEnv (b :: Γ))).map Prod.snd = a :: b :: Γ
      simp only [extEnv, List.map_cons, List.map_map]
      exact congrArg (a :: ·) ((List.map_congr_left fun _ _ ↦ rfl).trans ih)

/-- Each index of a parameters' environment is below its number of variables. -/
theorem lt_selBound {w : ℕ} (ws : List ℕ) : w ∈ ws → w < selBound ws :=
  ws.rec (motive := fun ws ↦ w ∈ ws → w < selBound ws) (fun hw ↦ by simp at hw)
    fun v ws ih hw ↦ by
      simp only [selBound] at ih ⊢
      rcases List.mem_cons.mp hw with rfl | hw
      · exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_max_left _ _)
      · exact Nat.lt_of_lt_of_le (ih hw) (Nat.le_max_right _ _)

/-- The number of variables of a parameters' environment is at most a bound of its indices. -/
theorem selBound_le {N : ℕ} (ws : List ℕ) : (∀ w ∈ ws, w < N) → selBound ws ≤ N :=
  ws.rec (motive := fun ws ↦ (∀ w ∈ ws, w < N) → selBound ws ≤ N) (fun _ ↦ Nat.zero_le _)
    fun v ws ih h ↦ by
      simp only [selBound] at ih ⊢
      exact Nat.max_le.mpr
        ⟨h v List.mem_cons_self, ih fun w hw ↦ h w (List.mem_cons_of_mem _ hw)⟩

/-- The number of variables of a parameters' environment. -/
theorem length_selEnv (ws : List ℕ) (P : Tree) (E : List (Tree × Tree)) :
    (selEnv ws P E).length = selBound ws := by
  simp [selEnv]

/-- A fold's parameters are the variables below the bound that its start or its step
mentions. -/
theorem mem_foldParams {k N i : ℕ} {z s : Term} :
    i ∈ foldParams k N z s ↔ i < N ∧ (Term.occurs z i || Term.occurs s (i + k)) = true := by
  simp [foldParams]

/-- The environment of a fold's start or step has at most the variables it binds besides those of
the fold's environment. -/
theorem length_foldEnvIn_le (bs : List Tree) (k : ℕ) (e : List (Tree × Tree)) (z s : Term) :
    (foldEnvIn bs k e z s).2.length ≤ e.length + bs.length := by
  simp only [foldEnvIn, foldEnv, length_selEnv]
  refine selBound_le _ fun w hw ↦ ?_
  rcases List.mem_append.mp hw with hw | hw
  · exact Nat.lt_of_lt_of_le (List.mem_range.mp hw) (Nat.le_add_left _ _)
  · obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hw
    exact Nat.add_lt_add_right (mem_foldParams.mp hv).1 _

/-- The entry of a parameters' environment at an index below its number of variables. -/
theorem getElem?_selEnv (ws : List ℕ) (P : Tree) (E : List (Tree × Tree)) {i : ℕ}
    (hi : i < selBound ws) :
    (selEnv ws P E)[i]? = some (((ws.idxOf? i).bind (E[·]?)).getD (idt P, P)) := by
  simp [selEnv, hi]

/-- The position of an element of an increasing list. -/
theorem idxOf?_of_pairwise {ws : List ℕ} (hw : ws.Pairwise (· < ·)) {j : ℕ}
    (hj : j < ws.length) : ws.idxOf? ws[j] = some j :=
  List.rec (motive := fun ws ↦ ws.Pairwise (· < ·) → ∀ j (hj : j < ws.length),
      ws.idxOf? ws[j] = some j)
    (fun _ j hj ↦ (Nat.not_lt_zero j hj).elim)
    (fun w ws ih hw j hj ↦ by
      rw [List.pairwise_cons] at hw
      rcases j with _ | j
      · simp only [List.getElem_cons_zero, List.idxOf?_cons, beq_self_eq_true, ↓reduceIte]
      · have hj' : j < ws.length := Nat.lt_of_succ_lt_succ hj
        have hne : (w == ws[j]) = false := Bool.eq_false_iff.mpr fun h ↦
          Nat.ne_of_lt (hw.1 _ (List.getElem_mem hj')) (beq_iff_eq.mp h)
        simp only [List.getElem_cons_succ, List.idxOf?_cons, hne, Bool.false_eq_true, ↓reduceIte,
          ih hw.2 j hj', Option.map_some])
    ws hw j hj

/-- A parameters' environment of increasing indices has at each index the entry of its
position. -/
theorem getElem?_selEnv_of_mem {ws : List ℕ} (hw : ws.Pairwise (· < ·)) (P : Tree)
    (E : List (Tree × Tree)) {j : ℕ} (hj : j < ws.length) :
    (selEnv ws P E)[ws[j]]? = some ((E[j]?).getD (idt P, P)) := by
  rw [getElem?_selEnv _ _ _ (lt_selBound _ (List.getElem_mem hj)), idxOf?_of_pairwise hw hj,
    Option.bind_some]

/-- A parameters' environment has a placeholder at each variable below its number of variables
other than its indices. -/
theorem getElem?_selEnv_of_not_mem {ws : List ℕ} (P : Tree) (E : List (Tree × Tree)) {w : ℕ}
    (hw : w ∉ ws) (hb : w < selBound ws) : (selEnv ws P E)[w]? = some (idt P, P) := by
  rw [getElem?_selEnv _ _ _ hb, List.idxOf?_eq_none_iff.mpr hw]
  rfl

/-- A strictly increasing map takes a variable below the number of variables of a parameters'
environment below that of the environment of the mapped indices. -/
theorem lt_selBound_map {f : ℕ → ℕ} (hf : StrictMono f) {i : ℕ} (ws : List ℕ) :
    i < selBound ws → f i < selBound (ws.map f) :=
  ws.rec (motive := fun ws ↦ i < selBound ws → f i < selBound (ws.map f))
    (fun h ↦ (Nat.not_lt_zero _ h).elim) fun v ws ih h ↦ by
      simp only [selBound, List.map_cons, List.foldr_cons] at ih h ⊢
      by_cases hv : i < v + 1
      · have hfv : f i ≤ f v := by
          rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hv) with hiv | rfl
          · exact Nat.le_of_lt (hf hiv)
          · exact Nat.le_refl _
        exact Nat.lt_of_lt_of_le (Nat.lt_succ_of_le hfv) (Nat.le_max_left _ _)
      · exact Nat.lt_of_lt_of_le (ih (by omega)) (Nat.le_max_right _ _)

/-- The parameters' environment of the indices mapped by a strictly increasing map has at a
mapped variable the entry of the variable. -/
theorem getElem?_selEnv_map {f : ℕ → ℕ} (hf : StrictMono f) (ws : List ℕ) (P : Tree)
    (E : List (Tree × Tree)) {i : ℕ} (hi : i < selBound ws) :
    (selEnv (ws.map f) P E)[f i]? = (selEnv ws P E)[i]? := by
  have hb : (fun x ↦ f x == f i) = fun x ↦ x == i :=
    funext fun x ↦ Bool.eq_iff_iff.mpr (by simp [hf.injective.eq_iff])
  rw [getElem?_selEnv _ _ _ (lt_selBound_map hf ws hi), getElem?_selEnv _ _ _ hi]
  simp only [List.idxOf?, List.findIdx?_map, Function.comp_def, hb]

/-- The entries of an environment at a list of its indices, at a position, are the entry at the
index of that position. -/
theorem getElem?_filterMap_getElem? {e : List (Tree × Tree)} (vs : List ℕ) :
    (∀ v ∈ vs, v < e.length) →
      ∀ j : ℕ, (vs.filterMap fun v : ℕ ↦ e[v]?)[j]? = (vs[j]?).bind fun v : ℕ ↦ e[v]? :=
  vs.rec (fun _ _ ↦ rfl) fun v vs ih h j ↦ by
    obtain ⟨p, hp⟩ : ∃ p, e[v]? = some p :=
      ⟨_, List.getElem?_eq_getElem (h v List.mem_cons_self)⟩
    rw [List.filterMap_cons, hp]
    rcases j with _ | j
    · simp [hp]
    · simp only [List.getElem?_cons_succ]
      exact ih (fun w hw ↦ h w (List.mem_cons_of_mem _ hw)) j

/-- The numbers below a bound, in order, increase. -/
theorem pairwise_lt_range (N : ℕ) : (List.range N).Pairwise (· < ·) :=
  List.pairwise_iff_getElem.mpr fun i j _ _ hij ↦ by
    simp only [List.getElem_range]
    exact hij

/-- Two increasing lists of numbers with the same elements are equal. -/
theorem eq_of_pairwise_lt (l₁ : List ℕ) :
    ∀ l₂ : List ℕ, l₁.Pairwise (· < ·) → l₂.Pairwise (· < ·) → (∀ a, a ∈ l₁ ↔ a ∈ l₂) → l₁ = l₂ :=
  l₁.rec (fun l₂ _ _ h ↦ match l₂, h with
      | [], _ => rfl
      | b :: _, h => (List.not_mem_nil ((h b).mpr List.mem_cons_self)).elim)
    fun a l₁ ih l₂ h₁ h₂ h ↦ match l₂, h₂, h with
      | [], _, h => (List.not_mem_nil ((h a).mp List.mem_cons_self)).elim
      | b :: l₂, h₂, h => by
        rw [List.pairwise_cons] at h₁ h₂
        -- the heads are the least elements of the two lists
        have hab : a = b := by
          rcases List.mem_cons.mp ((h a).mp List.mem_cons_self) with hab | hab
          · exact hab
          rcases List.mem_cons.mp ((h b).mpr List.mem_cons_self) with hba | hba
          · exact hba.symm
          exact (Nat.lt_irrefl _ (Nat.lt_trans (h₂.1 a hab) (h₁.1 b hba))).elim
        subst hab
        refine congrArg (a :: ·) (ih l₂ h₁.2 h₂.2 fun x ↦ ⟨fun hx ↦ ?_, fun hx ↦ ?_⟩)
        · rcases List.mem_cons.mp ((h x).mp (List.mem_cons_of_mem _ hx)) with rfl | hx'
          · exact (Nat.lt_irrefl _ (h₁.1 x hx)).elim
          · exact hx'
        · rcases List.mem_cons.mp ((h x).mpr (List.mem_cons_of_mem _ hx)) with rfl | hx'
          · exact (Nat.lt_irrefl _ (h₂.1 x hx)).elim
          · exact hx'

/-- A list of variables a predicate selects below one bound is that below another, when the
bounds agree at each variable it selects. -/
theorem filter_range_congr {N N' : ℕ} {p : ℕ → Bool} (h : ∀ i, p i = true → (i < N ↔ i < N')) :
    (List.range N).filter p = (List.range N').filter p :=
  eq_of_pairwise_lt _ _ ((pairwise_lt_range _).filter _)
    ((pairwise_lt_range _).filter _) fun i ↦ by
      simp only [List.mem_filter, List.mem_range]
      exact ⟨fun ⟨hl, hp⟩ ↦ ⟨(h i hp).mp hl, hp⟩, fun ⟨hl, hp⟩ ↦ ⟨(h i hp).mpr hl, hp⟩⟩

/-- The variables a predicate selects, after a strictly increasing map, are those the image
predicate selects, when the map takes each selected variable below the new bound. -/
theorem filter_range_map {N N' : ℕ} {p q : ℕ → Bool} {f : ℕ → ℕ} (hf : StrictMono f)
    (hq : ∀ j, q j = true ↔ ∃ i, p i = true ∧ f i = j)
    (hN : ∀ i, p i = true → i < N ∧ f i < N') :
    (List.range N').filter q = ((List.range N).filter p).map f :=
  eq_of_pairwise_lt _ _ ((pairwise_lt_range _).filter _)
    (List.pairwise_map.mpr (((pairwise_lt_range _).filter _).imp fun h ↦ hf h)) fun j ↦ by
      simp only [List.mem_filter, List.mem_range, List.mem_map, hq]
      constructor
      · rintro ⟨-, i, hi, rfl⟩
        exact ⟨i, ⟨(hN i hi).1, hi⟩, rfl⟩
      · rintro ⟨i, ⟨-, hi⟩, rfl⟩
        exact ⟨(hN i hi).2, i, hi, rfl⟩

/-- The entries of two environments at a list of indices of the first are related pointwise
when each entry of the first at them is related to the second's. -/
theorem forall₂_filterMap {R : Tree × Tree → Tree × Tree → Prop} {e e' : List (Tree × Tree)}
    (vs : List ℕ) :
    (∀ v ∈ vs, v < e.length) → (∀ v ∈ vs, ∀ p, e[v]? = some p → ∃ q, e'[v]? = some q ∧ R p q) →
      List.Forall₂ R (vs.filterMap fun v : ℕ ↦ e[v]?) (vs.filterMap fun v : ℕ ↦ e'[v]?) :=
  vs.rec (fun _ _ ↦ .nil) fun v vs ih hlt h ↦ by
    have hv := List.getElem?_eq_getElem (hlt v List.mem_cons_self)
    obtain ⟨q, hq, hR⟩ := h v List.mem_cons_self _ hv
    rw [List.filterMap_cons, List.filterMap_cons, hv, hq]
    exact .cons hR (ih (fun w hw ↦ hlt w (List.mem_cons_of_mem _ hw))
      fun w hw ↦ h w (List.mem_cons_of_mem _ hw))

/-- The environments of a fold's start and step in an environment are those in one of the same
types at the variables the fold mentions, when it mentions only variables of the first. -/
theorem foldEnvIn_retype {k : ℕ} {z s : Term} {e e' : List (Tree × Tree)}
    (hlt : ∀ i, (Term.occurs z i || Term.occurs s (i + k)) = true → i < e.length)
    (he : ∀ i, (Term.occurs z i || Term.occurs s (i + k)) = true →
      (e'[i]?).map Prod.snd = (e[i]?).map Prod.snd) (bs : List Tree) :
    foldEnvIn bs k e' z s = foldEnvIn bs k e z s := by
  have hV : foldParams k e'.length z s = foldParams k e.length z s :=
    filter_range_congr fun i hi ↦ by
      have h' := he i hi
      rw [List.getElem?_eq_getElem (hlt i hi), Option.map_some] at h'
      obtain ⟨q, hq, -⟩ := Option.map_eq_some_iff.mp h'
      exact ⟨fun _ ↦ hlt i hi, fun _ ↦ (List.getElem?_eq_some_iff.mp hq).1⟩
  have hT : (foldPs k e' z s).map Prod.snd = (foldPs k e z s).map Prod.snd := by
    simp only [foldPs, hV, List.map_filterMap]
    exact List.filterMap_congr fun v hv ↦ he v (mem_foldParams.mp hv).2
  simp only [foldEnvIn, hV, hT]

/-- Lifting a strictly increasing renaming under a binder keeps it strictly increasing. -/
theorem strictMono_liftR {f : ℕ → ℕ} (hf : StrictMono f) : StrictMono (Term.liftR f) := by
  intro a b hab
  rcases a with _ | a <;> rcases b with _ | b
  · exact (Nat.lt_irrefl 0 hab).elim
  · exact Nat.succ_pos _
  · exact (Nat.not_lt_zero _ hab).elim
  · exact Nat.succ_lt_succ (hf (Nat.lt_of_succ_lt_succ hab))

/-- The environments of a fold's start and step after a strictly increasing renaming {lit}`g`
of their variables are those before it at the renamed variables, when the renamed fold's
parameters are the renamings of the fold's, of the same types, and {lit}`g` takes the bound
variables to themselves and each parameter to its renaming. -/
theorem foldEnvIn_rename {bs : List Tree} {k : ℕ} {e e' : List (Tree × Tree)}
    {z s z₁ s₁ : Term} {f g : ℕ → ℕ} (hg : StrictMono g)
    (hV : foldParams k e.length z₁ s₁ = (foldParams k e'.length z s).map f)
    (hT : (foldPs k e z₁ s₁).map Prod.snd = (foldPs k e' z s).map Prod.snd)
    (hgw : (List.range bs.length ++ (foldParams k e'.length z s).map (· + bs.length)).map g =
      List.range bs.length ++ ((foldParams k e'.length z s).map f).map (· + bs.length)) :
    (foldEnvIn bs k e z₁ s₁).1 = (foldEnvIn bs k e' z s).1 ∧
      ∀ i < (foldEnvIn bs k e' z s).2.length,
        (foldEnvIn bs k e z₁ s₁).2[g i]? = (foldEnvIn bs k e' z s).2[i]? := by
  simp only [foldEnvIn, foldEnv, hV, hT, ← hgw]
  exact ⟨trivial, fun i hi ↦ getElem?_selEnv_map hg _ _ _ (by rwa [length_selEnv] at hi)⟩

/-- The indices of a fold's start's or step's environment, the bound variables before the
parameters, increase. -/
theorem pairwise_foldWs (k : ℕ) (vs : List ℕ) (hv : vs.Pairwise (· < ·)) :
    (List.range k ++ vs.map (· + k)).Pairwise (· < ·) :=
  List.pairwise_append.mpr ⟨pairwise_lt_range k,
    List.pairwise_map.mpr (hv.imp fun h ↦ Nat.add_lt_add_right h k),
    fun a ha b hb ↦ by
      obtain ⟨v, -, rfl⟩ := List.mem_map.mp hb
      exact Nat.lt_of_lt_of_le (List.mem_range.mp ha) (Nat.le_add_left _ _)⟩

/-- The environment over the product of the types of an environment's entries at increasing
indices of it, whose variables there are its projections, has at those indices the entries'
types. -/
theorem selEnv_types {E : List (Tree × Tree)} {ws : List ℕ} (hw : ws.Pairwise (· < ·))
    (hlt : ∀ w ∈ ws, w < E.length) :
    ∀ i ∈ ws, ((selEnv ws (ctxObj ((ws.filterMap fun w : ℕ ↦ E[w]?).map Prod.snd))
      (stdEnv ((ws.filterMap fun w : ℕ ↦ E[w]?).map Prod.snd)))[i]?).map Prod.snd =
      (E[i]?).map Prod.snd := by
  intro i hi
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hi
  have hqj : (ws.filterMap fun w : ℕ ↦ E[w]?)[j]? = E[ws[j]]? := by
    rw [getElem?_filterMap_getElem? ws hlt j, List.getElem?_eq_getElem hj, Option.bind_some]
  have h₁ := congrArg (·[j]?) (map_snd_stdEnv ((ws.filterMap fun w : ℕ ↦ E[w]?).map Prod.snd))
  simp only [List.getElem?_map, hqj] at h₁
  rw [getElem?_selEnv_of_mem hw _ _ hj]
  obtain ⟨p, hp⟩ : ∃ p, E[ws[j]]? = some p :=
    ⟨_, List.getElem?_eq_getElem (hlt _ (List.getElem_mem hj))⟩
  rw [hp, Option.map_some] at h₁ ⊢
  obtain ⟨p₀, hp₀, h₀⟩ := Option.map_eq_some_iff.mp h₁
  rw [hp₀, Option.getD_some, Option.map_some, h₀]

/-- The environment of a fold's start or step has at its indices the types of an environment's
entries there, when those are the bound types before the parameters' types. -/
theorem foldEnvIn_types {E : List (Tree × Tree)} {bs : List Tree} {k : ℕ}
    {e : List (Tree × Tree)} {z s : Term} {Q : List (Tree × Tree)}
    (hlt : ∀ w ∈ List.range bs.length ++ (foldParams k e.length z s).map (· + bs.length),
      w < E.length)
    (hQ : (List.range bs.length ++ (foldParams k e.length z s).map (· + bs.length)).filterMap
      (fun w : ℕ ↦ E[w]?) = Q)
    (hT : Q.map Prod.snd = bs ++ (foldPs k e z s).map Prod.snd) :
    ∀ i ∈ List.range bs.length ++ (foldParams k e.length z s).map (· + bs.length),
      ((foldEnvIn bs k e z s).2[i]?).map Prod.snd = (E[i]?).map Prod.snd := by
  have h := selEnv_types (E := E)
    (ws := List.range bs.length ++ (foldParams k e.length z s).map (· + bs.length))
    (pairwise_foldWs bs.length _ ((pairwise_lt_range _).filter _)) hlt
  rw [hQ, hT] at h
  exact h

/-- The indices of a fold's start's environment are variables of the fold's environment. -/
theorem foldWs_start_lt (k : ℕ) (e : List (Tree × Tree)) (z s : Term) :
    ∀ w ∈ List.range ([] : List Tree).length ++
      (foldParams k e.length z s).map (· + ([] : List Tree).length), w < e.length :=
  fun w hw ↦ by simpa using (mem_foldParams.mp (by simpa using hw)).1

/-- The entries of a fold's environment at its start's environment's indices are its
parameters'. -/
theorem foldWs_start_filterMap (k : ℕ) (e : List (Tree × Tree)) (z s : Term) :
    (List.range ([] : List Tree).length ++
      (foldParams k e.length z s).map (· + ([] : List Tree).length)).filterMap
        (fun w : ℕ ↦ e[w]?) = foldPs k e z s := by
  simp [foldPs]

/-- The indices of a natural-number fold's step's environment are variables of the fold's
environment extended by the value. -/
theorem foldWs_nat_lt (X c : Tree) (e : List (Tree × Tree)) (z s : Term) :
    ∀ w ∈ List.range [c].length ++ (foldParams 1 e.length z s).map (· + [c].length),
      w < (extEnv X c e).length := fun w hw ↦ by
  simp only [List.length_cons, List.length_nil, List.mem_append, List.mem_range,
    List.mem_map] at hw
  rcases hw with hw | ⟨v, hv, rfl⟩
  · simp [extEnv]; omega
  · simpa [extEnv] using (mem_foldParams.mp hv).1

/-- The entries of a natural-number fold's environment extended by the value at its step's
environment's indices are the value's and its parameters'. -/
theorem foldWs_nat_filterMap (X c : Tree) (e : List (Tree × Tree)) (z s : Term) :
    (List.range [c].length ++ (foldParams 1 e.length z s).map (· + [c].length)).filterMap
      (fun w : ℕ ↦ (extEnv X c e)[w]?) = extEnv X c (foldPs 1 e z s) := by
  simp [foldPs, extEnv, List.filterMap_map, List.map_filterMap]

/-- The indices of a list fold's step's environment are variables of the fold's environment
extended by the element and the value. -/
theorem foldWs_list_lt (X a c : Tree) (e : List (Tree × Tree)) (z s : Term) :
    ∀ w ∈ List.range [c, a].length ++ (foldParams 2 e.length z s).map (· + [c, a].length),
      w < (extEnv (prod X a) c (extEnv X a e)).length := fun w hw ↦ by
  simp only [List.length_cons, List.length_nil, List.mem_append, List.mem_range,
    List.mem_map] at hw
  rcases hw with hw | ⟨v, hv, rfl⟩
  · simp [extEnv]; omega
  · simpa [extEnv] using (mem_foldParams.mp hv).1

/-- The entries of a list fold's environment extended by the element and the value at its step's
environment's indices are the value's, the element's and its parameters'. -/
theorem foldWs_list_filterMap (X a c : Tree) (e : List (Tree × Tree)) (z s : Term) :
    (List.range [c, a].length ++ (foldParams 2 e.length z s).map (· + [c, a].length)).filterMap
      (fun w : ℕ ↦ (extEnv (prod X a) c (extEnv X a e))[w]?) =
      extEnv (prod X a) c (extEnv X a (foldPs 2 e z s)) := by
  simp [foldPs, extEnv, List.filterMap_map, List.map_filterMap, List.range_succ]

/-- List types of equal types have equal element types. -/
theorem list_inj {a a' : Tree} (h : list a = list a') : a = a' := by
  have h₁ := listPart_eq_some.mpr h
  rw [listPart_eq_some.mpr rfl] at h₁
  simpa using h₁

/-- The element of the terminal object mentions no variable. -/
theorem occurs_star (d : ℕ) : Term.occurs Term.star d = false := by
  rw [Term.star, Term.occurs_node]
  rfl

/-- A variable of the environment a rose-tree fold's step mentions is one the fold mentions. -/
theorem occurs_roseRec_of_step {c : Tree} {s m : Term} {i : ℕ}
    (hi : (Term.occurs Term.star i || Term.occurs s (i + 1)) = true) :
    Term.occurs (RoseTree.node (.roseRec c) [s, m]) i = true := by
  simp only [occurs_star, Bool.false_or] at hi
  simp only [Term.occurs_node, Term.occursStep, List.map_cons, List.map_nil, hi, Bool.true_or]

/-- The substitution of objects leaves the element of the terminal object. -/
theorem osubst_star (θ : List Tree) : Term.osubst θ Term.star = Term.star := by
  rw [Term.star, Term.osubst_node]
  rfl

/-- The substitution of objects leaves the variables a term mentions. -/
theorem occurs_osubst (θ : List Tree) :
    ∀ (t : Term) (d : ℕ), Term.occurs (Term.osubst θ t) d = Term.occurs t d :=
  RoseTree.ind fun l cs ih d ↦ by
    have h : cs.map (fun c ↦ (Term.osubst θ c, Term.occurs (Term.osubst θ c))) =
        cs.map (fun c ↦ (Term.osubst θ c, Term.occurs c)) :=
      List.map_congr_left fun c hc ↦ by rw [funext (ih c hc)]
    rw [Term.osubst_node, Term.occurs_node, Term.occurs_node, List.map_map, Function.comp_def, h]
    cases l <;> rcases cs with _ | ⟨c₁, _ | ⟨c₂, _ | ⟨c₃, _ | ⟨c₄, cs⟩⟩⟩⟩ <;>
      simp [Term.occursStep, Label.osubst, List.any_map, Function.comp_def]

/-- The number of variables of a parameters' environment of the first indices is their
number. -/
theorem selBound_range (N : ℕ) : selBound (List.range N) = N :=
  Nat.le_antisymm (selBound_le _ fun _ hw ↦ List.mem_range.mp hw)
    (match N with
      | 0 => Nat.zero_le _
      | N + 1 => Nat.succ_le_of_lt (lt_selBound _ (List.mem_range.mpr (Nat.lt_succ_self N))))

/-- A parameters' environment of the first indices, as many as an environment's entries, is that
environment. -/
theorem selEnv_range {N : ℕ} (P : Tree) {E : List (Tree × Tree)} (hE : E.length = N) :
    selEnv (List.range N) P E = E := by
  refine List.ext_getElem? fun i ↦ ?_
  by_cases hi : i < N
  · have hidx : (List.range N).idxOf? i = some i := by
      have h := idxOf?_of_pairwise (j := i) (pairwise_lt_range N) (by simpa using hi)
      rwa [List.getElem_range] at h
    rw [getElem?_selEnv _ _ _ (by rwa [selBound_range]), hidx]
    simp [List.getElem?_eq_getElem (hE ▸ hi : i < E.length)]
  · rw [List.getElem?_eq_none (by simp [length_selEnv, selBound_range]; omega),
      List.getElem?_eq_none (by omega)]

/-- A fold that mentions no variable of its environment has no parameters' entries. -/
theorem foldPs_closed {k : ℕ} {e : List (Tree × Tree)} {z s : Term}
    (h : foldParams k e.length z s = []) : foldPs k e z s = [] := by
  simp [foldPs, h]

/-- A fold that mentions no variable of its environment compiles its start and step in the
environments of the projections of their bound types. -/
theorem foldEnvIn_closed {k : ℕ} {e : List (Tree × Tree)} {z s : Term}
    (h : foldParams k e.length z s = []) (bs : List Tree) :
    foldEnvIn bs k e z s = (ctxObj bs, stdEnv bs) := by
  simp only [foldEnvIn, foldEnv, h, foldPs_closed h, List.map_nil, List.append_nil]
  rw [selEnv_range _ (by simpa using congrArg List.length (map_snd_stdEnv bs))]

/-- An entry of a parameters' environment is an entry of the environment it selects from or the
placeholder of its object. -/
theorem mem_selEnv {ws : List ℕ} {P : Tree} {E : List (Tree × Tree)} {p : Tree × Tree}
    (hp : p ∈ selEnv ws P E) : p ∈ E ∨ p = (idt P, P) := by
  simp only [selEnv, List.mem_map] at hp
  obtain ⟨i, -, rfl⟩ := hp
  cases h : (ws.idxOf? i).bind (E[·]?) with
  | none => exact .inr (by simp only [Option.getD_none])
  | some q =>
    obtain ⟨j, -, hj⟩ := Option.bind_eq_some_iff.mp h
    exact .inl (by simpa only [h, Option.getD_some] using List.mem_of_getElem? hj)

/-- A parameters' entry of an environment is an entry of it. -/
theorem mem_of_mem_foldPs {k : ℕ} {e : List (Tree × Tree)} {z s : Term} {p : Tree × Tree}
    (hp : p ∈ foldPs k e z s) : p ∈ e := by
  obtain ⟨i, -, hi⟩ := List.mem_filterMap.mp hp
  exact List.mem_of_getElem? hi

variable {G : Globals} {n : ℕ}

/-- A child of a list of terms each of which compiles compiles. -/
theorem compile_of_mapM {cs : List Term} {X : Tree} {e : List (Tree × Tree)}
    {rs : List (Tree × Tree)} (h : cs.mapM (fun c ↦ compile G n c X e) = some rs) {c : Term}
    (hc : c ∈ cs) : ∃ r, compile G n c X e = some r := by
  rw [PartialHorn.mapM_eq_some_iff] at h
  obtain ⟨r, -, hr⟩ := List.mem_map.mp (h ▸ List.mem_map_of_mem hc :
    compile G n c X e ∈ rs.map some)
  exact ⟨r, hr.symm⟩

/-- A term that compiles mentions only variables of its environment. -/
theorem compile_occurs_lt (t : Term) :
    ∀ (X : Tree) (e : List (Tree × Tree)) (r : Tree × Tree), compile G n t X e = some r →
      ∀ i, Term.occurs t i = true → i < e.length := by
  refine RoseTree.ind (P := fun t ↦ ∀ (X : Tree) (e : List (Tree × Tree)) (r : Tree × Tree),
    compile G n t X e = some r → ∀ i, Term.occurs t i = true → i < e.length) (fun l cs ih ↦ ?_) t
  intro X e r h i hi
  -- a child compiled in the node's environment
  have same : ∀ c ∈ cs, ∀ r, compile G n c X e = some r → Term.occurs c i = true → i < e.length :=
    fun c hc r hr ↦ ih c hc X e r hr i
  cases l with
  | var j =>
    obtain ⟨rfl, hj⟩ := compile_var_iff.mp h
    simp only [Term.occurs_node, Term.occursStep, beq_iff_eq] at hi
    subst hi
    exact (List.getElem?_eq_some_iff.mp hj).1
  | star =>
    obtain ⟨rfl, -⟩ := compile_star_iff.mp h
    simp [Term.occurs_node, Term.occursStep] at hi
  | pair =>
    obtain ⟨t, u, _, _, _, _, rfl, ht, hu, -⟩ := compile_pair_iff.mp h
    simp only [Term.occurs_node, Term.occursStep, List.map_cons, List.map_nil, List.any_cons,
      List.any_nil, Bool.or_false, Bool.or_eq_true] at hi
    rcases hi with hi | hi
    · exact same t (by simp) _ ht hi
    · exact same u (by simp) _ hu hi
  | fst =>
    obtain ⟨t, _, _, _, rfl, ht, -⟩ := compile_fst_iff.mp h
    simp only [Term.occurs_node, Term.occursStep, List.map_cons, List.map_nil, List.any_cons,
      List.any_nil, Bool.or_false] at hi
    exact same t (by simp) _ ht hi
  | snd =>
    obtain ⟨t, _, _, _, rfl, ht, -⟩ := compile_snd_iff.mp h
    simp only [Term.occurs_node, Term.occursStep, List.map_cons, List.map_nil, List.any_cons,
      List.any_nil, Bool.or_false] at hi
    exact same t (by simp) _ ht hi
  | lam a =>
    obtain ⟨t, _, _, rfl, -, ht, -⟩ := compile_lam_iff.mp h
    simp only [Term.occurs_node, Term.occursStep, List.map_cons, List.map_nil] at hi
    simpa [extEnv] using ih t (by simp) _ _ _ ht (i + 1) hi
  | app =>
    obtain ⟨t, u, rfl, _, _, _, ht, _, hu, -⟩ := compile_app_iff.mp h
    simp only [Term.occurs_node, Term.occursStep, List.map_cons, List.map_nil, List.any_cons,
      List.any_nil, Bool.or_false, Bool.or_eq_true] at hi
    rcases hi with hi | hi
    · exact same t (by simp) _ ht hi
    · exact same u (by simp) _ hu hi
  | arr k θ =>
    obtain ⟨t, rfl, _, -, _, ht, -⟩ := compile_arr_iff.mp h
    simp only [Term.occurs_node, Term.occursStep, List.map_cons, List.map_nil, List.any_cons,
      List.any_nil, Bool.or_false] at hi
    exact same t (by simp) _ ht hi
  | natRec =>
    obtain ⟨z, s, m, rfl, _, _, hz, _, hs, _, hm, -⟩ := compile_natRec_iff.mp h
    simp only [Term.occurs_node, Term.occursStep, List.map_cons, List.map_nil,
      Bool.or_eq_true] at hi
    rcases hi with (hi | hi) | hi
    · exact Nat.lt_of_lt_of_le (ih z (by simp) _ _ _ hz i hi)
        (length_foldEnvIn_le [] 1 e z s)
    · have := Nat.lt_of_lt_of_le (ih s (by simp) _ _ _ hs (i + 1) hi)
        (length_foldEnvIn_le [_] 1 e z s)
      simpa using this
    · exact same m (by simp) _ hm hi
  | listRec =>
    obtain ⟨z, s, m, rfl, _, _, hm, _, _, hz, _, hs, -⟩ := compile_listRec_iff.mp h
    simp only [Term.occurs_node, Term.occursStep, List.map_cons, List.map_nil,
      Bool.or_eq_true] at hi
    rcases hi with (hi | hi) | hi
    · exact Nat.lt_of_lt_of_le (ih z (by simp) _ _ _ hz i hi)
        (length_foldEnvIn_le [] 2 e z s)
    · have := Nat.lt_of_lt_of_le (ih s (by simp) _ _ _ hs (i + 2) hi)
        (length_foldEnvIn_le [_, _] 2 e z s)
      simpa using this
    · exact same m (by simp) _ hm hi
  | roseRec c =>
    obtain ⟨s, m, _, _, _, _, _, rfl, -, hm, -, hs, -⟩ := compile_roseRec_iff.mp h
    simp only [Term.occurs_node, Term.occursStep, List.map_cons, List.map_nil,
      Bool.or_eq_true] at hi
    rcases hi with hi | hi
    · have := Nat.lt_of_lt_of_le (ih s (by simp) _ _ _ hs (i + 1) hi)
        (length_foldEnvIn_le [_] 1 e Term.star s)
      simpa using this
    · exact same m (by simp) _ hm hi
  | eq =>
    obtain ⟨t, u, rfl, _, _, ht, _, hu, -⟩ := compile_eq_iff.mp h
    simp only [Term.occurs_node, Term.occursStep, List.map_cons, List.map_nil, List.any_cons,
      List.any_nil, Bool.or_false, Bool.or_eq_true] at hi
    rcases hi with hi | hi
    · exact same t (by simp) _ ht hi
    · exact same u (by simp) _ hu hi
  | defn k θ =>
    obtain ⟨_, rs, -, hrs, -⟩ := compile_defn_iff.mp h
    simp only [Term.occurs_node, Term.occursStep, List.any_map, List.any_eq_true,
      Function.comp_apply] at hi
    obtain ⟨c, hc, hi⟩ := hi
    obtain ⟨r, hr⟩ := compile_of_mapM hrs hc
    exact same c hc r hr hi

/-- A fold whose mentioned variables are below an environment's length, renamed by a strictly
increasing map into an environment that has at each renamed variable the first's entry, has as
parameters the renamings of its parameters, of the same entries. -/
theorem foldParams_rename_of_lt {k : ℕ} {z s : Term} {e e' : List (Tree × Tree)} {f : ℕ → ℕ}
    (hlt : ∀ i, (Term.occurs z i || Term.occurs s (i + k)) = true → i < e'.length)
    (hf : ∀ i < e'.length, e[f i]? = e'[i]?) (hmono : StrictMono f) (z₁ s₁ : Term)
    (hq : ∀ j, (Term.occurs z₁ j || Term.occurs s₁ (j + k)) = true ↔
      ∃ i, (Term.occurs z i || Term.occurs s (i + k)) = true ∧ f i = j) :
    foldParams k e.length z₁ s₁ = (foldParams k e'.length z s).map f ∧
      foldPs k e z₁ s₁ = foldPs k e' z s := by
  have hV : foldParams k e.length z₁ s₁ = (foldParams k e'.length z s).map f :=
    filter_range_map hmono hq fun i hi ↦ by
      have hfi := hf i (hlt i hi)
      rw [List.getElem?_eq_getElem (hlt i hi)] at hfi
      exact ⟨hlt i hi, (List.getElem?_eq_some_iff.mp hfi).1⟩
  refine ⟨hV, ?_⟩
  unfold foldPs
  rw [hV, List.filterMap_map]
  exact List.filterMap_congr fun v hv ↦ hf v (mem_foldParams.mp hv).1

/-- A fold that compiles in an environment, renamed by a strictly increasing map into an
environment that has at each renamed variable the first's entry, has as parameters the renamings
of its parameters, of the same entries. -/
theorem foldParams_rename {k : ℕ} {l : Label} {z s m : Term} {X : Tree}
    {e e' : List (Tree × Tree)} {r : Tree × Tree} {f : ℕ → ℕ}
    (h : compile G n (RoseTree.node l [z, s, m]) X e' = some r)
    (hl : ∀ i, (Term.occurs z i || Term.occurs s (i + k)) = true →
      Term.occurs (RoseTree.node l [z, s, m]) i = true)
    (hf : ∀ i < e'.length, e[f i]? = e'[i]?) (hmono : StrictMono f) (z₁ s₁ : Term)
    (hq : ∀ j, (Term.occurs z₁ j || Term.occurs s₁ (j + k)) = true ↔
      ∃ i, (Term.occurs z i || Term.occurs s (i + k)) = true ∧ f i = j) :
    foldParams k e.length z₁ s₁ = (foldParams k e'.length z s).map f ∧
      foldPs k e z₁ s₁ = foldPs k e' z s :=
  foldParams_rename_of_lt (fun i hi ↦ compile_occurs_lt _ X e' r h i (hl i hi)) hf hmono z₁ s₁ hq

end Geb.FreeTopos.Internal

end
