/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.FreeTopos.Internal.Prove
public import Geb.Prototypes.FreeTopos.Internal.Soundness

set_option doc.verso true in
/-!
# The prover's reductions check

The rewriting derivation a reduction of the prover computes is one the checker
{name}`Geb.FreeTopos.Internal.check` accepts, rewriting the term to the reduction's result: the
innermost normalization ({name}`Geb.FreeTopos.Internal.normalize`) and the reduction to a depth
({name}`Geb.FreeTopos.Internal.eval`) at every fuel. A step of conversion that names a reduction
therefore needs only the reduction's result, which a checker can compute without checking the
derivation, and is sound by the soundness of the derivation the reduction computes.

The derivations are built of the identity, the composition of two rewritings, the congruence over
a node's children and the rewriting at the root by one rule. A result is marked when it rewrites:
an unmarked result is the term itself, by the identity derivation, and a marked one's derivation
is not the identity's. The congruence the checker reads rewrites every child in the node's context
where each child outside it has the identity derivation, and otherwise in the contexts
{name}`Geb.FreeTopos.Internal.childCtxs` computes, which the prover uses where it rewrites inside
abstractions and the starts and steps of folds; by the marks, the two agree on every result the
prover computes.

## Main definitions

* {lit}`Checked` — a result of a reduction is checked.
* {lit}`RedChecked`, {lit}`EvalChecked` — a reduction's results are checked, and a reduction's
  to a depth at every depth.

## Main statements

* {lit}`checked_trans`, {lit}`checked_cong` — composition and congruence preserve checked
  results.
* {lit}`normalize_checked` — the innermost normalization's results are checked.
* {lit}`eval_checked` — the reduction's results are checked at every depth.

## Tags

internal language, prover, normalization, derivation, checker
-/

set_option doc.verso true

@[expose] public section

namespace Geb.FreeTopos.Internal

open PartialHorn (Tree)

variable {G : Globals} {E : Array Entry} {n : ℕ}

/-- A result of a reduction at a term in a context under hypotheses is checked: its derivation
rewrites the term to the result, an unmarked result is the term itself by the identity
derivation, and a marked result's derivation is not the identity's. -/
structure Checked (G : Globals) (E : Array Entry) (n : ℕ) (Γ : List Tree) (Φ : List Term)
    (t : Term) (r : Term × Deriv × Bool) : Prop where
  /-- The derivation rewrites the term to the result. -/
  check : (check G E n r.2.1).1 Γ Φ t = some r.1
  /-- An unmarked result is the term itself by the identity derivation. -/
  unmarked : r.2.2 = false → r.1 = t ∧ r.2 = dRefl
  /-- A marked result's derivation is not the identity's. -/
  marked : r.2.2 = true → r.2.1.label.isRefl = false

/-- The identity derivation of a term is checked. -/
theorem checked_refl (Γ : List Tree) (Φ : List Term) (t : Term) :
    Checked G E n Γ Φ t (t, dRefl) where
  check := by simp [dRefl, check_node, checkStep]
  unmarked _ := ⟨rfl, rfl⟩
  marked h := nomatch h

/-- An unmarked checked result is checked in every context. -/
theorem Checked.of_unmarked {Γ Δ : List Tree} {Φ Ψ : List Term} {t : Term}
    {r : Term × Deriv × Bool} (h : Checked G E n Γ Φ t r) (hb : r.2.2 = false) :
    Checked G E n Δ Ψ t r := by
  obtain ⟨t', d⟩ := r
  obtain ⟨rfl, rfl⟩ := h.unmarked hb
  exact checked_refl Δ Ψ t'

/-- The composition of two checked rewritings is checked. -/
theorem checked_trans {Γ : List Tree} {Φ : List Term} {t t₁ t₂ : Term} {d₁ d₂ : Deriv × Bool}
    (h₁ : Checked G E n Γ Φ t (t₁, d₁)) (h₂ : Checked G E n Γ Φ t₁ (t₂, d₂)) :
    Checked G E n Γ Φ t (t₂, dTrans d₁ d₂) := by
  obtain ⟨d₁, b₁⟩ := d₁
  obtain ⟨d₂, b₂⟩ := d₂
  cases b₁ with
  | false =>
    obtain ⟨rfl, -⟩ := h₁.unmarked rfl
    exact h₂
  | true => cases b₂ with
    | false =>
      obtain ⟨rfl, -⟩ := h₂.unmarked rfl
      exact h₁
    | true =>
      refine ⟨?_, fun h ↦ (nomatch h), fun _ ↦ rfl⟩
      simp only [dTrans, check_node, checkStep, List.map_cons, List.map_nil]
      rw [h₁.check]
      exact h₂.check

/-- A rule rewriting a term at its root is no identity, composition or congruence, and its leaf
derivation rewrites the term as the rule does. -/
theorem check_leaf {Γ : List Tree} {Φ : List Term} {l : Rule} {t t' : Term}
    (h : rootStep G E n Γ Φ l t = some t') :
    (check G E n (RoseTree.node l [])).1 Γ Φ t = some t' ∧ l.isRefl = false := by
  cases l <;> first
    | (simp [rootStep] at h; done)
    | exact ⟨by simpa [check_node, checkStep] using h, rfl⟩

/-- A rule the prover tries at a term's root rewrites it by a leaf derivation, of a rule of the
language rewriting the term to the result. -/
theorem tryRule_spec {Γ : List Tree} {Φ : List Term} {t t' : Term} {r : NormRule} {d : Deriv}
    (h : tryRule G E n Γ Φ t r = some (t', d)) :
    ∃ l, d = RoseTree.node l [] ∧ rootStep G E n Γ Φ l t = some t' := by
  have leaf (l : Rule)
      (h : (rootStep G E n Γ Φ l t).map (fun t' ↦ (t', RoseTree.node l [])) = some (t', d)) :
      ∃ l, d = RoseTree.node l [] ∧ rootStep G E n Γ Φ l t = some t' := by
    obtain ⟨u, hu, he⟩ := Option.map_eq_some_iff.mp h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
    exact ⟨l, rfl, hu⟩
  cases r with
  | rule => exact leaf _ h
  | delta | deltaBelow | unitVar =>
    simp only [tryRule] at h
    split at h
    · split at h
      · exact leaf _ h
      · cases h
    · cases h
  | thm =>
    simp only [tryRule, Option.bind_eq_bind] at h
    obtain ⟨_, -, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨_, -, h⟩ := Option.bind_eq_some_iff.mp h
    split at h
    · cases h
    · obtain ⟨_, -, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨_, -, h⟩ := Option.bind_eq_some_iff.mp h
      exact leaf _ h
  | thmAt =>
    simp only [tryRule, Option.bind_eq_bind] at h
    split at h
    · cases h
    · obtain ⟨_, -, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨_, -, h⟩ := Option.bind_eq_some_iff.mp h
      exact leaf _ h
  | hyp => exact leaf _ h

/-- The first rule that rewrites a term at its root rewrites it by a checked result. -/
theorem rootRewrite_checked {rs : List NormRule} {Γ : List Tree} {Φ : List Term} {t t' : Term}
    {d : Deriv} (h : rootRewrite G E n rs Γ Φ t = some (t', d)) :
    Checked G E n Γ Φ t (t', d, true) := by
  obtain ⟨r, -, hr⟩ := List.exists_of_findSome?_eq_some h
  obtain ⟨l, rfl, hl⟩ := tryRule_spec hr
  obtain ⟨hc, hrefl⟩ := check_leaf hl
  exact ⟨hc, fun h ↦ (nomatch h), fun _ ↦ hrefl⟩

/-- The congruence over a node's children, each rewritten by a checked result in its context
among those the checker reads, is checked. -/
theorem checked_cong {Γ : List Tree} {Φ : List Term} {l : Label} {ts : List Term}
    {rs : List (Term × Deriv × Bool)} {Γs : List (List Tree × List Term)}
    (hΓs : congCtxs G n l ts Γ Φ (rs.map (·.2.1)) = some Γs) (hl : rs.length = ts.length)
    (hΓl : Γs.length = ts.length)
    (h : ∀ (i : ℕ) (h₁ : i < rs.length) (h₂ : i < Γs.length) (h₃ : i < ts.length),
      Checked G E n Γs[i].1 Γs[i].2 ts[i] rs[i]) :
    Checked G E n Γ Φ (RoseTree.node l ts)
      (RoseTree.node l (rs.map (·.1)), dCong (rs.map (·.2))) := by
  unfold dCong
  split
  · refine ⟨?_, fun h ↦ (nomatch h), fun _ ↦ rfl⟩
    simp only [check_node, checkStep, List.map_map, RoseTree.label_node, RoseTree.children_node,
      Function.comp_def, hΓs, Option.bind_eq_bind, Option.bind_some, List.length_map, hl, hΓl,
      and_self, ite_true]
    have hm : ((rs.map fun x ↦ (x.2.1, check G E n x.2.1)).zip (Γs.zip ts)).mapM
        (fun x ↦ x.1.2.1 x.2.1.1 x.2.1.2 x.2.2) = some (rs.map (·.1)) := by
      refine (PartialHorn.mapM_eq_some_iff _ _).mpr (List.ext_getElem (by simp [hl, hΓl]) ?_)
      intro i h₁ h₂
      simp only [List.length_map, List.length_zip, hl, hΓl, min_self] at h₁
      simpa using (h i (hl ▸ h₁) (hΓl ▸ h₁) h₁).check
    rw [hm]
    rfl
  · rename_i hm
    simp only [List.any_eq_true, List.mem_map, not_exists, not_and] at hm
    have hts : rs.map (·.1) = ts := List.ext_getElem (by simp [hl]) fun i h₁ h₂ ↦ by
      simp only [List.length_map] at h₁
      have hb : rs[i].2.2 = false :=
        Bool.eq_false_iff.mpr (hm rs[i].2 ⟨rs[i], List.getElem_mem h₁, rfl⟩)
      simpa using ((h i h₁ (hΓl ▸ h₂) h₂).unmarked hb).1
    rw [hts]
    exact checked_refl Γ Φ _

/-- The congruence over a node's children, each rewritten by a checked result in the node's
context, each child outside it unmarked, is checked. -/
theorem checked_cong_same {Γ : List Tree} {Φ : List Term} {l : Label} {ts : List Term}
    {rs : List (Term × Deriv × Bool)} (hl : rs.length = ts.length)
    (hs : ∀ (i : ℕ) (h₁ : i < rs.length), sameCtx l i = false → rs[i].2.2 = false)
    (h : ∀ (i : ℕ) (h₁ : i < rs.length) (h₃ : i < ts.length), Checked G E n Γ Φ ts[i] rs[i]) :
    Checked G E n Γ Φ (RoseTree.node l ts)
      (RoseTree.node l (rs.map (·.1)), dCong (rs.map (·.2))) := by
  have hall : ((rs.map (·.2.1)).zipIdx.all fun (d, i) ↦ sameCtx l i || d.label.isRefl) = true := by
    refine List.all_eq_true.mpr fun ⟨d, i⟩ hd ↦ ?_
    obtain ⟨hi, rfl⟩ := List.getElem?_eq_some_iff.mp (List.mk_mem_zipIdx_iff_getElem?.mp hd)
    simp only [List.length_map] at hi
    cases hsi : sameCtx l i with
    | true => simp [hsi]
    | false =>
      obtain ⟨-, hd⟩ := (h i hi (hl ▸ hi)).unmarked (hs i hi hsi)
      simp [hd, dRefl, Rule.isRefl]
  refine checked_cong (Γs := ts.map fun _ ↦ (Γ, Φ)) (by simp [congCtxs, hall]) hl (by simp)
    fun i h₁ _ h₃ ↦ ?_
  simpa using h i h₁ h₃

/-- The congruence over a node's children, each rewritten by a checked result in the context
{name}`Geb.FreeTopos.Internal.childCtxs` gives it, is checked. -/
theorem checked_cong_child {Γ : List Tree} {Φ : List Term} {l : Label} {ts : List Term}
    {rs : List (Term × Deriv × Bool)} {Γs : List (List Tree × List Term)}
    (hc' : childCtxs G n l ts Γ Φ = some Γs) (hl : rs.length = ts.length)
    (h : ∀ (i : ℕ) (h₁ : i < rs.length) (h₂ : i < Γs.length) (h₃ : i < ts.length),
      Checked G E n Γs[i].1 Γs[i].2 ts[i] rs[i]) :
    Checked G E n Γ Φ (RoseTree.node l ts)
      (RoseTree.node l (rs.map (·.1)), dCong (rs.map (·.2))) := by
  have hΓl := childCtxs_length hc'
  by_cases hall : ((rs.map (·.2.1)).zipIdx.all fun (d, i) ↦ sameCtx l i || d.label.isRefl) = true
  · refine checked_cong (Γs := ts.map fun _ ↦ (Γ, Φ)) (by simp [congCtxs, hall]) hl (by simp)
      fun i h₁ _ h₃ ↦ ?_
    simp only [List.getElem_map]
    have hi := List.all_eq_true.mp hall ((rs.map (·.2.1))[i]'(by simpa using h₁), i)
      (List.mk_mem_zipIdx_iff_getElem?.mpr (List.getElem?_eq_getElem _))
    cases hsi : sameCtx l i with
    | true =>
      have hc := h i h₁ (hΓl ▸ h₃) h₃
      rwa [childCtxs_sameCtx hc' (List.getElem?_eq_getElem (hΓl ▸ h₃)) hsi] at hc
    | false =>
      simp only [hsi, Bool.false_or, List.getElem_map] at hi
      have hb : rs[i].2.2 = false := by
        cases hb : rs[i].2.2 with
        | false => rfl
        | true => simp [(h i h₁ (hΓl ▸ h₃) h₃).marked hb] at hi
      exact (h i h₁ (hΓl ▸ h₃) h₃).of_unmarked hb
  · exact checked_cong (by simp [congCtxs, hall, hc']) hl hΓl h

/-- A reduction's results are checked wherever it computes one. -/
def RedChecked (G : Globals) (E : Array Entry) (n : ℕ)
    (r : List Tree → List Term → Term → Option (Term × Deriv × Bool)) : Prop :=
  ∀ (Γ : List Tree) (Φ : List Term) (t : Term) (x : Term × Deriv × Bool),
    r Γ Φ t = some x → Checked G E n Γ Φ t x

/-- The reductions of a node's children in their contexts, where each is computed, are one for
each child, each the reduction of its child. -/
theorem mapM_zip_spec {rec : List Tree → List Term → Term → Option (Term × Deriv × Bool)}
    {Γs : List (List Tree × List Term)} {ts : List Term} {cs : List (Term × Deriv × Bool)}
    (h : (Γs.zip ts).mapM (fun x ↦ rec x.1.1 x.1.2 x.2) = some cs)
    (hΓl : Γs.length = ts.length) :
    cs.length = ts.length ∧ ∀ (i : ℕ) (h₁ : i < cs.length) (h₂ : i < Γs.length)
      (h₃ : i < ts.length), rec Γs[i].1 Γs[i].2 ts[i] = some cs[i] := by
  have hm := (PartialHorn.mapM_eq_some_iff _ _).mp h
  have hl : cs.length = ts.length := by
    simpa [hΓl] using (congrArg List.length hm).symm
  refine ⟨hl, fun i h₁ h₂ h₃ ↦ ?_⟩
  have := List.getElem_of_eq hm (by simpa [hΓl] using h₃)
  simpa using this

/-- One step of the innermost normalization, its subterms normalized by a reduction whose
results are checked, computes checked results. -/
theorem normStep_checked {rs : List NormRule}
    {rec : List Tree → List Term → Term → Option (Term × Deriv × Bool)}
    (hrec : RedChecked G E n rec) : RedChecked G E n (normStep G E n rs rec) := by
  intro Γ Φ t x h
  simp only [normStep, Option.bind_eq_bind] at h
  obtain ⟨Γs, hΓs, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨cs, hcs, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨hl, hpt⟩ := mapM_zip_spec hcs (childCtxs_length hΓs)
  have hd : (if (cs.any fun x ↦ x.2.2) = true then
      (RoseTree.node Rule.cong (cs.map fun x ↦ x.2.1), true) else dRefl) =
      dCong (cs.map (·.2)) := by
    rw [dCong, List.any_map, List.map_map]
    rfl
  have h₁ : Checked G E n Γ Φ t
      (RoseTree.node t.label (cs.map Prod.fst), dCong (cs.map (·.2))) := by
    have := checked_cong_child (G := G) (E := E) hΓs hl fun i h₁ h₂ h₃ ↦
      hrec _ _ _ _ (hpt i h₁ h₂ h₃)
    rwa [RoseTree.node_label_children] at this
  rw [hd] at h
  split at h
  · rename_i t₂ dr hr
    obtain ⟨⟨t₃, d₃⟩, h₃, h⟩ := Option.bind_eq_some_iff.mp h
    simp only [pure, Option.some.injEq] at h
    subst h
    exact checked_trans h₁ (checked_trans (rootRewrite_checked hr) (hrec _ _ _ _ h₃))
  · simp only [pure, Option.some.injEq] at h
    subst h
    exact h₁

/-- The innermost normalization's results are checked, at every fuel. -/
theorem normalize_checked (rs : List NormRule) (fuel : ℕ) :
    RedChecked G E n (normalize G E n rs fuel) :=
  Nat.rec (motive := fun f ↦ RedChecked G E n (normalize G E n rs f))
    (fun Γ Φ t x h ↦ by
      simp only [normalize, Option.some.injEq] at h
      subst h
      exact checked_refl Γ Φ t)
    (fun _ ih ↦ normStep_checked ih) fuel

/-- A reduction to a depth whose results are checked at every depth. -/
def EvalChecked (G : Globals) (E : Array Entry) (n : ℕ) (rec : Reduction) : Prop :=
  ∀ dp : Depth, RedChecked G E n (rec dp)

/-- The rewriting at the root after a checked rewriting, its result reduced by a reduction whose
results are checked, computes a checked result. -/
theorem atRoot_checked {rs : List NormRule} {rec : Reduction} (hrec : EvalChecked G E n rec)
    {Γ : List Tree} {Φ : List Term} {dp : Depth} {t t₁ : Term} {d₁ : Deriv × Bool}
    (h₁ : Checked G E n Γ Φ t (t₁, d₁)) {x : Term × Deriv × Bool}
    (h : atRoot G E n rs rec Γ Φ dp t₁ d₁ = some x) : Checked G E n Γ Φ t x := by
  simp only [atRoot, Option.bind_eq_bind] at h
  split at h
  · rename_i t₂ dr hr
    obtain ⟨⟨t₃, d₃⟩, h₃, h⟩ := Option.bind_eq_some_iff.mp h
    simp only [pure, Option.some.injEq] at h
    subst h
    exact checked_trans h₁ (checked_trans (rootRewrite_checked hr) (hrec _ _ _ _ _ h₃))
  · simp only [pure, Option.some.injEq] at h
    subst h
    exact h₁

/-- The child a weak head normal form reduces before a rule at a node's root is in the node's
context. -/
theorem headChild_same {l : Label} {cs : List Term} {i : ℕ} (h : headChild l cs = some i) :
    sameCtx l i = true := by
  unfold headChild at h
  split at h <;> first
    | (simp only [Option.some.injEq] at h; subst h; rfl)
    | cases h

/-- The congruence rewriting one child of a node in the node's context by a checked result, the
others by the identity, is checked. -/
theorem checked_set {Γ : List Tree} {Φ : List Term} {l : Label} {cs : List Term} {i : ℕ}
    {c c' : Term} {dc : Deriv × Bool} (hs : sameCtx l i = true) (hi : cs[i]? = some c)
    (hc : Checked G E n Γ Φ c (c', dc)) :
    Checked G E n Γ Φ (RoseTree.node l cs) (RoseTree.node l (cs.set i c'),
      dCong ((List.range cs.length).map fun j ↦ if j = i then dc else dRefl)) := by
  let rs := cs.zipIdx.map fun (u, j) ↦ if j = i then (c', dc) else (u, dRefl)
  have hrs (j : ℕ) (hj : j < rs.length) : rs[j] = if j = i then (c', dc) else
      (cs[j]'(by simpa [rs] using hj), dRefl) := by
    simp [rs, List.getElem_zipIdx]
  have h₁ : rs.map (·.1) = cs.set i c' := List.ext_getElem (by simp [rs]) fun j h₁ h₂ ↦ by
    rw [List.getElem_map, hrs j (by simpa using h₁), List.getElem_set]
    by_cases hji : j = i
    · subst hji
      simp
    · simp [hji, Ne.symm hji]
  have h₂ : rs.map (·.2) = (List.range cs.length).map fun j ↦ if j = i then dc else dRefl :=
    List.ext_getElem (by simp [rs]) fun j h₁ h₂ ↦ by
      rw [List.getElem_map, hrs j (by simpa using h₁)]
      split <;> simp_all
  rw [← h₁, ← h₂]
  refine checked_cong_same (by simp [rs]) (fun j hj hsj ↦ ?_) fun j hj hj' ↦ ?_
  · rw [hrs j hj]
    split
    · simp_all
    · rfl
  · rw [hrs j hj]
    split
    · rename_i hji
      subst hji
      rw [List.getElem?_eq_getElem hj', Option.some.injEq] at hi
      rw [hi]
      exact hc
    · exact checked_refl Γ Φ _

/-- The results of a function computed at each element of a list, where each is computed, are
one for each element, each the function's value there. -/
theorem mapM_spec {α β : Type} {f : α → Option β} {l : List α} {cs : List β}
    (h : l.mapM f = some cs) :
    cs.length = l.length ∧ ∀ (i : ℕ) (h₁ : i < cs.length) (h₂ : i < l.length),
      f l[i] = some cs[i] := by
  have hm := (PartialHorn.mapM_eq_some_iff _ _).mp h
  have hl : cs.length = l.length := by simpa using (congrArg List.length hm).symm
  refine ⟨hl, fun i h₁ h₂ ↦ ?_⟩
  have := List.getElem_of_eq hm (by simpa using h₂)
  rwa [List.getElem_map, List.getElem_map] at this

/-- The children of a node the weak normal form reduces are in the node's context, or the
children's contexts are all the node's. -/
theorem weak_shape {G : Globals} {n : ℕ} {l : Label} {ts : List Term} {Γ : List Tree}
    {Φ : List Term} :
    (∀ i < ts.length, sameCtx l i = true ∨ keepsWeak l i = true) ∨
      childCtxs G n l ts Γ Φ = some (ts.map fun _ ↦ (Γ, Φ)) := by
  cases l with
  | lam => exact .inl fun _ _ ↦ .inr rfl
  | natRec | listRec =>
    refine .inl fun i _ ↦ ?_
    match i with
    | 0 | 1 => exact .inr rfl
    | _ + 2 => exact .inl rfl
  | roseRec c =>
    match ts with
    | [] => exact .inl fun _ hi ↦ (Nat.not_lt_zero _ hi).elim
    | [_] => exact .inl fun i hi ↦ match i, hi with | 0, _ => .inr rfl
    | [_, _] => exact .inl fun i hi ↦ match i, hi with
      | 0, _ => .inr rfl
      | 1, _ => .inl rfl
    | _ :: _ :: _ :: _ => exact .inr (by simp [childCtxs])
  | _ => exact .inl fun _ _ ↦ .inl rfl

/-- The contexts in which a congruence reads the children of a node the weak normal form reduces
are all the node's, where every child it leaves in place has the identity derivation. -/
theorem congCtxs_weak {l : Label} {ts : List Term} {Γ : List Tree} {Φ : List Term}
    {ds : List Deriv} (hlen : ds.length = ts.length)
    (h : ∀ (i : ℕ) (hi : i < ds.length), keepsWeak l i = true → ds[i].label.isRefl = true) :
    congCtxs G n l ts Γ Φ ds = some (ts.map fun _ ↦ (Γ, Φ)) := by
  rcases weak_shape (G := G) (n := n) (l := l) (ts := ts) (Γ := Γ) (Φ := Φ) with hs | hc
  · have hall : (ds.zipIdx.all fun (d, i) ↦ sameCtx l i || d.label.isRefl) = true := by
      refine List.all_eq_true.mpr fun ⟨d, i⟩ hd ↦ ?_
      obtain ⟨hi, rfl⟩ := List.getElem?_eq_some_iff.mp (List.mk_mem_zipIdx_iff_getElem?.mp hd)
      rcases hs i (hlen ▸ hi) with hsi | hk
      · simp [hsi]
      · simp [h i hi hk]
    simp [congCtxs, hall]
  · unfold congCtxs
    split
    · rfl
    · exact hc

/-- One step of the weak head normal form, its subterms reduced by a reduction whose results are
checked, computes checked results. -/
theorem headStep_checked {rs : List NormRule} {rec : Reduction} (hrec : EvalChecked G E n rec) :
    RedChecked G E n (headStep G E n rs rec) := by
  intro Γ Φ t x h
  simp only [headStep, Option.bind_eq_bind] at h
  split at h
  · rename_i f u hl hc
    have ht : t = Term.app f u := by
      rw [← RoseTree.node_label_children t, hl, hc]
      rfl
    subst ht
    obtain ⟨⟨f', df⟩, hf, h⟩ := Option.bind_eq_some_iff.mp h
    have hcf := hrec _ _ _ _ _ hf
    have app {u' : Term} {du : Deriv × Bool} (hu : Checked G E n Γ Φ u (u', du))
        (ha : atRoot G E n rs rec Γ Φ .head (Term.app f' u') (dCong [df, du]) = some x) :
        Checked G E n Γ Φ (Term.app f u) x :=
      atRoot_checked hrec (checked_cong_same (l := .app) (ts := [f, u])
        (rs := [(f', df), (u', du)]) rfl (fun _ _ h ↦ by simp [sameCtx] at h)
        fun i h₁ _ ↦ match i, h₁ with
          | 0, _ => hcf
          | 1, _ => hu) ha
    split at h
    · split at h
      · obtain ⟨⟨u', du⟩, hu, h⟩ := Option.bind_eq_some_iff.mp h
        simp only [Option.some.injEq, Prod.mk.injEq] at hu
        obtain ⟨rfl, rfl⟩ := hu
        exact app (checked_refl Γ Φ u) h
      · obtain ⟨⟨u', du⟩, hu, h⟩ := Option.bind_eq_some_iff.mp h
        exact app (hrec _ _ _ _ _ hu) h
    · obtain ⟨⟨u', du⟩, hu, h⟩ := Option.bind_eq_some_iff.mp h
      exact app (hrec _ _ _ _ _ hu) h
  · split at h
    · rename_i t₁ dr hr
      obtain ⟨⟨t₂, d₂⟩, h₂, h⟩ := Option.bind_eq_some_iff.mp h
      simp only [pure, Option.some.injEq] at h
      subst h
      exact checked_trans (rootRewrite_checked hr) (hrec _ _ _ _ _ h₂)
    · split at h
      · simp only [Option.some.injEq] at h
        subst h
        exact checked_refl Γ Φ t
      · rename_i i hi
        obtain ⟨c, hc, h⟩ := Option.bind_eq_some_iff.mp h
        obtain ⟨⟨c', dc⟩, hc', h⟩ := Option.bind_eq_some_iff.mp h
        split at h
        · have := checked_set (headChild_same hi) hc (hrec _ _ _ _ _ hc')
          rw [RoseTree.node_label_children] at this
          exact atRoot_checked hrec this h
        · simp only [Option.some.injEq] at h
          subst h
          exact checked_refl Γ Φ t

/-- The reduction past a weak head normal form reached by a checked rewriting, its subterms
reduced by a reduction whose results are checked, computes checked results. -/
theorem deepStep_checked {rs : List NormRule} {rec : Reduction} (hrec : EvalChecked G E n rec)
    {depth : Depth} {Γ : List Tree} {Φ : List Term} {t w : Term} {dw : Deriv × Bool}
    (hw : Checked G E n Γ Φ t (w, dw)) {x : Term × Deriv × Bool}
    (h : deepStep G E n rs rec depth Γ Φ w dw = some x) : Checked G E n Γ Φ t x := by
  cases depth with
  | head =>
    simp only [deepStep, pure, Option.some.injEq] at h
    subst h
    exact hw
  | weak =>
    simp only [deepStep, Option.bind_eq_bind] at h
    obtain ⟨cs, hcs, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨hl, hpt⟩ := mapM_spec hcs
    simp only [List.length_zipIdx] at hl
    have hpi (i : ℕ) (h₁ : i < cs.length) (h₃ : i < w.children.length) :
        Checked G E n Γ Φ w.children[i] cs[i] ∧
          (keepsWeak w.label i = true → cs[i].2.2 = false) := by
      have := hpt i h₁ (by simpa using h₃)
      simp only [List.getElem_zipIdx, zero_add] at this
      split at this
      · simp only [Option.some.injEq] at this
        rw [← this]
        exact ⟨checked_refl Γ Φ _, fun _ ↦ rfl⟩
      next hk => exact ⟨hrec _ _ _ _ _ this, fun h' ↦ (hk h').elim⟩
    have hc : Checked G E n Γ Φ w
        (RoseTree.node w.label (cs.map Prod.fst), dCong (cs.map Prod.snd)) := by
      have := checked_cong (l := w.label) (Γs := w.children.map fun _ ↦ (Γ, Φ))
        (congCtxs_weak (by simp [hl]) fun i hi hk ↦ ?_) hl (by simp)
        fun i h₁ _ h₃ ↦ by simpa using (hpi i h₁ h₃).1
      · rwa [RoseTree.node_label_children] at this
      · simp only [List.length_map] at hi
        have hu := ((hpi i hi (hl ▸ hi)).1.unmarked ((hpi i hi (hl ▸ hi)).2 hk)).2
        simp [hu, dRefl, Rule.isRefl]
    have h₁ := checked_trans hw hc
    split at h
    · exact atRoot_checked hrec h₁ h
    · simp only [pure, Option.some.injEq] at h
      subst h
      exact h₁
  | «open» =>
    simp only [deepStep, Option.bind_eq_bind] at h
    obtain ⟨Γs, hΓs, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨cs, hcs, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨hl, hpt⟩ := mapM_spec hcs
    have hΓl := childCtxs_length hΓs
    simp only [List.length_zipIdx, List.length_zip, hΓl, min_self] at hl
    have hc : Checked G E n Γ Φ w
        (RoseTree.node w.label (cs.map Prod.fst), dCong (cs.map Prod.snd)) := by
      have := checked_cong_child (E := E) hΓs hl fun i h₁ h₂ h₃ ↦ by
        have := hpt i h₁ (by simpa [hΓl] using h₃)
        simp only [List.getElem_zipIdx, List.getElem_zip, zero_add] at this
        split at this
        · simp only [Option.some.injEq] at this
          rw [← this]
          exact checked_refl _ _ _
        · exact hrec _ _ _ _ _ this
      rwa [RoseTree.node_label_children] at this
    have h₁ := checked_trans hw hc
    split at h
    · exact atRoot_checked hrec h₁ h
    · simp only [pure, Option.some.injEq] at h
      subst h
      exact h₁
  | full =>
    simp only [deepStep, Option.bind_eq_bind] at h
    obtain ⟨Γs, hΓs, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨cs, hcs, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨hl, hpt⟩ := mapM_zip_spec hcs (childCtxs_length hΓs)
    have hc : Checked G E n Γ Φ w
        (RoseTree.node w.label (cs.map Prod.fst), dCong (cs.map Prod.snd)) := by
      have := checked_cong_child hΓs hl fun i h₁ h₂ h₃ ↦ hrec _ _ _ _ _ (hpt i h₁ h₂ h₃)
      rwa [RoseTree.node_label_children] at this
    split at h
    · rename_i t₂ dr hr
      obtain ⟨⟨t₃, d₃⟩, h₃, h⟩ := Option.bind_eq_some_iff.mp h
      simp only [pure, Option.some.injEq] at h
      subst h
      exact checked_trans hw
        (checked_trans hc (checked_trans (rootRewrite_checked hr) (hrec _ _ _ _ _ h₃)))
    · simp only [pure, Option.some.injEq] at h
      subst h
      exact checked_trans hw hc

/-- One step of the reduction to a depth, its subterms reduced by a reduction whose results are
checked, computes checked results. -/
theorem evalStep_checked {rs : List NormRule} {rec : Reduction} (hrec : EvalChecked G E n rec) :
    EvalChecked G E n (evalStep G E n rs rec) := fun _ _ _ _ _ h ↦ by
  simp only [evalStep, Option.bind_eq_bind] at h
  obtain ⟨⟨_, _⟩, hw, h⟩ := Option.bind_eq_some_iff.mp h
  exact deepStep_checked hrec (headStep_checked hrec _ _ _ _ hw) h

/-- The reduction's results are checked, at every depth and fuel. -/
theorem eval_checked (rs : List NormRule) (fuel : ℕ) : EvalChecked G E n (eval G E n rs fuel) :=
  Nat.rec (motive := fun f ↦ EvalChecked G E n (eval G E n rs f))
    (fun _ Γ Φ t x h ↦ by
      simp only [eval, Option.some.injEq] at h
      subst h
      exact checked_refl Γ Φ t)
    (fun _ ih ↦ evalStep_checked ih) fuel

end Geb.FreeTopos.Internal

end
