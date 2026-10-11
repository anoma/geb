/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.LF.Metatheory.HSubstRename

set_option doc.verso true in
/-!
# The composition of hereditary substitutions

Hereditary substitutions compose as ordinary ones do (\[HarperLicata2007\], Lemma 2.10):
substituting {lit}`M` for {lit}`y` and then {lit}`N` for {lit}`x` is substituting {lit}`N` for
{lit}`x` in {lit}`M` and in the expression and then the first for {lit}`y`, and the outer two
substitutions are defined whenever the inner three are. With de Bruijn indices, {lit}`y` is the
variable of index {lit}`k` of the expression, {lit}`x` the variable {lit}`j` above it, {lit}`M`
an expression of the context below {lit}`y`, which contains {lit}`x`, and {lit}`N` one of the
context below {lit}`x` ({lit}`CompStmt`).

The proof is by induction on the sum of the sizes of the two simple types, and within it on the
expression. Where the head of an application is {lit}`y`, the substitution of {lit}`N` meets the
reduction of {lit}`M` applied to the spine, and where it is {lit}`x`, the substitution of the
substituted {lit}`M` meets the reduction of {lit}`N`: substitution commutes with reduction
({lit}`RedStmt`), by induction on the reduction's simple type, through the composition at the
smaller simple types of its domains. In the second case {lit}`N` does not contain {lit}`y`, and
the substitution for it leaves {lit}`N` in place ({name}`Geb.LF.hsubWith_vacuous`); the two cases
exchange the two simple types, as the measure allows.

## Main definitions

* {lit}`SimpleTy.size` — the size of a simple type.
* {lit}`CompStmt`, {lit}`RedStmt` — the composition of two hereditary substitutions, and of a
  substitution with a reduction.

## Main statements

* {lit}`red_of_comp` — substitution commutes with reduction where the compositions at smaller
  simple types hold.
* {lit}`comp` — the composition of hereditary substitutions.

## References

* \[HarperLicata2007\], Lemma 2.10.

## Tags

logical framework, LF, hereditary substitution, composition, substitution lemma
-/

set_option doc.verso true

@[expose] public section

namespace Geb.LF

/-- The size of a simple type: one more than the sum of the sizes of its children. -/
def SimpleTy.size : SimpleTy → ℕ := RoseTree.elim fun _ cs ↦ cs.sum + 1

/-- The size of a function type exceeds the sum of its domain's and codomain's. -/
theorem SimpleTy.size_arrow (α₁ α₂ : SimpleTy) :
    SimpleTy.size (RoseTree.node .arrow [α₁, α₂]) = α₁.size + α₂.size + 1 := by
  simp [SimpleTy.size, Nat.add_assoc]

/-- Hereditary substitution is substitution into the expression given the reduction at the
simple type. -/
theorem hsub_eq (α : SimpleTy) (n e : Expr) (j : ℕ) : hsub α n e j = hsubWith (reduce α) e n j :=
  rfl

/-- Renaming by adding zero is the identity. -/
theorem rename_add_zero (e : Expr) : e.rename (· + 0) = e :=
  rename_id e

/-- The composition of the hereditary substitution of {lit}`M`, at {lit}`α₂`, for the variable
of index {lit}`k`, with that of {lit}`N`, at {lit}`α₀`, for the variable {lit}`j` above it, the
other way round: where the inner three are defined, the outer two are, and agree. -/
def CompStmt (α₀ α₂ : SimpleTy) : Prop :=
  ∀ (E₁ : Expr) (k j : ℕ) (N M E M' E₁' : Expr),
    hsub α₂ (M.rename (· + k)) E₁ k = some E →
    hsub α₀ N M j = some M' →
    hsub α₀ (N.rename (· + (k + 1))) E₁ (k + 1 + j) = some E₁' →
    ∃ R, hsub α₀ (N.rename (· + k)) E (k + j) = some R ∧
      hsub α₂ (M'.rename (· + k)) E₁' k = some R

/-- The commutation of the hereditary substitution of {lit}`P`, at {lit}`α₀`, with the reduction
at {lit}`α₂` of a term applied to a spine: where the reduction and the substitutions into its term
and spine are defined, the substitution into its result is, and is the reduction of the
substituted term applied to the substituted spine. -/
def RedStmt (α₀ α₂ : SimpleTy) : Prop :=
  ∀ (P Q Q' R : Expr) (as as' : List Expr) (j : ℕ),
    reduce α₂ Q as = some R → hsub α₀ P Q j = some Q' →
    (as.map fun a ↦ hsub α₀ P a j).mapM id = some as' →
    ∃ R', hsub α₀ P R j = some R' ∧ reduce α₂ Q' as' = some R'

/-- Substitution commutes with reduction at a simple type where it composes with substitution at
every smaller simple type. -/
theorem red_of_comp (α₀ : SimpleTy) :
    ∀ α₂ : SimpleTy, (∀ β, β.size < α₂.size → CompStmt α₀ β) → RedStmt α₀ α₂ :=
  RoseTree.ind fun l cs ih hcomp P Q Q' R as as' j hR hQ has ↦ by
    rw [reduce_node] at hR
    rcases l with a | _
    · rcases cs with _ | ⟨c, cs⟩
      · rcases as with _ | ⟨m, as⟩
        · change some Q = some R at hR
          obtain rfl := Option.some.inj hR
          simp only [List.map_nil, List.mapM_nil, Option.pure_def, Option.some.injEq] at has
          subst has
          exact ⟨Q', hQ, rfl⟩
        · simp [reduceStep] at hR
      · simp [reduceStep] at hR
    · rcases cs with _ | ⟨β₁, _ | ⟨β₂, _ | ⟨β₃, cs⟩⟩⟩
      · simp [reduceStep] at hR
      · simp [reduceStep] at hR
      · rcases as with _ | ⟨A, As⟩
        · simp [reduceStep] at hR
        · obtain ⟨ql, qcs, rfl⟩ := exists_node Q
          simp only [List.map_cons, List.map_nil, reduceStep, RoseTree.label_node,
            RoseTree.children_node] at hR
          rcases ql with _ | _ | _ | _
          · simp at hR
          · simp at hR
          · rcases qcs with _ | ⟨B, _ | ⟨B₂, qcs⟩⟩
            · simp at hR
            · obtain ⟨C, hC, hRC⟩ := Option.bind_eq_some_iff.mp hR
              rw [hsub_eq, hsubWith_node_of_ne _ _ (fun i h ↦ by cases h), Option.map_eq_map,
                Option.map_eq_some_iff] at hQ
              obtain ⟨ys, hys, rfl⟩ := hQ
              obtain ⟨hlen, hk⟩ := getElem_of_mapM_id_eq_some hys
              rcases ys with _ | ⟨B', _ | ⟨y₂, ys⟩⟩
              · simp at hlen
              · have hB' := hk 0 (by simp) (by simp)
                simp only [List.zipIdx_cons, List.zipIdx_nil, List.map_cons, List.map_nil,
                  List.getElem_cons_zero, show Label.lam.binders 0 = 1 from rfl,
                  Function.iterate_one] at hB'
                rw [mapM_id_eq_some_iff] at has
                rcases as' with _ | ⟨A', As'⟩
                · simp at has
                simp only [List.map_cons, List.cons.injEq] at has
                obtain ⟨hA', hAs⟩ := has
                rw [← mapM_id_eq_some_iff] at hAs
                have hsz := SimpleTy.size_arrow β₁ β₂
                obtain ⟨R₀, hR₀, hR₀'⟩ := hcomp β₁ (by omega) B 0 j P A C A' B'
                  (by rw [rename_add_zero]; exact hC) hA'
                  (by
                    rw [show 0 + 1 + j = j + 1 by omega, show (· + (0 + 1)) = Nat.succ from rfl]
                    exact hB')
                rw [rename_add_zero, Nat.zero_add] at hR₀
                rw [rename_add_zero] at hR₀'
                obtain ⟨R', hR', hred⟩ := ih β₂ (by simp)
                  (fun β hβ ↦ hcomp β (by omega)) P C R₀ R As As' j hRC hR₀ hAs
                refine ⟨R', hR', ?_⟩
                rw [reduce_node]
                simp only [List.map_cons, List.map_nil, reduceStep, RoseTree.label_node,
                  RoseTree.children_node]
                rw [← hsub_eq, hR₀', Option.bind_some]
                exact hred
              · simp only [List.length_cons, List.length_nil, List.length_map,
                  List.length_zipIdx] at hlen
                omega
            · simp at hR
          · simp at hR
      · simp [reduceStep] at hR

/-- A list of partial values each of which has a value has a list of values. -/
theorem exists_mapM_id {β : Type} :
    ∀ xs : List (Option β), (∀ (k : ℕ) (hk : k < xs.length), ∃ y, xs[k] = some y) →
      ∃ ys, xs.mapM id = some ys :=
  fun xs ↦ xs.rec (motive := fun xs ↦ (∀ (k : ℕ) (hk : k < xs.length), ∃ y, xs[k] = some y) →
      ∃ ys, xs.mapM id = some ys)
    (fun _ ↦ ⟨[], rfl⟩)
    (fun x xs ih h ↦ by
      obtain ⟨y, hy⟩ := h 0 (by simp)
      obtain ⟨ys, hys⟩ := ih fun k hk ↦ h (k + 1) (by simpa using hk)
      refine ⟨y :: ys, ?_⟩
      rw [mapM_id_eq_some_iff] at hys ⊢
      simp only [List.getElem_cons_zero] at hy
      rw [hy, hys]
      rfl)

/-- Two lists of partial values that agree, each entry having a value, have one list of
values. -/
theorem exists_mapM_id_of_agree {β : Type} {xs ys : List (Option β)} (hl : xs.length = ys.length)
    (h : ∀ (k : ℕ) (h₁ : k < xs.length) (h₂ : k < ys.length),
      ∃ r, xs[k] = some r ∧ ys[k] = some r) :
    ∃ rs, xs.mapM id = some rs ∧ ys.mapM id = some rs := by
  have hxy : xs = ys := List.ext_getElem hl fun k h₁ h₂ ↦ by
    obtain ⟨r, hx, hy⟩ := h k h₁ h₂
    rw [hx, hy]
  subst hxy
  obtain ⟨rs, hrs⟩ := exists_mapM_id xs fun k hk ↦ by
    obtain ⟨r, hx, -⟩ := h k hk hk
    exact ⟨r, hx⟩
  exact ⟨rs, hrs, hrs⟩

/-- Hereditary substitution into the application of a variable. -/
theorem hsub_var (α : SimpleTy) (n : Expr) (i : ℕ) (cs : List Expr) (j : ℕ) :
    hsub α n (Expr.var i cs) j = ((cs.map fun c ↦ hsub α n c j).mapM id).bind fun ms ↦
      if i = j then reduce α n ms else some (Expr.var (renumber j i) ms) :=
  hsubWith_var _ i cs n j

/-- Weakening by {lit}`b` after weakening by {lit}`k` is weakening by their sum. -/
theorem iterate_shift_rename_add (b k : ℕ) (e : Expr) :
    Expr.shift^[b] (e.rename (· + k)) = e.rename (· + (k + b)) := by
  rw [iterate_shift, rename_rename]
  congr 1
  funext x
  simp only [Function.comp_apply]
  omega

/-- Weakening past {lit}`k + 1` variables is weakening past {lit}`k` and then past the variable
of index {lit}`k`. -/
theorem rename_add_succ (k : ℕ) (e : Expr) :
    e.rename (· + (k + 1)) = (e.rename (· + k)).rename (liftR^[k] Nat.succ) := by
  rw [rename_rename]
  congr 1
  funext x
  simp only [Function.comp_apply, iterate_liftR_apply, show ¬ x + k < k by omega, ↓reduceIte,
    Nat.add_sub_cancel, Nat.succ_eq_add_one]
  omega

/-- The composition at two simple types, given it at every pair of smaller total size. -/
theorem comp_step {α₀ α₂ : SimpleTy}
    (hsmall : ∀ α β : SimpleTy, α.size + β.size < α₀.size + α₂.size → CompStmt α β) :
    CompStmt α₀ α₂ := by
  have redA : RedStmt α₀ α₂ := red_of_comp α₀ α₂ fun β hβ ↦ hsmall α₀ β (by omega)
  have redB : RedStmt α₂ α₀ := red_of_comp α₂ α₀ fun β hβ ↦ hsmall α₂ β (by omega)
  intro E₁
  refine RoseTree.ind (P := fun E₁ ↦ ∀ (k j : ℕ) (N M E M' E₁' : Expr),
      hsub α₂ (M.rename (· + k)) E₁ k = some E → hsub α₀ N M j = some M' →
      hsub α₀ (N.rename (· + (k + 1))) E₁ (k + 1 + j) = some E₁' →
      ∃ R, hsub α₀ (N.rename (· + k)) E (k + j) = some R ∧
        hsub α₂ (M'.rename (· + k)) E₁' k = some R) (fun l cs ih ↦ ?_) E₁
  intro k j N M E M' E₁' h₁ h₂ h₃
  have nonvar : (∀ i, l ≠ .app (.var i)) → ∃ R, hsub α₀ (N.rename (· + k)) E (k + j) = some R ∧
      hsub α₂ (M'.rename (· + k)) E₁' k = some R := by
    intro hl
    rw [hsub_eq, hsubWith_node_of_ne _ l hl, Option.map_eq_map, Option.map_eq_some_iff] at h₁ h₃
    obtain ⟨es, hes, rfl⟩ := h₁
    obtain ⟨cs', hcs', rfl⟩ := h₃
    obtain ⟨hl₁, hk₁⟩ := getElem_of_mapM_id_eq_some hes
    obtain ⟨hl₃, hk₃⟩ := getElem_of_mapM_id_eq_some hcs'
    simp only [length_zipIdx_map] at hl₁ hl₃
    obtain ⟨rs, hrs₁, hrs₂⟩ := exists_mapM_id_of_agree
      (xs := es.zipIdx.map fun p ↦ hsubWith (reduce α₀) p.1
        (Expr.shift^[l.binders p.2] (N.rename (· + k))) (k + j + l.binders p.2))
      (ys := cs'.zipIdx.map fun p ↦ hsubWith (reduce α₂) p.1
        (Expr.shift^[l.binders p.2] (M'.rename (· + k))) (k + l.binders p.2))
      (by simp only [length_zipIdx_map]; omega) fun idx h₁' h₂' ↦ by
        simp only [length_zipIdx_map] at h₁' h₂'
        have e₁ := hk₁ idx (by simp only [length_zipIdx_map]; omega) h₁'
        have e₃ := hk₃ idx (by simp only [length_zipIdx_map]; omega) h₂'
        simp only [List.getElem_map, List.getElem_zipIdx, zero_add,
          iterate_shift_rename_add] at e₁ e₃ ⊢
        obtain ⟨r, hr₁, hr₂⟩ := ih _ (List.getElem_mem _) (k + l.binders idx) j N M _ M' _ e₁ h₂
          (by
            rw [show k + l.binders idx + 1 = k + 1 + l.binders idx by omega,
              show k + 1 + l.binders idx + j = k + 1 + j + l.binders idx by omega]
            exact e₃)
        refine ⟨r, ?_, hr₂⟩
        rw [show k + j + l.binders idx = k + l.binders idx + j by omega]
        exact hr₁
    refine ⟨RoseTree.node l rs, ?_, ?_⟩
    · rw [hsub_eq, hsubWith_node_of_ne _ l hl, hrs₁]
      rfl
    · rw [hsub_eq, hsubWith_node_of_ne _ l hl, hrs₂]
      rfl
  rcases l with _ | _ | _ | (i | c)
  · exact nonvar fun i h ↦ by cases h
  · exact nonvar fun i h ↦ by cases h
  · exact nonvar fun i h ↦ by cases h
  · change hsub α₂ _ (Expr.var i cs) k = some E at h₁
    change hsub α₀ _ (Expr.var i cs) (k + 1 + j) = some E₁' at h₃
    rw [hsub_var] at h₁ h₃
    obtain ⟨es, hes, h₁⟩ := Option.bind_eq_some_iff.mp h₁
    obtain ⟨cs', hcs', h₃⟩ := Option.bind_eq_some_iff.mp h₃
    obtain ⟨hl₁, hk₁⟩ := getElem_of_mapM_id_eq_some hes
    obtain ⟨hl₃, hk₃⟩ := getElem_of_mapM_id_eq_some hcs'
    simp only [List.length_map] at hl₁ hl₃
    obtain ⟨rs, hrs₁, hrs₂⟩ := exists_mapM_id_of_agree
      (xs := es.map fun e ↦ hsub α₀ (N.rename (· + k)) e (k + j))
      (ys := cs'.map fun c ↦ hsub α₂ (M'.rename (· + k)) c k)
      (by simp only [List.length_map]; omega) fun idx h₁' h₂' ↦ by
        simp only [List.length_map] at h₁' h₂'
        have e₁ := hk₁ idx (by simp only [List.length_map]; omega) h₁'
        have e₃ := hk₃ idx (by simp only [List.length_map]; omega) h₂'
        simp only [List.getElem_map] at e₁ e₃ ⊢
        exact ih _ (List.getElem_mem _) k j N M _ M' _ e₁ h₂ e₃
    by_cases hik : i = k
    · simp only [hik, ↓reduceIte, show ¬ k = k + 1 + j by omega] at h₁ h₃
      obtain rfl := Option.some.inj h₃
      obtain ⟨R', hR', hred⟩ := redA _ _ _ _ es rs (k + j) h₁
        (by
          have := hsub_weaken α₀ M N j k M' h₂
          rwa [Nat.add_comm j k] at this) hrs₁
      refine ⟨R', hR', ?_⟩
      rw [hsub_var, hrs₂, Option.bind_some]
      simp only [show renumber (k + 1 + j) k = k by unfold renumber; split_ifs <;> omega,
        ↓reduceIte]
      exact hred
    · by_cases hix : i = k + 1 + j
      · simp only [hix, ↓reduceIte, show ¬ k + 1 + j = k by omega] at h₁ h₃
        obtain rfl := Option.some.inj h₁
        have hvac : hsub α₂ (M'.rename (· + k)) (N.rename (· + (k + 1))) k =
            some (N.rename (· + k)) := by
          rw [rename_add_succ]
          exact hsubWith_vacuous _ _ _ _
        obtain ⟨R', hR', hred⟩ := redB _ _ _ _ cs' rs k h₃ hvac hrs₂
        refine ⟨R', ?_, hR'⟩
        rw [show renumber k (k + 1 + j) = k + j by unfold renumber; split_ifs <;> omega,
          hsub_var, hrs₁, Option.bind_some]
        simp only [↓reduceIte]
        exact hred
      · simp only [hik, hix, ↓reduceIte] at h₁ h₃
        obtain rfl := Option.some.inj h₁
        obtain rfl := Option.some.inj h₃
        refine ⟨Expr.var (renumber (k + j) (renumber k i)) rs, ?_, ?_⟩
        · rw [hsub_var, hrs₁, Option.bind_some]
          have hne : renumber k i ≠ k + j := by unfold renumber; split_ifs <;> omega
          simp only [hne, ↓reduceIte]
        · rw [hsub_var, hrs₂, Option.bind_some]
          have hne : renumber (k + 1 + j) i ≠ k := by unfold renumber; split_ifs <;> omega
          simp only [hne, ↓reduceIte]
          congr 2
          unfold renumber
          split_ifs <;> omega
  · exact nonvar fun i h ↦ by cases h

/-- Hereditary substitutions compose (\[HarperLicata2007\], Lemma 2.10). -/
theorem comp (α₀ α₂ : SimpleTy) : CompStmt α₀ α₂ :=
  Nat.rec (motive := fun s ↦ ∀ α β : SimpleTy, α.size + β.size < s → CompStmt α β)
    (fun _ _ h ↦ absurd h (Nat.not_lt_zero _))
    (fun _ ih _ _ h ↦ comp_step fun α' β' h' ↦ ih α' β' (by omega))
    (α₀.size + α₂.size + 1) α₀ α₂ (Nat.lt_succ_self _)

end Geb.LF

end
