/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
-- Modified from geb-mathlib by scripts/geb-mathlib-backport.patch.
module

public import Geb.Prototypes.LF.HSubst
public import Geb.Prototypes.LF.Metatheory.Rename
public import Geb.Prototypes.PartialHorn.Basic

set_option doc.verso true in
/-!
# Hereditary substitution and renaming

Hereditary substitution commutes with renaming: substituting and then renaming the result is
renaming the expression and the substituted term and then substituting. With de Bruijn indices,
the substitution for the variable of index {lit}`j` acts on an expression in a context of
{lit}`j` variables, the substituted one, and an outer context; a renaming of the outer context
is lifted past the {lit}`j` inner variables on the result and the substituted term, and past the
substituted one as well on the expression.

The substitution into an expression commutes with renaming whenever the reduction it is given
does ({lit}`hsubWith_rename`), by induction on the expression; the reduction at a simple type
does ({lit}`reduce_rename`), by induction on the simple type, its substitution at the domain
being the substitution of the first case. Both are the de Bruijn form of the stability of
hereditary substitution under weakening and exchange (\[HarperLicata2007\], Lemmas 2.6 and
2.7).

## Main definitions

* {lit}`RenameCompat` — a reduction commutes with renaming.
* {lit}`renumber`, {lit}`HoleRen` — the renumbering past a removed variable, and renamings that
  agree around it.

## Main statements

* {lit}`hsubWith_node`, {lit}`hsubWith_var`, {lit}`hsubWith_node_of_ne` — the computation
  rules of the substitution.
* {lit}`HoleRen.lift`, {lit}`HoleRen.iterate` — agreement around a variable under binders.
* {lit}`hsubWith_holeRen`, {lit}`hsubWith_rename` — the substitution commutes with renamings
  that agree around the substituted variable, and with renaming outside it, given a reduction
  that does.
* {lit}`reduce_rename`, {lit}`hsub_rename` — the reduction and the hereditary substitution at a
  simple type commute with renaming.

## References

* \[HarperLicata2007\], Section 2.3.

## Tags

logical framework, LF, hereditary substitution, renaming, weakening
-/

set_option doc.verso true

@[expose] public section

namespace Geb.LF

/-- A list of partial values all has values exactly when it is the list of those values. -/
theorem mapM_id_eq_some_iff {β : Type} (xs : List (Option β)) (ys : List β) :
    xs.mapM id = some ys ↔ xs = ys.map some := by
  rw [PartialHorn.mapM_eq_some_iff, List.map_id]

/-- A list of partial values all of which have values, in order, element by element. -/
theorem mapM_id_eq_some_of_getElem {β : Type} {xs : List (Option β)} {ys : List β}
    (hl : xs.length = ys.length) (h : ∀ k (h₁ : k < xs.length) (h₂ : k < ys.length),
      xs[k] = some ys[k]) : xs.mapM id = some ys := by
  rw [mapM_id_eq_some_iff]
  exact List.ext_getElem (by simp [hl]) fun k h₁ h₂ ↦ by
    simpa using h k h₁ (by simpa using h₂)

/-- The values of a list of partial values all of which have them, element by element. -/
theorem getElem_of_mapM_id_eq_some {β : Type} {xs : List (Option β)} {ys : List β}
    (h : xs.mapM id = some ys) :
    xs.length = ys.length ∧ ∀ k (h₁ : k < xs.length) (h₂ : k < ys.length), xs[k] = some ys[k] := by
  rw [mapM_id_eq_some_iff] at h
  subst h
  exact ⟨by simp, fun k _ _ ↦ by simp⟩

/-- Pairing with positions and mapping after mapping is pairing and mapping by the composite. -/
theorem zipIdx_map_map {α β γ : Type} (f : α → β) (g : β × ℕ → γ) (l : List α) :
    (l.map f).zipIdx.map g = l.zipIdx.map fun p ↦ g (f p.1, p.2) :=
  List.ext_getElem (by simp) fun k _ _ ↦ by
    simp only [List.getElem_map, List.getElem_zipIdx, zero_add]

/-- The computation rule of the substitution. -/
theorem hsubWith_node (red : Expr → List Expr → Option Expr) (l : Label) (cs : List Expr)
    (n : Expr) (j : ℕ) :
    hsubWith red (RoseTree.node l cs) n j = hsubStep red l (cs.map (hsubWith red)) n j :=
  congrFun (congrFun (RoseTree.elim_node _ l cs) n) j

/-- The substitution into an application of a variable: the substitution into its spine, then
the reduction where the variable is the substituted one, and the renumbering of the variable
otherwise. -/
theorem hsubWith_var (red : Expr → List Expr → Option Expr) (i : ℕ) (cs : List Expr) (n : Expr)
    (j : ℕ) :
    hsubWith red (RoseTree.node (.app (.var i)) cs) n j =
      ((cs.map fun c ↦ hsubWith red c n j).mapM id).bind fun ms ↦
        if i = j then red n ms else some (Expr.var (if j < i then i - 1 else i) ms) := by
  rw [hsubWith_node, hsubStep, List.mapM_map, List.mapM_map]
  rfl

/-- The substitution into a node other than an application of a variable: the substitution into
each child, under the variables the node binds over it. -/
theorem hsubWith_node_of_ne (red : Expr → List Expr → Option Expr) (l : Label)
    (hl : ∀ i, l ≠ .app (.var i)) (cs : List Expr) (n : Expr) (j : ℕ) :
    hsubWith red (RoseTree.node l cs) n j = RoseTree.node l <$>
      (cs.zipIdx.map fun p ↦
        hsubWith red p.1 (Expr.shift^[l.binders p.2] n) (j + l.binders p.2)).mapM
        id := by
  rw [hsubWith_node]
  rcases l with _ | _ | _ | (i | c)
  · simp only [hsubStep, zipIdx_map_map]
  · simp only [hsubStep, zipIdx_map_map]
  · simp only [hsubStep, zipIdx_map_map]
  · exact absurd rfl (hl i)
  · simp only [hsubStep, zipIdx_map_map]

/-- A reduction commutes with renaming: reducing and renaming the result is renaming the term
and the spine and reducing. -/
def RenameCompat (red : Expr → List Expr → Option Expr) : Prop :=
  ∀ (n : Expr) (ms : List Expr) (r : Expr) (ρ : ℕ → ℕ), red n ms = some r →
    red (n.rename ρ) (ms.map fun m ↦ m.rename ρ) = some (r.rename ρ)

/-- A label other than an application of a variable is left in place by renaming. -/
theorem Label.rename_of_ne {l : Label} (hl : ∀ i, l ≠ .app (.var i)) (σ : ℕ → ℕ) :
    l.rename σ = l := by
  rcases l with _ | _ | _ | (i | c)
  · rfl
  · rfl
  · rfl
  · exact absurd rfl (hl i)
  · rfl

/-- An application of a variable binds no variable over its spine. -/
@[simp] theorem Label.binders_app (h : Head) (k : ℕ) : (Label.app h).binders k = 0 := rfl

/-- The renumbering of a variable other than the substituted one commutes with renaming: the
variable of index {lit}`i` in a context with the variable of index {lit}`j` removed. -/
theorem iterate_liftR_renumber (j i : ℕ) (ρ : ℕ → ℕ) (h : i ≠ j) :
    liftR^[j] ρ (if j < i then i - 1 else i) =
      if j < liftR^[j + 1] ρ i then liftR^[j + 1] ρ i - 1 else liftR^[j + 1] ρ i := by
  rw [iterate_liftR_apply (j + 1), iterate_liftR_apply j]
  by_cases hij : i < j
  · simp [hij, show i < j + 1 by omega, show ¬ j < i by omega]
  · have hji : j < i := by omega
    simp only [hji, ↓reduceIte, show ¬ i < j + 1 by omega,
      show ¬ i - 1 < j by omega, show i - 1 - j = i - (j + 1) by omega]
    split_ifs <;> omega

/-- The renaming of the application of a variable: the variable renamed, and the spine. -/
theorem rename_var (i : ℕ) (ms : List Expr) (ρ : ℕ → ℕ) :
    (Expr.var i ms).rename ρ = Expr.var (ρ i) (ms.map fun m ↦ m.rename ρ) := by
  rw [Expr.var, Expr.app, rename_node]
  exact congrArg _ (List.ext_getElem (by simp) fun k _ _ ↦ by simp)

/-- The renumbering of a variable past the removal of the variable of index {lit}`j`. -/
def renumber (j i : ℕ) : ℕ := if j < i then i - 1 else i

/-- A renaming {lit}`τ` of a context with a variable at {lit}`j` and a renaming {lit}`σ` of that
context with the variable removed agree around it: {lit}`τ` takes it to {lit}`j'`, and every other
variable to one other than {lit}`j'` which, renumbered past {lit}`j'`, is the image under
{lit}`σ` of the variable renumbered past {lit}`j`. -/
def HoleRen (σ τ : ℕ → ℕ) (j j' : ℕ) : Prop :=
  τ j = j' ∧ ∀ i, i ≠ j → τ i ≠ j' ∧ renumber j' (τ i) = σ (renumber j i)

/-- Renamings that agree around a variable agree, lifted under a binder, around its
successor. -/
theorem HoleRen.lift {σ τ : ℕ → ℕ} {j j' : ℕ} (h : HoleRen σ τ j j') :
    HoleRen (liftR σ) (liftR τ) (j + 1) (j' + 1) := by
  refine ⟨congrArg (· + 1) h.1, fun i hi ↦ ?_⟩
  rcases i with _ | i
  · refine ⟨fun e ↦ Nat.succ_ne_zero j' e.symm, ?_⟩
    simp only [renumber, Nat.not_lt_zero, ↓reduceIte]
    rfl
  · have hi' : i ≠ j := fun e ↦ hi (congrArg (· + 1) e)
    obtain ⟨hne, heq⟩ := h.2 i hi'
    refine ⟨fun e ↦ hne (Nat.succ.inj e), ?_⟩
    change renumber (j' + 1) (τ i + 1) = liftR σ (renumber (j + 1) (i + 1))
    have h₁ : renumber (j' + 1) (τ i + 1) = renumber j' (τ i) + 1 := by
      unfold renumber
      split_ifs <;> omega
    have h₂ : renumber (j + 1) (i + 1) = renumber j i + 1 := by
      unfold renumber
      split_ifs <;> omega
    rw [h₁, h₂, heq]
    rfl

/-- Renamings that agree around a variable agree, lifted under {lit}`b` binders, around the
variable {lit}`b` above it. -/
theorem HoleRen.iterate {σ τ : ℕ → ℕ} {j j' : ℕ} (h : HoleRen σ τ j j') (b : ℕ) :
    HoleRen (liftR^[b] σ) (liftR^[b] τ) (j + b) (j' + b) :=
  Nat.rec (motive := fun b ↦ HoleRen (liftR^[b] σ) (liftR^[b] τ) (j + b) (j' + b)) h
    (fun b ih ↦ by
      beta_reduce
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', Nat.succ_eq_add_one,
        ← Nat.add_assoc, ← Nat.add_assoc]
      exact ih.lift) b

/-- The substitution into an expression commutes with renamings that agree around the
substituted variable, given a reduction that commutes with renaming. -/
theorem hsubWith_holeRen {red : Expr → List Expr → Option Expr} (hred : RenameCompat red) :
    ∀ (e n : Expr) (j j' : ℕ) (σ τ : ℕ → ℕ) (e' : Expr), HoleRen σ τ j j' →
      hsubWith red e n j = some e' → hsubWith red (e.rename τ) (n.rename σ) j' =
        some (e'.rename σ) :=
  RoseTree.ind fun l cs ih n j j' σ τ e' hστ h ↦ by
    have nonvar : (∀ i, l ≠ .app (.var i)) → hsubWith red (Expr.rename (RoseTree.node l cs) τ)
        (n.rename σ) j' = some (e'.rename σ) := by
      intro hl
      rw [hsubWith_node_of_ne red l hl, Option.map_eq_map, Option.map_eq_some_iff] at h
      obtain ⟨ys, hys, rfl⟩ := h
      obtain ⟨hlen, hk⟩ := getElem_of_mapM_id_eq_some hys
      rw [rename_node, Label.rename_of_ne hl, hsubWith_node_of_ne red l hl, rename_node,
        Label.rename_of_ne hl]
      refine congrArg (Option.map _) (mapM_id_eq_some_of_getElem (by simpa using hlen)
        fun k h₁ h₂ ↦ ?_)
      have hk' := hk k (by simpa using h₁) (by simpa using h₂)
      simp only [List.getElem_map, List.getElem_zipIdx, zero_add] at hk' ⊢
      rw [iterate_shift_rename]
      exact ih _ (List.getElem_mem _) _ _ _ _ _ _ (hστ.iterate _) hk'
    rcases l with _ | _ | _ | (i | c)
    · exact nonvar fun i h ↦ by cases h
    · exact nonvar fun i h ↦ by cases h
    · exact nonvar fun i h ↦ by cases h
    · rw [hsubWith_var, Option.bind_eq_some_iff] at h
      obtain ⟨ms, hms, h⟩ := h
      obtain ⟨hl, hk⟩ := getElem_of_mapM_id_eq_some hms
      rw [rename_node]
      simp only [Label.rename, Head.rename, Label.binders_app, Function.iterate_zero_apply]
      rw [hsubWith_var]
      have hms' : ((cs.zipIdx.map fun p ↦ Expr.rename p.1 τ).map
          fun c ↦ hsubWith red c (n.rename σ) j').mapM id =
          some (ms.map fun m ↦ m.rename σ) :=
        mapM_id_eq_some_of_getElem (by simpa using hl) fun k h₁ h₂ ↦ by
          have hk' := hk k (by simpa using h₁) (by simpa using h₂)
          simp only [List.getElem_map, List.getElem_zipIdx, zero_add] at hk' ⊢
          exact ih _ (List.getElem_mem _) _ _ _ _ _ _ hστ hk'
      rw [hms', Option.bind_some]
      by_cases hij : i = j
      · subst hij
        simp only [↓reduceIte] at h
        simp only [hστ.1, ↓reduceIte]
        exact hred _ _ _ _ h
      · simp only [hij, ↓reduceIte] at h
        obtain rfl := Option.some.inj h
        obtain ⟨hne, heq⟩ := hστ.2 i hij
        simp only [hne, ↓reduceIte]
        rw [rename_var]
        exact congrArg (fun x ↦ some (Expr.var x _)) heq
    · exact nonvar fun i h ↦ by cases h

/-- The substitution into an expression commutes with renaming, given a reduction that does: a
renaming of the context outside the substituted variable and the {lit}`j` variables inside it. -/
theorem hsubWith_rename {red : Expr → List Expr → Option Expr} (hred : RenameCompat red)
    (e n : Expr) (j : ℕ) (ρ : ℕ → ℕ) (e' : Expr) (h : hsubWith red e n j = some e') :
    hsubWith red (e.rename (liftR^[j + 1] ρ)) (n.rename (liftR^[j] ρ)) j =
      some (e'.rename (liftR^[j] ρ)) := by
  refine hsubWith_holeRen hred e n j j _ _ e' ⟨?_, fun i hi ↦ ⟨?_, ?_⟩⟩ h
  · rw [iterate_liftR_apply]
    simp
  · rw [iterate_liftR_apply]
    split_ifs <;> omega
  · exact (iterate_liftR_renumber j i ρ hi).symm

/-- Weakening past {lit}`b` variables is renaming by adding {lit}`b`. -/
theorem iterate_shift (b : ℕ) : ∀ e : Expr, Expr.shift^[b] e = e.rename (· + b) :=
  Nat.rec (motive := fun b ↦ ∀ e : Expr, Expr.shift^[b] e = e.rename (· + b))
    (fun e ↦ (rename_id e).symm)
    (fun b ih e ↦ by
      rw [Function.iterate_succ_apply', ih, Expr.shift, rename_rename]
      rfl) b

/-- Substitution into an expression in which the substituted variable does not occur, an
expression of the context without it renamed past it, gives that expression
(\[HarperLicata2007\], Lemma 2.8), whatever the reduction. -/
theorem hsubWith_vacuous (red : Expr → List Expr → Option Expr) :
    ∀ (e n : Expr) (j : ℕ), hsubWith red (e.rename (liftR^[j] Nat.succ)) n j = some e :=
  RoseTree.ind fun l cs ih n j ↦ by
    have hch : ∀ b, ((cs.zipIdx.map fun p ↦ Expr.rename p.1 (liftR^[b] (liftR^[j] Nat.succ))).map
        fun c ↦ hsubWith red c (Expr.shift^[b] n) (j + b)).mapM id = some cs := fun b ↦
      mapM_id_eq_some_of_getElem (by simp) fun k h₁ h₂ ↦ by
        simp only [List.getElem_map, List.getElem_zipIdx, zero_add]
        have := ih _ (List.getElem_mem h₂) (Expr.shift^[b] n) (j + b)
        rwa [show liftR^[j + b] Nat.succ = liftR^[b] (liftR^[j] Nat.succ) by
          rw [Nat.add_comm, Function.iterate_add_apply]] at this
    have nonvar : (∀ i, l ≠ .app (.var i)) →
        hsubWith red (Expr.rename (RoseTree.node l cs) (liftR^[j] Nat.succ)) n j =
          some (RoseTree.node l cs) := by
      intro hl
      rw [rename_node, Label.rename_of_ne hl, hsubWith_node_of_ne red l hl]
      refine congrArg (Option.map _) (mapM_id_eq_some_of_getElem (by simp) fun k h₁ h₂ ↦ ?_)
      simp only [List.getElem_map, List.getElem_zipIdx, zero_add]
      have := ih _ (List.getElem_mem h₂) (Expr.shift^[l.binders k] n) (j + l.binders k)
      rwa [show liftR^[j + l.binders k] Nat.succ = liftR^[l.binders k] (liftR^[j] Nat.succ) by
        rw [Nat.add_comm, Function.iterate_add_apply]] at this
    rcases l with _ | _ | _ | (i | c)
    · exact nonvar fun i h ↦ by cases h
    · exact nonvar fun i h ↦ by cases h
    · exact nonvar fun i h ↦ by cases h
    · rw [rename_node]
      simp only [Label.rename, Head.rename, Label.binders_app, Function.iterate_zero_apply]
      rw [hsubWith_var]
      have hcs := hch 0
      simp only [Function.iterate_zero_apply, Nat.add_zero] at hcs
      rw [hcs, Option.bind_some]
      have hτ : liftR^[j] Nat.succ i = if i < j then i else i + 1 := by
        rw [iterate_liftR_apply]
        split_ifs with h
        · rfl
        · simp only [Nat.succ_eq_add_one]
          omega
      have hne : liftR^[j] Nat.succ i ≠ j := by
        rw [hτ]
        split_ifs <;> omega
      simp only [hne, ↓reduceIte]
      congr 2
      rw [hτ]
      split_ifs <;> omega
    · exact nonvar fun i h ↦ by cases h

/-- The computation rule of the reduction. -/
theorem reduce_node (l : SimpleLabel) (cs : List SimpleTy) :
    reduce (RoseTree.node l cs) = reduceStep l (cs.map reduce) :=
  RoseTree.elim_node _ l cs

/-- The reduction at a simple type commutes with renaming. -/
theorem reduce_rename : ∀ α : SimpleTy, RenameCompat (reduce α) :=
  RoseTree.ind fun l cs ih n ms r ρ h ↦ by
    rw [reduce_node] at h ⊢
    rcases l with a | _
    · rcases cs with _ | ⟨c, cs⟩
      · rcases ms with _ | ⟨m, ms⟩
        · change some n = some r at h
          change some (n.rename ρ) = some (r.rename ρ)
          rw [Option.some.inj h]
        · simp [reduceStep] at h
      · simp [reduceStep] at h
    · rcases cs with _ | ⟨α₁, _ | ⟨α₂, _ | ⟨α₃, cs⟩⟩⟩
      · simp [reduceStep] at h
      · simp [reduceStep] at h
      · rcases ms with _ | ⟨m, ms⟩
        · simp [reduceStep] at h
        · obtain ⟨l', cs', rfl⟩ : ∃ l' cs', n = RoseTree.node l' cs' :=
            ⟨n.label, n.children, (RoseTree.node_label_children n).symm⟩
          simp only [List.map_cons, List.map_nil, reduceStep, RoseTree.label_node,
            RoseTree.children_node] at h
          simp only [List.map_cons, List.map_nil, reduceStep, rename_node, RoseTree.label_node,
            RoseTree.children_node]
          rcases l' with _ | _ | _ | _
          · simp at h
          · simp at h
          · rcases cs' with _ | ⟨b, _ | ⟨b₂, cs'⟩⟩
            · simp at h
            · obtain ⟨b', hb, hr⟩ := Option.bind_eq_some_iff.mp h
              have hb' := hsubWith_rename (ih α₁ (by simp)) b m 0 ρ b' hb
              simp only [zero_add, Function.iterate_one, Function.iterate_zero_apply] at hb'
              simp only [Label.rename, List.zipIdx_cons, List.zipIdx_nil, List.map_cons,
                List.map_nil]
              rw [show Label.lam.binders 0 = 1 from rfl, Function.iterate_one, hb',
                Option.bind_some]
              exact ih α₂ (by simp) _ _ _ _ hr
            · simp at h
          · simp at h
      · simp [reduceStep] at h

/-- The hereditary substitution at a simple type commutes with renaming. -/
theorem hsub_rename (α : SimpleTy) (e n : Expr) (j : ℕ) (ρ : ℕ → ℕ) (e' : Expr)
    (h : hsub α n e j = some e') :
    hsub α (n.rename (liftR^[j] ρ)) (e.rename (liftR^[j + 1] ρ)) j =
      some (e'.rename (liftR^[j] ρ)) :=
  hsubWith_rename (reduce_rename α) e n j ρ e' h

/-- Hereditary substitution commutes with weakening by {lit}`k` variables inside the substituted
one. -/
theorem hsub_weaken (α : SimpleTy) (e n : Expr) (j k : ℕ) (e' : Expr) (h : hsub α n e j = some e') :
    hsub α (n.rename (· + k)) (e.rename (· + k)) (j + k) = some (e'.rename (· + k)) :=
  hsubWith_holeRen (reduce_rename α) e n j (j + k) _ _ e' ⟨rfl, fun i hi ↦
    ⟨fun e ↦ hi (by dsimp only at e; omega), by dsimp only; unfold renumber; split_ifs <;> omega⟩⟩
    h

end Geb.LF

end
