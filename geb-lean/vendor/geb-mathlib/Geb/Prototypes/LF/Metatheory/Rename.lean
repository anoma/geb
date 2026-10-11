/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
-- Modified from geb-mathlib by scripts/geb-mathlib-backport.patch.
module

public import Geb.Prototypes.LF.Syntax

set_option doc.verso true in
/-!
# Renaming

The laws of the renaming of an expression's variables: it is the functor's action of the
binding signature ({lit}`Label.binders`), so that renaming by the identity is the identity and
renaming twice is renaming by the composite ({lit}`rename_id`, {lit}`rename_rename`), the
lifting of a renaming under binders respecting both. Renaming preserves the label of a node, and
so its binders, and the erasure of a type ({lit}`erase_rename`).

## Main statements

* {lit}`rename_node` — the computation rule of the renaming.
* {lit}`liftR_comp`, {lit}`iterate_liftR_comp` — lifting respects composition.
* {lit}`rename_id`, {lit}`rename_rename` — the functor laws.
* {lit}`erase_rename` — renaming preserves erasure.

## Tags

logical framework, LF, de Bruijn index, renaming
-/

set_option doc.verso true

@[expose] public section

namespace Geb.LF

/-- An element of a list paired with positions and mapped is the map at the element and its
position. Stated through {name}`List.zipIdx`, whose element access does not depend on
{lit}`Classical.choice`, unlike that of {name}`List.mapIdx`. -/
theorem getElem_zipIdx_map {α β : Type} (l : List α) (f : α × ℕ → β) (k : ℕ)
    (h : k < (l.zipIdx.map f).length) :
    (l.zipIdx.map f)[k] = f (l[k]'(by simpa using h), k) := by
  simp only [List.getElem_map, List.getElem_zipIdx, zero_add]

/-- A list paired with positions and mapped has the list's length. -/
theorem length_zipIdx_map {α β : Type} (l : List α) (f : α × ℕ → β) :
    (l.zipIdx.map f).length = l.length := by
  simp

/-- An expression is the node of its label over its children. -/
theorem exists_node (e : Expr) : ∃ l cs, e = RoseTree.node l cs :=
  ⟨e.label, e.children, (RoseTree.node_label_children e).symm⟩

/-- The renaming of a node renames its label and each child, lifted under the variables the node
binds over it. -/
theorem rename_node (l : Label) (cs : List Expr) (ρ : ℕ → ℕ) :
    Expr.rename (RoseTree.node l cs) ρ =
      RoseTree.node (l.rename ρ) (cs.zipIdx.map fun p ↦ p.1.rename (liftR^[l.binders p.2] ρ)) := by
  rw [Expr.rename, RoseTree.elim_node]
  refine congrArg _ (List.ext_getElem (by simp) fun i _ _ ↦ ?_)
  simp only [List.getElem_map, List.getElem_zipIdx, zero_add]

/-- Renaming preserves the binders of a label. -/
@[simp] theorem Label.binders_rename (ρ : ℕ → ℕ) (l : Label) (k : ℕ) :
    (l.rename ρ).binders k = l.binders k := by
  cases l <;> rfl

/-- Lifting the composite of two renamings is composing their liftings. -/
theorem liftR_comp (σ ρ : ℕ → ℕ) : liftR (σ ∘ ρ) = liftR σ ∘ liftR ρ :=
  funext fun i ↦ by cases i <;> rfl

/-- Lifting the identity is the identity. -/
@[simp] theorem liftR_id : liftR id = id :=
  funext fun i ↦ by cases i <;> rfl

/-- Lifting the composite of two renamings under any number of binders is composing their
liftings. -/
theorem iterate_liftR_comp (n : ℕ) :
    ∀ σ ρ : ℕ → ℕ, liftR^[n] (σ ∘ ρ) = liftR^[n] σ ∘ liftR^[n] ρ :=
  Nat.rec (motive := fun n ↦ ∀ σ ρ : ℕ → ℕ, liftR^[n] (σ ∘ ρ) = liftR^[n] σ ∘ liftR^[n] ρ)
    (fun _ _ ↦ rfl)
    (fun n ih σ ρ ↦ by
      simp only [Function.iterate_succ_apply', ih, liftR_comp]) n

/-- Lifting the identity under any number of binders is the identity. -/
@[simp] theorem iterate_liftR_id (n : ℕ) : liftR^[n] id = id :=
  Nat.rec (motive := fun n ↦ liftR^[n] id = id) rfl
    (fun n ih ↦ by beta_reduce; rw [Function.iterate_succ_apply', ih, liftR_id]) n

/-- A renaming lifted under {lit}`j` binders fixes the {lit}`j` innermost variables and renames
the rest above them. -/
theorem iterate_liftR_apply (j : ℕ) :
    ∀ (σ : ℕ → ℕ) (i : ℕ), liftR^[j] σ i = if i < j then i else σ (i - j) + j :=
  Nat.rec (motive := fun j ↦ ∀ (σ : ℕ → ℕ) (i : ℕ),
      liftR^[j] σ i = if i < j then i else σ (i - j) + j)
    (fun σ i ↦ by simp)
    (fun j ih σ i ↦ by
      rw [Function.iterate_succ_apply']
      rcases i with _ | i
      · simp [liftR]
      · change liftR^[j] σ i + 1 = _
        rw [ih, Nat.add_sub_add_right]
        split_ifs <;> omega) j

/-- Renaming a label by the identity leaves it in place. -/
@[simp] theorem Label.rename_id (l : Label) : l.rename id = l := by
  rcases l with _ | _ | _ | (_ | _) <;> rfl

/-- Renaming a label twice is renaming it by the composite. -/
theorem Label.rename_rename (σ ρ : ℕ → ℕ) (l : Label) :
    (l.rename ρ).rename σ = l.rename (σ ∘ ρ) := by
  rcases l with _ | _ | _ | (_ | _) <;> rfl

/-- Renaming by the identity leaves an expression in place. -/
@[simp] theorem rename_id : ∀ e : Expr, e.rename id = e :=
  RoseTree.ind fun l cs ih ↦ by
    rw [rename_node, Label.rename_id]
    congr 1
    refine List.ext_getElem (by simp) fun i h₁ h₂ ↦ ?_
    simp only [getElem_zipIdx_map, iterate_liftR_id]
    exact ih _ (List.getElem_mem _)

/-- Renaming twice is renaming by the composite. -/
theorem rename_rename : ∀ (e : Expr) (σ ρ : ℕ → ℕ), (e.rename ρ).rename σ = e.rename (σ ∘ ρ) :=
  RoseTree.ind fun l cs ih σ ρ ↦ by
    rw [rename_node, rename_node, rename_node, Label.rename_rename]
    congr 1
    refine List.ext_getElem (by simp) fun i h₁ h₂ ↦ ?_
    simp only [getElem_zipIdx_map, Label.binders_rename, iterate_liftR_comp]
    exact ih _ (List.getElem_mem _) _ _

/-- Weakening after a renaming is renaming, lifted, after weakening. -/
theorem shift_rename (e : Expr) (σ : ℕ → ℕ) : (e.rename σ).shift = e.shift.rename (liftR σ) := by
  simp only [Expr.shift, rename_rename]
  rfl

/-- Weakening past {lit}`b` variables after a renaming is renaming, lifted under them, after the
weakening. -/
theorem iterate_shift_rename (b : ℕ) :
    ∀ (e : Expr) (σ : ℕ → ℕ),
      Expr.shift^[b] (e.rename σ) = (Expr.shift^[b] e).rename (liftR^[b] σ) :=
  Nat.rec (motive := fun b ↦ ∀ (e : Expr) (σ : ℕ → ℕ),
      Expr.shift^[b] (e.rename σ) = (Expr.shift^[b] e).rename (liftR^[b] σ))
    (fun _ _ ↦ rfl)
    (fun b ih e σ ↦ by
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', Function.iterate_succ_apply',
        ih, shift_rename]) b

/-- The computation rule of the erasure. -/
theorem erase_node (l : Label) (cs : List Expr) :
    Expr.erase (RoseTree.node l cs) = eraseStep l (cs.map Expr.erase) :=
  RoseTree.elim_node _ l cs

/-- Renaming preserves erasure. -/
theorem erase_rename : ∀ (e : Expr) (ρ : ℕ → ℕ), (e.rename ρ).erase = e.erase :=
  RoseTree.ind fun l cs ih ρ ↦ by
    rw [rename_node, erase_node, erase_node]
    rcases l with _ | _ | _ | (i | c)
    · rfl
    · rcases cs with _ | ⟨a, _ | ⟨b, _ | ⟨d, cs⟩⟩⟩
      · rfl
      · rfl
      · simp [eraseStep, Label.rename, ih a (by simp), ih b (by simp)]
      · simp [eraseStep, Label.rename]
    · rfl
    · rfl
    · rfl

end Geb.LF

end
