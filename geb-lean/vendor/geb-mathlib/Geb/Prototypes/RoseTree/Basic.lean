/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Mathlib.Data.W.Basic

set_option doc.verso true in
/-!
# Rose trees as W-types

A rose tree over a label type is a node carrying a label and a list of
children. It is the W-type of the signature whose shapes are a label paired
with an arity, each shape having as many directions as its arity; the list
of children is the tabulation of the direction function. Every other
representation of rose trees is measured against this one: a representation
is a type with a computable isomorphism to {lit}`RoseTree`.

# Main definitions

* {lit}`RoseTree.Sig` — the signature, a label paired with an arity.
* {lit}`RoseTree` — the W-type of the signature.
* {lit}`RoseTree.node`, {lit}`RoseTree.label`, {lit}`RoseTree.children` — the
  constructor from a list of children and its two projections.
* {lit}`RoseTree.elim` — the fold, whose step sees the label and the list of
  the children's results.

# Main statements

* {lit}`RoseTree.node_eq_mk`, {lit}`RoseTree.node_label_children` — a node over
  a tabulation is the tabulated tree; a tree is the node of its label over its
  children.
* {lit}`RoseTree.ind` — induction over nodes and their lists of children.
* {lit}`RoseTree.elim_node` — the computation rule of the fold.

# Tags

rose tree, W-type
-/

set_option doc.verso true

@[expose] public section

namespace Geb

/-- The signature of rose trees over {lit}`α`: a shape is a label with an
arity, and a direction is a position below the arity. -/
abbrev RoseTree.Sig (α : Type) : α × ℕ → Type := fun p ↦ Fin p.2

/-- A rose tree: the W-type of {name}`RoseTree.Sig`. -/
abbrev RoseTree (α : Type) : Type := WType (RoseTree.Sig α)

namespace RoseTree

variable {α β : Type}

/-- The node with a label over a list of children. -/
def node (a : α) (cs : List (RoseTree α)) : RoseTree α :=
  WType.mk (a, cs.length) fun i ↦ cs[i]

/-- The label of a tree. -/
def label : RoseTree α → α
  | ⟨(a, _), _⟩ => a

/-- The children of a tree, in order. -/
def children : RoseTree α → List (RoseTree α)
  | ⟨_, f⟩ => List.ofFn f

@[simp] theorem label_node (a : α) (cs : List (RoseTree α)) : (node a cs).label = a := rfl

@[simp] theorem children_node (a : α) (cs : List (RoseTree α)) :
    (node a cs).children = cs := List.ofFn_getElem

/-- A node over a list tabulating a direction function is the tree of that
function. -/
theorem node_eq_mk (a : α) (cs : List (RoseTree α)) {n : ℕ} (hlen : cs.length = n)
    (f : Fin n → RoseTree α) (key : ∀ i : Fin n, cs[i.1]? = some (f i)) :
    node a cs = WType.mk (a, n) f := by
  subst hlen
  unfold node
  congr 1
  funext i
  exact Option.some.inj ((List.getElem?_eq_getElem i.2).symm.trans (key i))

/-- A tree is the node of its label over its children. -/
@[simp] theorem node_label_children (t : RoseTree α) : node t.label t.children = t := by
  obtain ⟨⟨a, n⟩, f⟩ := t
  exact node_eq_mk a (List.ofFn f) List.length_ofFn f fun i ↦ by simp

/-- Induction: a property of every node over children that have it holds of
every tree. -/
theorem ind {P : RoseTree α → Prop} (h : ∀ a cs, (∀ c ∈ cs, P c) → P (node a cs)) :
    ∀ t, P t :=
  WType.rec fun x f ih ↦ by
    obtain ⟨a, n⟩ := x
    rw [← node_eq_mk a (List.ofFn f) List.length_ofFn f fun i ↦ by simp]
    exact h a _ fun c hc ↦ by
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hc
      exact ih i

/-- The fold: the step sees the label and the list of the children's
results. -/
def elim (f : α → List β → β) : RoseTree α → β :=
  WType.elim β fun x ↦ f x.1.1 (List.ofFn x.2)

/-- The computation rule of the fold. -/
@[simp] theorem elim_node (f : α → List β → β) (a : α) (cs : List (RoseTree α)) :
    elim f (node a cs) = f a (cs.map (elim f)) := by
  simp [elim, node, WType.elim, List.ofFn_getElem_eq_map]

end RoseTree

end Geb

end
