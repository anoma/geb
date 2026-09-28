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
* {lit}`RoseTree.para` — the paramorphism, whose step also sees each child as a
  tree.
* {lit}`RoseTree.map` — the functor's action on the labels.

# Main statements

* {lit}`RoseTree.node_eq_mk`, {lit}`RoseTree.node_label_children` — a node over
  a tabulation is the tabulated tree; a tree is the node of its label over its
  children.
* {lit}`RoseTree.ind` — induction over nodes and their lists of children.
* {lit}`RoseTree.elim_node` — the computation rule of the fold.
* {lit}`RoseTree.para_node` — the computation rule of the paramorphism.

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

universe u

variable {α : Type} {β : Type u}

/-- The node with a label over a list of children. The children are tabulated in an array
built once, so that each is reached in constant time. -/
def node (a : α) (cs : List (RoseTree α)) : RoseTree α :=
  let arr := cs.toArray
  WType.mk (a, cs.length) fun i ↦ arr[i.1]'(by simp [arr])

/-- The label of a tree. -/
def label : RoseTree α → α
  | ⟨(a, _), _⟩ => a

/-- The children of a tree, in order. -/
def children : RoseTree α → List (RoseTree α)
  | ⟨_, f⟩ => List.ofFn f

@[simp] theorem label_node (a : α) (cs : List (RoseTree α)) : (node a cs).label = a := rfl

@[simp] theorem children_node (a : α) (cs : List (RoseTree α)) :
    (node a cs).children = cs := by
  simp only [children, node, List.getElem_toArray, List.ofFn_getElem]

/-- A node over a list tabulating a direction function is the tree of that
function. -/
theorem node_eq_mk (a : α) (cs : List (RoseTree α)) {n : ℕ} (hlen : cs.length = n)
    (f : Fin n → RoseTree α) (key : ∀ i : Fin n, cs[i.1]? = some (f i)) :
    node a cs = WType.mk (a, n) f := by
  subst hlen
  unfold node
  dsimp only
  congr 1
  funext i
  rw [List.getElem_toArray]
  exact Option.some.inj ((List.getElem?_eq_getElem i.2).symm.trans (key i))

/-- A tree is the node of its label over its children. -/
@[simp] theorem node_label_children (t : RoseTree α) : node t.label t.children = t := by
  obtain ⟨⟨a, n⟩, f⟩ := t
  exact node_eq_mk a (List.ofFn f) List.length_ofFn f fun i ↦ by simp

/-- A node is a tree exactly when its label and children are the tree's. -/
theorem node_eq_iff {a : α} {cs : List (RoseTree α)} {t : RoseTree α} :
    node a cs = t ↔ a = t.label ∧ cs = t.children :=
  ⟨fun h ↦ h ▸ ⟨(label_node a cs).symm, (children_node a cs).symm⟩,
    fun ⟨h₁, h₂⟩ ↦ by rw [h₁, h₂, node_label_children]⟩

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
  simp [elim, node, WType.elim, List.getElem_toArray, List.ofFn_getElem_eq_map]

/-- The algebra of the paramorphism: rebuild the node from the children's rebuilt subtrees,
and apply the step to the children paired with their results. -/
def paraStep (f : α → List (RoseTree α × β) → β) (a : α) (rs : List (RoseTree α × β)) :
    RoseTree α × β :=
  (node a (rs.map Prod.fst), f a rs)

/-- The paramorphism: the fold whose step sees each child as a tree together with its
result. It is the fold at the carrier of pairs, so each child's result is computed once. -/
def para (f : α → List (RoseTree α × β) → β) (t : RoseTree α) : β :=
  (elim (paraStep f) t).2

/-- The first component of the paramorphism's carrier rebuilds its input. -/
theorem elim_paraStep_fst (f : α → List (RoseTree α × β) → β) (t : RoseTree α) :
    (elim (paraStep f) t).1 = t :=
  ind (P := fun t ↦ (elim (paraStep f) t).1 = t) (fun a cs ih ↦ by
    simp only [elim_node, paraStep, List.map_map]
    exact congrArg (node a) ((List.map_congr_left fun c hc ↦ ih c hc).trans cs.map_id)) t

/-- The computation rule of the paramorphism. -/
@[simp] theorem para_node (f : α → List (RoseTree α × β) → β) (a : α)
    (cs : List (RoseTree α)) : para f (node a cs) = f a (cs.map fun c ↦ (c, para f c)) := by
  simp only [para, elim_node, paraStep]
  exact congrArg (f a) (List.map_congr_left fun c _ ↦
    Prod.ext (elim_paraStep_fst f c) rfl)

/-- The tree of the same shape with a function applied at each label: the functor's action. -/
def map {γ : Type} (f : α → γ) : RoseTree α → RoseTree γ := elim fun a cs ↦ node (f a) cs

/-- The computation rule of the map. -/
@[simp] theorem map_node {γ : Type} (f : α → γ) (a : α) (cs : List (RoseTree α)) :
    map f (node a cs) = node (f a) (cs.map (map f)) := by
  simp [map]

/-- The label of a mapped tree is the mapped label. -/
@[simp] theorem label_map {γ : Type} (f : α → γ) (t : RoseTree α) :
    (map f t).label = f t.label := by
  rw [← node_label_children t, map_node, label_node, label_node]

/-- The children of a mapped tree are the mapped children. -/
@[simp] theorem children_map {γ : Type} (f : α → γ) (t : RoseTree α) :
    (map f t).children = t.children.map (map f) := by
  rw [← node_label_children t, map_node, children_node, children_node]

/-- Mapping twice is mapping by the composite. -/
theorem map_map {γ δ : Type} (f : α → γ) (g : γ → δ) (t : RoseTree α) :
    map g (map f t) = map (g ∘ f) t :=
  ind (P := fun t ↦ map g (map f t) = map (g ∘ f) t) (fun a cs ih ↦ by
    simp only [map_node, List.map_map]
    exact congrArg _ (List.map_congr_left fun c hc ↦ ih c hc)) t

/-- Mapping by the identity is the identity. -/
@[simp] theorem map_id (t : RoseTree α) : map id t = t :=
  ind (P := fun t ↦ map id t = t) (fun a cs ih ↦ by
    simp only [map_node, id]
    exact congrArg _ ((List.map_congr_left fun c hc ↦ ih c hc).trans cs.map_id)) t

end RoseTree

end Geb

end
