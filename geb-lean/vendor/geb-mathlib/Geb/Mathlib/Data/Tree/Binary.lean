/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Mathlib.Data.W.Basic

/-!
# Unlabelled binary trees as a W-type

The initial algebra of `F X = 1 + X × X`, presented as the W-type on a
two-element shape type. The presentation is the one this repository uses
for every self-referential datatype: a non-recursive shape type, a
direction family, and the W-type of that family, so that all recursion is
carried by `WType.elim` and `WType.rec`.

## Main definitions

* `BinTree.Shape` — the two node forms.
* `BinTree.Direction` — the child index type of each shape.
* `BinTree` — the trees themselves.
* `BinTree.leaf`, `BinTree.node` — the two constructors.
* `BinTree.size` — the number of nodes, leaves included.

## Main statements

* `BinTree.induction` — induction in the two-constructor presentation.

## Implementation notes

`Direction` names the child index family, following the convention of
this repository's polynomial-functor modules, where a shape's fibre is
its `Direction`.

`Direction` is `@[expose]`. The module system does not unfold a
non-exposed definition, so without it `WType.mk .leaf Fin.elim0` does not
elaborate: `Fin.elim0` cannot be checked against `Direction Shape.leaf`.

`Direction` sends `leaf` to `Fin 0` rather than to `Empty`, so that both
fibres lie in one family.

## Tags

binary tree, W-type, initial algebra, polynomial functor
-/

namespace BinTree

public section

/-- The node forms of an unlabelled binary tree. -/
inductive Shape
  /-- A leaf, with no children. -/
  | leaf
  /-- A node, with two children. -/
  | node

/-- The child index type of each shape: a leaf has none, a node has two. -/
@[expose] def Direction : Shape → Type
  | .leaf => Fin 0
  | .node => Fin 2

end

end BinTree

/-- Unlabelled binary trees: the initial algebra of `F X = 1 + X × X`. -/
@[expose] public def BinTree : Type := WType BinTree.Direction

namespace BinTree

public section

/-- The leaf. -/
@[expose] def leaf : BinTree := WType.mk .leaf Fin.elim0

/-- The node with left child `l` and right child `r`. -/
@[expose] def node (l r : BinTree) : BinTree :=
  WType.mk .node fun b : Fin 2 ↦ Fin.cases l (fun _ ↦ r) b

/-- The number of nodes, leaves included. Extracted upstream this would
sit beside `BinaryTree.numNodes`, `BinaryTree.numLeaves` and
`BinaryTree.height`, and it is none of the three: it is
`numNodes + numLeaves`. -/
@[expose] def size : BinTree → ℕ :=
  WType.elim ℕ fun x ↦
    match x with
    | ⟨.leaf, _⟩ => 1
    | ⟨.node, ch⟩ => ch (0 : Fin 2) + ch (1 : Fin 2) + 1

/-- Induction in the two-constructor presentation, so that a proof driven
by it need not mention the underlying shape and direction families. -/
theorem induction {motive : BinTree → Prop} (hleaf : motive leaf)
    (hnode : ∀ l r, motive l → motive r → motive (node l r)) :
    ∀ t, motive t :=
  WType.rec (motive := motive) fun s f ih ↦
    match s, f, ih with
    | .leaf, f, _ => by
        have : f = Fin.elim0 := funext (fun e ↦ e.elim0)
        subst this; exact hleaf
    | .node, f, ih => by
        have : (fun b : Fin 2 ↦ Fin.cases (f (0 : Fin 2))
            (fun _ ↦ f (1 : Fin 2)) b) = f :=
          funext fun b ↦ match b with
            | ⟨0, _⟩ => rfl
            | ⟨1, _⟩ => rfl
        exact this ▸ hnode (f (0 : Fin 2)) (f (1 : Fin 2))
          (ih (0 : Fin 2)) (ih (1 : Fin 2))

@[simp] theorem size_leaf : leaf.size = 1 := rfl

@[simp] theorem size_node (l r : BinTree) :
    (node l r).size = l.size + r.size + 1 := rfl

end

end BinTree
