/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.SizeBounded.Logspace.WTree.Nodes
public import Geb.Prototypes.Computability.SizeBounded.Logspace.WTree.Children

set_option doc.verso true in
/-!
# The recognizer of the W-trees of a coded signature

A word spells an admissible W-tree of a coded signature exactly when it is
the encoding of a binary tree of labels, every node's label decodes to a shape
with as many directions as the node has children, and every child's label
lies over the index the parent's label prescribes at the child's position.
The recognizer composes the three: the streaming scanner of the encoding, and
the scan over the nodes whose check at a node is the label condition together
with the scan over the node's children. Each scan reads the word from its
beginning with a fixed number of counters, the scan over the children once
per node, so the recognizer reads the word a number of times quadratic in its
length and keeps a fixed number of counters bounded by its length, which is
what a logarithmic-space machine keeps.

# Main definitions

* {lit}`CodedSig.nodeCheck` — the check at a node: its label is in order
  and its children are.
* {lit}`CodedSig.recognize` — the recognizer.

# Main statements

* {lit}`CodedSig.recognize_iff` — the recognizer accepts exactly the
  spellings of admissible W-trees.

# Tags

W-type, slice polynomial functor, bitstring, recognizer, logspace
-/

set_option doc.verso true

namespace Geb.SizeBounded.Logspace.WTree

namespace CodedSig

variable {I : Type} [DecidableEq I] (C : CodedSig I)

public section

/-- The check at a node of a word: its label decodes to a shape with as many
directions as the node has children, and the scan over its children accepts,
each child's label lying over the index the node's label prescribes at the
child's position. -/
@[expose] def nodeCheck (w : List Bool) (l : Loc) (k : ℕ) : Bool :=
  C.labelSpec (labelAt w l) k &&
    (childScan l k (fun l' j ↦ C.edgeSpec (labelAt w l) j (labelAt w l')) w).extra.ok

/-- The recognizer: the word encodes a binary tree of labels, and the scan over
its nodes accepts. -/
@[expose] def recognize (w : List Bool) : Bool :=
  Geb.BitTree.Elias.Scanner.validBool w && (nodeScan (C.nodeCheck w) w).extra.ok

/-- The recognizer accepts exactly the spellings of admissible W-trees. -/
theorem recognize_iff (w : List Bool) :
    C.recognize w = true ↔ ∃ t, C.P.WValid t ∧ C.spell t = w := by
  rw [C.isW_iff, recognize, Bool.and_eq_true, Geb.BitTree.Elias.Scanner.validBool_iff]
  constructor
  · rintro ⟨⟨t, rfl⟩, h⟩
    refine ⟨t, rfl, ?_, ?_⟩
    · rw [C.labelsOk_iff_nodes]
      intro n hn
      have := (nodeScan_ok_iff (C.nodeCheck (Geb.BitTree.Elias.encode t)) t).mp h n hn
      unfold nodeCheck at this
      rw [Bool.and_eq_true] at this
      exact this.1
    · rw [C.edgesOk_iff_nodes]
      intro n hn
      have := (nodeScan_ok_iff (C.nodeCheck (Geb.BitTree.Elias.encode t)) t).mp h n hn
      unfold nodeCheck at this
      rw [Bool.and_eq_true] at this
      exact (childScan_ok_iff _ t n hn).mp this.2
  · rintro ⟨t, rfl, hl, he⟩
    refine ⟨⟨t, rfl⟩, ?_⟩
    rw [nodeScan_ok_iff]
    intro n hn
    unfold nodeCheck
    rw [Bool.and_eq_true]
    exact ⟨(C.labelsOk_iff_nodes t).mp hl n hn,
      (childScan_ok_iff _ t n hn).mpr ((C.edgesOk_iff_nodes t).mp he n hn)⟩

end

end CodedSig

end Geb.SizeBounded.Logspace.WTree
