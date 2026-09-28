/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
-- Modified from geb-mathlib by scripts/geb-mathlib-backport.patch.
module

public import Geb.Prototypes.Computability.SizeBounded.Logspace.WTree.Events
public import Geb.Prototypes.Computability.SizeBounded.Logspace.WTree.Positions

set_option doc.verso true in
/-!
# The scan over the nodes of an encoded tree

The streaming scanner extended by two registers: the number of fork tags read
since the last leaf completed, which at a leaf's tag is the number of children
of the node the leaf labels, and a flag that is the conjunction of a check at
every node. The check receives the location of the node's label, at the
completion of the header, and its number of children; on an encoded tree the
flag is the conjunction of the check over the tree's nodes.

# Main definitions

* {lit}`NodeReg`, {lit}`nodeUpd`, {lit}`nodeScan` — the registers, their
  update at an event, and the scan of a word.

# Main statements

* {lit}`nodeUpd_silent` — the registers are unchanged by no event.
* {lit}`foldl_nodeStep_encode` — the scan over an encoded tree from a state in
  the tree phase: the flag is conjoined with the check at every node, the node
  the tree's open spine belongs to at the spine's length plus the forks read
  before it.
* {lit}`nodeScan_ok_iff` — the scan of an encoded tree accepts exactly when
  the check holds at every node.

# Tags

W-type, binary tree, bitstring, streaming recognizer
-/

set_option doc.verso true

namespace Geb.SizeBounded.Logspace.WTree

open Geb.BitTree (Tree leaf fork tree_ind)
open Geb.BitTree.Elias (encode encodeNat)
open Geb.BitTree.Elias.Scanner (Mode State step finish)

public section

/-- The registers: the fork tags read since the last leaf completed, and the
flag. -/
structure NodeReg where
  /-- The fork tags read since the last leaf completed. -/
  k : ℕ
  /-- The conjunction of the check at the nodes met so far. -/
  ok : Bool
  deriving DecidableEq, Repr

attribute [nolint unusedArguments] instReprNodeReg.repr

/-- The update at an event: a fork tag raises the count, a completed leaf
resets it, and a completed header conjoins the check at the label beginning at
the next bit, with the count. -/
@[expose] def nodeUpd (check : Loc → ℕ → Bool) (pos : ℕ) (e : Event) (x : NodeReg) : NodeReg :=
  ⟨if e.fork then x.k + 1 else if e.done then 0 else x.k,
    match e.payload with
    | some L => x.ok && check ⟨pos + 1, L⟩ x.k
    | none => x.ok⟩

/-- No event leaves the registers unchanged. -/
theorem nodeUpd_silent (check : Loc → ℕ → Bool) (pos : ℕ) (x : NodeReg) :
    nodeUpd check pos .silent x = x := rfl

/-- The scan of a word, from one pending root with no fork read and the flag
set. -/
@[expose] def nodeScan (check : Loc → ℕ → Bool) (w : List Bool) : Ext NodeReg :=
  w.foldl (extStep (nodeUpd check)) ⟨(.tree, 1), 0, ⟨0, true⟩⟩

variable (check : Loc → ℕ → Bool)

/-- The scan over an encoded tree from a state in the tree phase with a
positive pending count: the phase completes one pending subtree, the position
advances by the encoding, the count is reset, and the flag is conjoined with
the check at every node completed inside the tree and at the node the open
spine belongs to, whose children are the spine's plus the forks read before
the tree. -/
theorem foldl_nodeStep_encode : ∀ (t : Tree) (m p d : ℕ) (ok : Bool), 0 < m →
    ∃ ok' : Bool, (encode t).foldl (extStep (nodeUpd check)) ⟨(.tree, m), p, ⟨d, ok⟩⟩ =
      ⟨finish m, p + (encode t).length, ⟨0, ok'⟩⟩ ∧
      (ok' = true ↔ ok = true ∧ (∀ n ∈ (roseAt t p).inner, check n.label n.k = true) ∧
        check (roseAt t p).label (d + (roseAt t p).children.length) = true) :=
  tree_ind (fun s m p d ok _ ↦ by
      refine ⟨ok && check ⟨p + 1 + (encodeNat s.length).length, s.length⟩ d, ?_, ?_⟩
      · rw [Geb.BitTree.Elias.encode_leaf, List.foldl_cons, List.foldl_append]
        change (s.foldl (extStep (nodeUpd check))
          ((encodeNat s.length).foldl (extStep (nodeUpd check))
            ⟨(.zeros 0, m), p + 1, nodeUpd check p ⟨false, true, none, false⟩ ⟨d, ok⟩⟩)) = _
        rw [foldl_extStep_encodeNat (nodeUpd check) (nodeUpd_silent check)]
        cases s with
        | nil =>
          simp only [List.length_nil, List.foldl_nil, List.length_cons, List.length_append,
            Nat.add_zero, nodeUpd, ↓reduceIte, decide_true, Bool.false_eq_true]
          rfl
        | cons b bs =>
          rw [if_neg (by simp), foldl_extStep_payload (nodeUpd check) (nodeUpd_silent check)
            (b :: bs) m _ _ (List.cons_ne_nil b bs)]
          have hp' : p + 1 + (encodeNat (bs.length + 1)).length - 1 + 1 =
              p + 1 + (encodeNat (bs.length + 1)).length := by
            have := Geb.BitTree.Elias.length_encodeNat_pos (bs.length + 1)
            omega
          simp only [List.length_cons, List.length_append, nodeUpd, ↓reduceIte,
            Bool.false_eq_true, decide_false, hp', Nat.add_one_ne_zero]
          congr 1
          omega
      · rw [roseAt_leaf, Bool.and_eq_true]
        dsimp only
        exact ⟨fun ⟨h₁, h₂⟩ ↦ ⟨h₁, fun _ h ↦ absurd h List.not_mem_nil, h₂⟩,
          fun ⟨h₁, _, h₂⟩ ↦ ⟨h₁, h₂⟩⟩)
    fun l r ihl ihr m p d ok hm ↦ by
      obtain ⟨ok₁, hl, hl'⟩ := ihl (m + 1) (p + 1) (d + 1) ok (Nat.succ_pos m)
      have hf : finish (m + 1) = (.tree, m) := by
        rw [Geb.BitTree.Elias.Scanner.finish, if_neg (by omega), Nat.add_sub_cancel]
      rw [hf] at hl
      obtain ⟨ok₂, hr, hr'⟩ := ihr m (p + 1 + (encode l).length) 0 ok₁ hm
      refine ⟨ok₂, ?_, ?_⟩
      · rw [Geb.BitTree.Elias.encode_fork, List.foldl_cons, List.foldl_append]
        change (encode r).foldl (extStep (nodeUpd check))
          ((encode l).foldl (extStep (nodeUpd check))
            ⟨(.tree, m + 1), p + 1, nodeUpd check p ⟨true, false, none, false⟩ ⟨d, ok⟩⟩) = _
        rw [show nodeUpd check p ⟨true, false, none, false⟩ ⟨d, ok⟩ = ⟨d + 1, ok⟩ from rfl, hl, hr,
          List.length_cons, List.length_append,
          show p + 1 + (encode l).length + (encode r).length =
            p + ((encode l).length + (encode r).length + 1) by omega]
      · rw [hr', hl', roseAt_fork]
        dsimp only
        rw [List.length_append, List.length_singleton, Nat.zero_add,
          show d + 1 + (roseAt l (p + 1)).children.length =
            d + ((roseAt l (p + 1)).children.length + 1) by omega]
        constructor
        · rintro ⟨⟨h₁, h₂, h₃⟩, h₄, h₅⟩
          refine ⟨h₁, fun n hn ↦ ?_, h₃⟩
          rw [List.mem_append, List.mem_append, List.mem_singleton] at hn
          rcases hn with (hn | hn) | rfl
          · exact h₂ n hn
          · exact h₄ n hn
          · exact h₅
        · rintro ⟨h₁, h₂, h₃⟩
          have m₁ : ∀ n ∈ (roseAt l (p + 1)).inner, check n.label n.k = true := fun n hn ↦
            h₂ n (by rw [List.mem_append, List.mem_append]; exact Or.inl (Or.inl hn))
          have m₂ : ∀ n ∈ (roseAt r (p + 1 + (encode l).length)).inner,
              check n.label n.k = true := fun n hn ↦
            h₂ n (by rw [List.mem_append, List.mem_append]; exact Or.inl (Or.inr hn))
          have m₃ := h₂ ⟨(roseAt r (p + 1 + (encode l).length)).label,
              (roseAt r (p + 1 + (encode l).length)).children⟩
            (by rw [List.mem_append, List.mem_singleton]; exact Or.inr rfl)
          exact ⟨⟨h₁, m₁, h₃⟩, m₂, m₃⟩

/-- The scan of an encoded tree accepts exactly when the check holds at every
node. -/
theorem nodeScan_ok_iff (t : Tree) :
    (nodeScan check (encode t)).extra.ok = true ↔ ∀ n ∈ nodes t 0, check n.label n.k = true := by
  obtain ⟨ok', h, h'⟩ := foldl_nodeStep_encode check t 1 0 0 true Nat.one_pos
  unfold nodeScan
  rw [h]
  change ok' = true ↔ _
  rw [h', Nat.zero_add]
  unfold nodes
  constructor
  · rintro ⟨_, h₁, h₂⟩ n hn
    rw [List.mem_append, List.mem_singleton] at hn
    rcases hn with hn | rfl
    · exact h₁ n hn
    · exact h₂
  · intro h
    exact ⟨rfl, fun n hn ↦ h n (by rw [List.mem_append]; exact Or.inl hn),
      h ⟨(roseAt t 0).label, (roseAt t 0).children⟩
        (by rw [List.mem_append, List.mem_singleton]; exact Or.inr rfl)⟩

end

end Geb.SizeBounded.Logspace.WTree
