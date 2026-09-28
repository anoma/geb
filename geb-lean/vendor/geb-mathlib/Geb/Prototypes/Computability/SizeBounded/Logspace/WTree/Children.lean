/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
-- Modified from geb-mathlib by scripts/geb-mathlib-backport.patch.
module

public import Geb.Prototypes.Computability.SizeBounded.Logspace.WTree.Events
public import Geb.Prototypes.Computability.SizeBounded.Logspace.WTree.Positions
public import Geb.Prototypes.Computability.BitTree.Elias.ScannerCorrect

set_option doc.verso true in
/-!
# The scan over the children of one node

The streaming scanner extended by registers that find the children of the
node whose label is at a given location and check each against the node. The
scan waits for the header completing at that location, reads the node's
payload, and then reads the children one by one: a child begins with its fork
tags, and its label's header raises the check, with the child's position among
the children; the child ends when the leaves completed since it began exceed
the fork tags read since it began by one, which is when its last pending
subtree closes, and never before. Both counts are kept from the child's
beginning, so that each rises and neither falls, and after the last child the
scan is done.

# Main definitions

* {lit}`CMode`, {lit}`ChildReg`, {lit}`afterChildren`, {lit}`childUpd`,
  {lit}`childScan` — the modes and registers, the registers after a number of
  children, the update at an event, and the scan of a word.
* {lit}`edgesAll` — the conjunction of the check over a list of children.

# Main statements

* {lit}`childUpd_silent`, {lit}`childUpd_tag` — no event, and a leaf tag,
  leave the registers unchanged.
* {lit}`edgesAll_concat`, {lit}`edgesAll_iff` — the conjunction over one more
  child, and its meaning.
* {lit}`foldl_child_done`, {lit}`foldl_child_body`, {lit}`foldl_child_spine`,
  {lit}`foldl_child_before_miss`, {lit}`foldl_child_root`,
  {lit}`foldl_child_inner` — the scan over an encoded tree from each mode: done
  stays; inside a child the counts advance by the tree's forks and leaves and
  the child ends exactly when the counts began equal; at a child's beginning
  the check is raised at its label; before the node, a tree without the label
  is passed over, the tree whose open spine belongs to the node reads the
  node's payload and its children on the spine, and a tree with the node
  completed inside reads all its children.
* {lit}`childScan_ok_iff` — the scan of an encoded tree for one of its nodes
  accepts exactly when the check holds at each of the node's children.

# Tags

W-type, binary tree, bitstring, streaming recognizer, monotone counter
-/

set_option doc.verso true

namespace Geb.SizeBounded.Logspace.WTree

open Geb.BitTree (Tree leaf fork tree_ind counts)
open Geb.BitTree.Elias (encode encodeNat)
open Geb.BitTree.Elias.Scanner (Mode State step finish)

public section

/-- The modes: before the node's label; inside its payload; at a child's fork
tags; inside a child past its label's header; and after the last child. -/
inductive CMode where
  | before
  | label
  | spine
  | body
  | done
  deriving DecidableEq, Repr

/-- The registers: the mode, the fork tags read and the leaves completed since
the current child began, the number of children completed, and the flag. -/
structure ChildReg where
  /-- The mode. -/
  mode : CMode
  /-- The fork tags read since the current child began. -/
  fc : ℕ
  /-- The leaves completed since the current child began. -/
  lc : ℕ
  /-- The number of children completed. -/
  j : ℕ
  /-- The conjunction of the check at the children met so far. -/
  ok : Bool
  deriving DecidableEq, Repr

attribute [nolint unusedArguments] instReprChildReg.repr

/-- The registers after a number of children of a node with a given number:
done when they are all, else at the next child's fork tags with the counts at
zero. -/
@[expose] def afterChildren (k j : ℕ) (ok : Bool) : ChildReg :=
  ⟨if j = k then .done else .spine, 0, 0, j, ok⟩

/-- The update at an event, for the node with the label at the target location
and the given number of children. Before the node, the header completing at
the target opens the payload, or, when the payload is empty, the children.
Inside the payload, the leaf completing opens the children. At a child's fork
tags, a fork tag raises the fork count, and the header completing raises the
check at the label with the child's position and opens the child's body, or,
when the payload is empty and no fork tag was read, completes the child. Inside
a child, a fork tag raises the fork count, and a leaf completing raises the leaf
count or, when the counts are equal, completes the child. -/
@[expose] def childUpd (target : Loc) (k : ℕ) (edge : Loc → ℕ → Bool) (pos : ℕ) (e : Event)
    (x : ChildReg) : ChildReg :=
  match x.mode with
  | .before =>
    match e.payload with
    | some _ =>
      if pos + 1 = target.pos then
        if e.done then afterChildren k 0 x.ok else ⟨.label, 0, 0, 0, x.ok⟩
      else x
    | none => x
  | .label => if e.done then afterChildren k 0 x.ok else x
  | .spine =>
    match e.payload with
    | some L =>
      if e.done then
        if x.fc = 0 then afterChildren k (x.j + 1) (x.ok && edge ⟨pos + 1, L⟩ x.j)
        else ⟨.body, x.fc, 1, x.j, x.ok && edge ⟨pos + 1, L⟩ x.j⟩
      else ⟨.body, x.fc, 0, x.j, x.ok && edge ⟨pos + 1, L⟩ x.j⟩
    | none => if e.fork then ⟨.spine, x.fc + 1, x.lc, x.j, x.ok⟩ else x
  | .body =>
    if e.fork then ⟨.body, x.fc + 1, x.lc, x.j, x.ok⟩
    else if e.done then
      if x.lc = x.fc then afterChildren k (x.j + 1) x.ok else ⟨.body, x.fc, x.lc + 1, x.j, x.ok⟩
    else x
  | .done => x

/-- The scan of a word for the node with the label at the target location and
the given number of children. -/
@[expose] def childScan (target : Loc) (k : ℕ) (edge : Loc → ℕ → Bool) (w : List Bool) :
    Ext ChildReg :=
  w.foldl (extStep (childUpd target k edge)) ⟨(.tree, 1), 0, ⟨.before, 0, 0, 0, true⟩⟩

/-- The conjunction of the check over a list of children, each at its
position. -/
@[expose] def edgesAll (edge : Loc → ℕ → Bool) (cs : List Loc) : Bool :=
  (cs.foldl (fun (acc : Bool × ℕ) l ↦ (acc.1 && edge l acc.2, acc.2 + 1)) (true, 0)).1

/-- After fewer children than the node has, the scan is at the next child's
fork tags. -/
theorem afterChildren_of_ne (k j : ℕ) (ok : Bool) (h : j ≠ k) :
    afterChildren k j ok = ⟨.spine, 0, 0, j, ok⟩ := by
  unfold afterChildren
  rw [if_neg h]

/-- After all the node's children, the scan is done. -/
theorem afterChildren_self (k : ℕ) (ok : Bool) : afterChildren k k ok = ⟨.done, 0, 0, k, ok⟩ := by
  unfold afterChildren
  rw [if_pos rfl]

variable (target : Loc) (k : ℕ) (edge : Loc → ℕ → Bool)

/-- No event leaves the registers unchanged. -/
theorem childUpd_silent (pos : ℕ) (x : ChildReg) : childUpd target k edge pos .silent x = x := by
  rcases x with ⟨mode, fc, lc, j, ok⟩
  cases mode <;> rfl

/-- A leaf tag leaves the registers unchanged. -/
theorem childUpd_tag (pos : ℕ) (x : ChildReg) :
    childUpd target k edge pos ⟨false, true, none, false⟩ x = x := by
  rcases x with ⟨mode, fc, lc, j, ok⟩
  cases mode <;> rfl

/-- The position component of the fold behind the conjunction counts the
children. -/
theorem edgesAll_foldl_snd (cs : List Loc) : ∀ (acc : Bool) (j : ℕ),
    (cs.foldl (fun (acc : Bool × ℕ) l ↦ (acc.1 && edge l acc.2, acc.2 + 1)) (acc, j)).2 =
      j + cs.length :=
  List.rec (fun _ _ ↦ rfl) (fun l cs ih acc j ↦ by
    rw [List.foldl_cons, ih, List.length_cons]
    omega) cs

/-- The conjunction over one more child. -/
theorem edgesAll_concat (cs : List Loc) (l : Loc) :
    edgesAll edge (cs ++ [l]) = (edgesAll edge cs && edge l cs.length) := by
  unfold edgesAll
  rw [List.foldl_concat, edgesAll_foldl_snd, Nat.zero_add]

/-- The conjunction holds exactly when the check holds at each child. -/
theorem edgesAll_iff (cs : List Loc) :
    edgesAll edge cs = true ↔ ∀ (i : ℕ) (h : i < cs.length), edge cs[i] i = true := by
  have key : ∀ (cs : List Loc) (acc : Bool) (j : ℕ),
      (cs.foldl (fun (acc : Bool × ℕ) l ↦ (acc.1 && edge l acc.2, acc.2 + 1)) (acc, j)).1 = true ↔
        acc = true ∧ ∀ (i : ℕ) (h : i < cs.length), edge cs[i] (j + i) = true :=
    List.rec (fun acc j ↦ ⟨fun h ↦ ⟨h, fun _ h ↦ absurd h (Nat.not_lt_zero _)⟩, fun h ↦ h.1⟩)
      fun l cs ih acc j ↦ by
        rw [List.foldl_cons, ih, Bool.and_eq_true]
        constructor
        · rintro ⟨⟨h₁, h₂⟩, h₃⟩
          refine ⟨h₁, fun i hi ↦ ?_⟩
          cases i with
          | zero => exact h₂
          | succ i =>
            rw [List.getElem_cons_succ, show j + (i + 1) = j + 1 + i by omega]
            exact h₃ i (by rw [List.length_cons] at hi; omega)
        · rintro ⟨h₁, h₂⟩
          refine ⟨⟨h₁, h₂ 0 (by rw [List.length_cons]; omega)⟩, fun i hi ↦ ?_⟩
          have := h₂ (i + 1) (by rw [List.length_cons]; omega)
          rwa [List.getElem_cons_succ, show j + (i + 1) = j + 1 + i by omega] at this
  unfold edgesAll
  rw [key]
  simp only [Nat.zero_add, true_and]

/-- Once done, the scan stays done. -/
theorem foldl_child_done (w : List Bool) : ∀ (σ : State) (p fc lc j : ℕ) (ok : Bool),
    w.foldl (extStep (childUpd target k edge)) ⟨σ, p, ⟨.done, fc, lc, j, ok⟩⟩ =
      ⟨w.foldl step σ, p + w.length, ⟨.done, fc, lc, j, ok⟩⟩ :=
  List.rec (fun _ _ _ _ _ _ ↦ rfl) (fun b w ih σ p fc lc j ok ↦ by
    rw [List.foldl_cons, List.foldl_cons]
    change w.foldl (extStep (childUpd target k edge))
      ⟨step σ b, p + 1, childUpd target k edge p (eventS σ b) ⟨.done, fc, lc, j, ok⟩⟩ = _
    rw [show childUpd target k edge p (eventS σ b) ⟨.done, fc, lc, j, ok⟩ = ⟨.done, fc, lc, j, ok⟩
      from rfl, ih, List.length_cons, Nat.add_assoc, Nat.add_comm 1]) w

/-- Inside a child, an encoded tree advances the counts by its forks and its
leaves, and completes the child exactly when the counts were equal, which is
when the tree is the child's last pending subtree. -/
theorem foldl_child_body : ∀ (t : Tree) (m p fc lc j : ℕ) (ok : Bool), 0 < m → lc ≤ fc →
    (encode t).foldl (extStep (childUpd target k edge)) ⟨(.tree, m), p, ⟨.body, fc, lc, j, ok⟩⟩ =
      ⟨finish m, p + (encode t).length,
        if lc = fc then afterChildren k (j + 1) ok
        else ⟨.body, fc + (counts t).1, lc + (counts t).1 + 1, j, ok⟩⟩ :=
  tree_ind (fun s m p fc lc j ok _ _ ↦ by
      rw [Geb.BitTree.Elias.encode_leaf, List.foldl_cons, List.foldl_append]
      change (s.foldl (extStep (childUpd target k edge))
        ((encodeNat s.length).foldl (extStep (childUpd target k edge))
          ⟨(.zeros 0, m), p + 1,
            childUpd target k edge p ⟨false, true, none, false⟩ ⟨.body, fc, lc, j, ok⟩⟩)) = _
      rw [childUpd_tag, foldl_extStep_encodeNat _ (childUpd_silent target k edge)]
      cases s with
      | nil =>
        simp only [List.length_nil, List.foldl_nil, List.length_cons, List.length_append,
          Nat.add_zero, childUpd, ↓reduceIte, decide_true, Bool.false_eq_true, counts]
        rfl
      | cons b bs =>
        rw [if_neg (by simp), foldl_extStep_payload _ (childUpd_silent target k edge)
          (b :: bs) m _ _ (List.cons_ne_nil b bs)]
        simp only [List.length_cons, List.length_append, childUpd, ↓reduceIte,
          Bool.false_eq_true, decide_false, Nat.add_one_ne_zero, counts]
        congr 1
        omega)
    fun l r ihl ihr m p fc lc j ok hm hlf ↦ by
      rw [Geb.BitTree.Elias.encode_fork, List.foldl_cons, List.foldl_append]
      change (encode r).foldl (extStep (childUpd target k edge))
        ((encode l).foldl (extStep (childUpd target k edge))
          ⟨(.tree, m + 1), p + 1,
            childUpd target k edge p ⟨true, false, none, false⟩ ⟨.body, fc, lc, j, ok⟩⟩) = _
      rw [show childUpd target k edge p ⟨true, false, none, false⟩ ⟨.body, fc, lc, j, ok⟩ =
        ⟨.body, fc + 1, lc, j, ok⟩ from rfl,
        ihl (m + 1) (p + 1) (fc + 1) lc j ok (Nat.succ_pos m) (by omega),
        if_neg (by omega)]
      have hf : finish (m + 1) = (.tree, m) := by
        rw [Geb.BitTree.Elias.Scanner.finish, if_neg (by omega), Nat.add_sub_cancel]
      rw [hf, ihr m _ _ _ j ok hm (by omega), List.length_cons, List.length_append,
        Geb.BitTree.counts_fork]
      by_cases h : lc = fc
      · rw [if_pos (by omega), if_pos h]
        congr 1
        omega
      · rw [if_neg (by omega), if_neg h]
        congr 1
        · omega
        · congr 1 <;> omega

/-- At a child's fork tags, an encoded tree is the child: the check is raised
at its label, and the child completes exactly when no fork tag preceded it,
which is when the tree is the whole child. -/
theorem foldl_child_spine : ∀ (t : Tree) (m p fc j : ℕ) (ok : Bool), 0 < m →
    (encode t).foldl (extStep (childUpd target k edge)) ⟨(.tree, m), p, ⟨.spine, fc, 0, j, ok⟩⟩ =
      ⟨finish m, p + (encode t).length,
        if fc = 0 then afterChildren k (j + 1) (ok && edge (roseAt t p).label j)
        else ⟨.body, fc + (counts t).1, (counts t).1 + 1, j, ok && edge (roseAt t p).label j⟩⟩ :=
  tree_ind (fun s m p fc j ok _ ↦ by
      rw [Geb.BitTree.Elias.encode_leaf, List.foldl_cons, List.foldl_append, roseAt_leaf]
      change (s.foldl (extStep (childUpd target k edge))
        ((encodeNat s.length).foldl (extStep (childUpd target k edge))
          ⟨(.zeros 0, m), p + 1,
            childUpd target k edge p ⟨false, true, none, false⟩ ⟨.spine, fc, 0, j, ok⟩⟩)) = _
      rw [childUpd_tag, foldl_extStep_encodeNat _ (childUpd_silent target k edge)]
      cases s with
      | nil =>
        simp only [List.length_nil, List.foldl_nil, List.length_cons, List.length_append,
          Nat.add_zero, childUpd, ↓reduceIte, decide_true, counts]
        rfl
      | cons b bs =>
        have hp' : p + 1 + (encodeNat (bs.length + 1)).length - 1 + 1 =
            p + 1 + (encodeNat (bs.length + 1)).length := by
          have := Geb.BitTree.Elias.length_encodeNat_pos (bs.length + 1)
          omega
        rw [if_neg (by simp), foldl_extStep_payload _ (childUpd_silent target k edge)
          (b :: bs) m _ _ (List.cons_ne_nil b bs)]
        simp only [List.length_cons, List.length_append, childUpd, ↓reduceIte,
          Bool.false_eq_true, decide_false, Nat.add_one_ne_zero, counts, hp']
        by_cases hfc : fc = 0
        · rw [if_pos hfc, if_pos hfc.symm]
          congr 1
          omega
        · rw [if_neg hfc, if_neg (Ne.symm hfc)]
          congr 1
          omega)
    fun l r ihl ihr m p fc j ok hm ↦ by
      rw [Geb.BitTree.Elias.encode_fork, List.foldl_cons, List.foldl_append, roseAt_fork]
      dsimp only
      change (encode r).foldl (extStep (childUpd target k edge))
        ((encode l).foldl (extStep (childUpd target k edge))
          ⟨(.tree, m + 1), p + 1,
            childUpd target k edge p ⟨true, false, none, false⟩ ⟨.spine, fc, 0, j, ok⟩⟩) = _
      rw [show childUpd target k edge p ⟨true, false, none, false⟩ ⟨.spine, fc, 0, j, ok⟩ =
        ⟨.spine, fc + 1, 0, j, ok⟩ from rfl,
        ihl (m + 1) (p + 1) (fc + 1) j ok (Nat.succ_pos m), if_neg (Nat.add_one_ne_zero fc)]
      have hf : finish (m + 1) = (.tree, m) := by
        rw [Geb.BitTree.Elias.Scanner.finish, if_neg (by omega), Nat.add_sub_cancel]
      rw [hf, foldl_child_body target k edge r m _ _ _ j _ hm (by omega), List.length_cons,
        List.length_append, Geb.BitTree.counts_fork]
      by_cases h : fc = 0
      · rw [if_pos (by omega), if_pos h]
        congr 1
        omega
      · rw [if_neg (by omega), if_neg h]
        congr 1
        · omega
        · congr 1 <;> omega

/-- The label positions of the nodes of a fork's subtrees are among those of
the fork's nodes. -/
theorem nodes_fork_pos (l r : Tree) (p q : ℕ)
    (h : ∀ n ∈ nodes (fork l r) p, n.label.pos ≠ q) :
    (∀ n ∈ nodes l (p + 1), n.label.pos ≠ q) ∧
      ∀ n ∈ nodes r (p + 1 + (encode l).length), n.label.pos ≠ q := by
  unfold nodes at h ⊢
  rw [roseAt_fork] at h
  dsimp only at h
  have hl : ∀ n ∈ (roseAt l (p + 1)).inner, n.label.pos ≠ q := fun n hn ↦
    h n (by
      rw [List.mem_append, List.mem_append, List.mem_append]
      exact Or.inl (Or.inl (Or.inl hn)))
  have hr : ∀ n ∈ (roseAt r (p + 1 + (encode l).length)).inner, n.label.pos ≠ q := fun n hn ↦
    h n (by
      rw [List.mem_append, List.mem_append, List.mem_append]
      exact Or.inl (Or.inl (Or.inr hn)))
  have hrr := h ⟨(roseAt r (p + 1 + (encode l).length)).label,
      (roseAt r (p + 1 + (encode l).length)).children⟩
    (by rw [List.mem_append, List.mem_append, List.mem_singleton]; exact Or.inl (Or.inr rfl))
  have hll := h ⟨(roseAt l (p + 1)).label,
      (roseAt l (p + 1)).children ++ [(roseAt r (p + 1 + (encode l).length)).label]⟩
    (by rw [List.mem_append, List.mem_singleton]; exact Or.inr rfl)
  constructor
  · intro n hn
    rw [List.mem_append, List.mem_singleton] at hn
    rcases hn with hn | rfl
    · exact hl n hn
    · exact hll
  · intro n hn
    rw [List.mem_append, List.mem_singleton] at hn
    rcases hn with hn | rfl
    · exact hr n hn
    · exact hrr

/-- Before the node, an encoded tree none of whose labels is at the target is
passed over. -/
theorem foldl_child_before_miss : ∀ (t : Tree) (m p : ℕ) (x : ChildReg), 0 < m →
    x.mode = .before → (∀ n ∈ nodes t p, n.label.pos ≠ target.pos) →
    (encode t).foldl (extStep (childUpd target k edge)) ⟨(.tree, m), p, x⟩ =
      ⟨finish m, p + (encode t).length, x⟩ :=
  tree_ind (fun s m p x _ hx hn ↦ by
      have hne : p + 1 + (encodeNat s.length).length ≠ target.pos :=
        hn ⟨⟨p + 1 + (encodeNat s.length).length, s.length⟩, []⟩
          (by unfold nodes; rw [roseAt_leaf]; exact List.mem_singleton.mpr rfl)
      rcases x with ⟨mode, fc, lc, j, ok⟩
      change mode = .before at hx
      subst hx
      rw [Geb.BitTree.Elias.encode_leaf, List.foldl_cons, List.foldl_append]
      change (s.foldl (extStep (childUpd target k edge))
        ((encodeNat s.length).foldl (extStep (childUpd target k edge))
          ⟨(.zeros 0, m), p + 1,
            childUpd target k edge p ⟨false, true, none, false⟩ ⟨.before, fc, lc, j, ok⟩⟩)) = _
      rw [childUpd_tag, foldl_extStep_encodeNat _ (childUpd_silent target k edge)]
      cases s with
      | nil =>
        have hp : p + 1 + (encodeNat 0).length - 1 + 1 = p + 1 + (encodeNat 0).length := by
          have := Geb.BitTree.Elias.length_encodeNat_pos 0
          omega
        rw [List.length_nil] at hne
        simp only [List.length_nil, List.foldl_nil, List.length_cons, List.length_append,
          Nat.add_zero, childUpd, hp, hne, ↓reduceIte]
        rfl
      | cons b bs =>
        have hp' : p + 1 + (encodeNat (bs.length + 1)).length - 1 + 1 =
            p + 1 + (encodeNat (bs.length + 1)).length := by
          have := Geb.BitTree.Elias.length_encodeNat_pos (bs.length + 1)
          omega
        rw [List.length_cons] at hne
        rw [if_neg (by simp), foldl_extStep_payload _ (childUpd_silent target k edge)
          (b :: bs) m _ _ (List.cons_ne_nil b bs)]
        simp only [List.length_cons, List.length_append, childUpd, hp', hne, ↓reduceIte]
        congr 1
        omega)
    fun l r ihl ihr m p x hm hx hn ↦ by
      obtain ⟨hnl, hnr⟩ := nodes_fork_pos l r p target.pos hn
      rcases x with ⟨mode, fc, lc, j, ok⟩
      change mode = .before at hx
      subst hx
      rw [Geb.BitTree.Elias.encode_fork, List.foldl_cons, List.foldl_append]
      change (encode r).foldl (extStep (childUpd target k edge))
        ((encode l).foldl (extStep (childUpd target k edge))
          ⟨(.tree, m + 1), p + 1,
            childUpd target k edge p ⟨true, false, none, false⟩ ⟨.before, fc, lc, j, ok⟩⟩) = _
      rw [show childUpd target k edge p ⟨true, false, none, false⟩ ⟨.before, fc, lc, j, ok⟩ =
        ⟨.before, fc, lc, j, ok⟩ from rfl, ihl (m + 1) (p + 1) _ (Nat.succ_pos m) rfl hnl]
      have hf : finish (m + 1) = (.tree, m) := by
        rw [Geb.BitTree.Elias.Scanner.finish, if_neg (by omega), Nat.add_sub_cancel]
      rw [hf, ihr m _ _ hm rfl hnr, List.length_cons, List.length_append]
      congr 1
      omega

/-- Before the node, the encoded tree whose open spine belongs to the node reads
the node's payload and then the children on the spine: the check is raised at
each, and the registers are those after as many children as the spine has. -/
theorem foldl_child_root : ∀ (t : Tree) (m p : ℕ) (x : ChildReg), 0 < m → x.mode = .before →
    (roseAt t p).label = target → (roseAt t p).children.length ≤ k →
    (encode t).foldl (extStep (childUpd target k edge)) ⟨(.tree, m), p, x⟩ =
      ⟨finish m, p + (encode t).length,
        afterChildren k (roseAt t p).children.length
          (x.ok && edgesAll edge (roseAt t p).children)⟩ :=
  tree_ind (fun s m p x _ hx ht _ ↦ by
      rw [roseAt_leaf] at ht ⊢
      dsimp only at ht ⊢
      have hpos : p + 1 + (encodeNat s.length).length = target.pos := by rw [← ht]
      rcases x with ⟨mode, fc, lc, j, ok⟩
      change mode = .before at hx
      subst hx
      rw [Geb.BitTree.Elias.encode_leaf, List.foldl_cons, List.foldl_append]
      change (s.foldl (extStep (childUpd target k edge))
        ((encodeNat s.length).foldl (extStep (childUpd target k edge))
          ⟨(.zeros 0, m), p + 1,
            childUpd target k edge p ⟨false, true, none, false⟩ ⟨.before, fc, lc, j, ok⟩⟩)) = _
      rw [childUpd_tag, foldl_extStep_encodeNat _ (childUpd_silent target k edge)]
      cases s with
      | nil =>
        rw [List.length_nil] at hpos
        have hc : p + 1 + (encodeNat 0).length - 1 + 1 = target.pos := by
          have := Geb.BitTree.Elias.length_encodeNat_pos 0
          omega
        simp only [List.length_nil, List.foldl_nil, List.length_cons, List.length_append,
          Nat.add_zero, childUpd, hc, ↓reduceIte, decide_true, edgesAll, Bool.and_true]
        rw [show p + 1 + (encodeNat 0).length = p + ((encodeNat 0).length + 1) by omega]
      | cons b bs =>
        rw [List.length_cons] at hpos
        have hc : p + 1 + (encodeNat (bs.length + 1)).length - 1 + 1 = target.pos := by
          have := Geb.BitTree.Elias.length_encodeNat_pos (bs.length + 1)
          omega
        rw [if_neg (by simp), foldl_extStep_payload _ (childUpd_silent target k edge)
          (b :: bs) m _ _ (List.cons_ne_nil b bs)]
        simp only [List.length_cons, List.length_append, childUpd, hc, ↓reduceIte,
          Bool.false_eq_true, decide_false, edgesAll, List.foldl_nil, Bool.and_true,
          Nat.add_one_ne_zero]
        congr 1
        omega)
    fun l r ihl ihr m p x hm hx ht hk ↦ by
      rw [roseAt_fork] at ht hk ⊢
      dsimp only at ht hk ⊢
      rw [List.length_append, List.length_singleton] at hk ⊢
      rcases x with ⟨mode, fc, lc, j, ok⟩
      change mode = .before at hx
      subst hx
      rw [Geb.BitTree.Elias.encode_fork, List.foldl_cons, List.foldl_append]
      change (encode r).foldl (extStep (childUpd target k edge))
        ((encode l).foldl (extStep (childUpd target k edge))
          ⟨(.tree, m + 1), p + 1,
            childUpd target k edge p ⟨true, false, none, false⟩ ⟨.before, fc, lc, j, ok⟩⟩) = _
      rw [show childUpd target k edge p ⟨true, false, none, false⟩ ⟨.before, fc, lc, j, ok⟩ =
        ⟨.before, fc, lc, j, ok⟩ from rfl,
        ihl (m + 1) (p + 1) _ (Nat.succ_pos m) rfl ht (by omega)]
      have hf : finish (m + 1) = (.tree, m) := by
        rw [Geb.BitTree.Elias.Scanner.finish, if_neg (by omega), Nat.add_sub_cancel]
      rw [hf, afterChildren_of_ne k (roseAt l (p + 1)).children.length _ (by omega),
        foldl_child_spine target k edge r m _ 0 _ _ hm, if_pos rfl, List.length_cons,
        List.length_append, edgesAll_concat, ← Bool.and_assoc]
      congr 1
      omega

/-- Before the node, an encoded tree with the node completed inside reads all
its children: the scan ends done with the check raised at each. -/
theorem foldl_child_inner : ∀ (t : Tree) (m p : ℕ) (x : ChildReg) (n : Node), 0 < m →
    x.mode = .before → n ∈ (roseAt t p).inner → n.label = target → n.k = k →
    (encode t).foldl (extStep (childUpd target k edge)) ⟨(.tree, m), p, x⟩ =
      ⟨finish m, p + (encode t).length, ⟨.done, 0, 0, k, x.ok && edgesAll edge n.children⟩⟩ :=
  tree_ind (fun s m p x n _ _ hn ↦ by
      rw [roseAt_leaf] at hn
      exact absurd hn List.not_mem_nil)
    fun l r ihl ihr m p x n hm hx hn ht hk ↦ by
      rcases x with ⟨mode, fc, lc, j, ok⟩
      change mode = .before at hx
      subst hx
      have hf : finish (m + 1) = (.tree, m) := by
        rw [Geb.BitTree.Elias.Scanner.finish, if_neg (by omega), Nat.add_sub_cancel]
      rw [roseAt_fork] at hn
      dsimp only at hn
      rw [Geb.BitTree.Elias.encode_fork, List.foldl_cons, List.foldl_append]
      change (encode r).foldl (extStep (childUpd target k edge))
        ((encode l).foldl (extStep (childUpd target k edge))
          ⟨(.tree, m + 1), p + 1,
            childUpd target k edge p ⟨true, false, none, false⟩ ⟨.before, fc, lc, j, ok⟩⟩) = _
      rw [show childUpd target k edge p ⟨true, false, none, false⟩ ⟨.before, fc, lc, j, ok⟩ =
        ⟨.before, fc, lc, j, ok⟩ from rfl]
      -- the labels of the left subtree lie before the right subtree's first bit
      have hleft : ∀ q, p + 1 + (encode l).length < q →
          ∀ n' ∈ nodes l (p + 1), n'.label.pos ≠ q := fun q hq n' hn' ↦ by
          have := nodes_pos_bounds l (p + 1) n' hn'
          omega
      rw [List.mem_append, List.mem_append, List.mem_singleton] at hn
      rcases hn with (hn | hn) | rfl
      · rw [ihl (m + 1) (p + 1) _ n (Nat.succ_pos m) rfl hn ht hk, hf, foldl_child_done,
          Geb.BitTree.Elias.Scanner.foldl_encode r m hm, List.length_cons, List.length_append]
        congr 1
        omega
      · have hpos := ((pos_roseAt_lt r (p + 1 + (encode l).length)).2.2 n hn).1.1
        rw [foldl_child_before_miss target k edge l (m + 1) (p + 1) _ (Nat.succ_pos m) rfl
          (hleft target.pos (ht ▸ hpos)), hf,
          ihr m _ _ n hm rfl hn ht hk, List.length_cons, List.length_append]
        congr 1
        omega
      · have hpos := (pos_roseAt_lt r (p + 1 + (encode l).length)).1.1
        rw [foldl_child_before_miss target k edge l (m + 1) (p + 1) _ (Nat.succ_pos m) rfl
          (hleft target.pos (ht ▸ hpos)), hf,
          foldl_child_root target k edge r m _ _ hm rfl ht hk.le, List.length_cons,
          List.length_append,
          show (roseAt r (p + 1 + (encode l).length)).children.length = k from hk,
          afterChildren_self]
        congr 1
        omega

/-- The scan of an encoded tree for one of its nodes accepts exactly when the
check holds at each of the node's children. -/
theorem childScan_ok_iff (t : Tree) (n : Node) (hn : n ∈ nodes t 0) :
    (childScan n.label n.k edge (encode t)).extra.ok = true ↔
      ∀ (i : ℕ) (h : i < n.k), edge n.children[i] i = true := by
  unfold childScan
  refine Iff.trans ?_ (edgesAll_iff edge n.children)
  unfold nodes at hn
  rw [List.mem_append, List.mem_singleton] at hn
  rcases hn with hn | rfl
  · rw [foldl_child_inner n.label n.k edge t 1 0 ⟨.before, 0, 0, 0, true⟩ n Nat.one_pos rfl hn rfl
      rfl]
    exact Bool.true_and _ ▸ Iff.rfl
  · dsimp only [Node.k]
    rw [foldl_child_root _ _ edge t 1 0 ⟨.before, 0, 0, 0, true⟩ Nat.one_pos rfl rfl
      (Nat.le_refl _), afterChildren_self]
    exact Bool.true_and _ ▸ Iff.rfl

end

end Geb.SizeBounded.Logspace.WTree
