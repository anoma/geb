/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
-- Modified from geb-mathlib by scripts/geb-mathlib-backport.patch.
module

public import Geb.Mathlib.Data.PFunctor.Slice.W
public import Geb.Mathlib.Data.PFunctor.Univariate.Finitary
public import Geb.Prototypes.Computability.BitTree.Elias.Tree

set_option doc.verso true in
/-!
# W-trees of a coded signature as binary trees of labels

A finitary slice polynomial endofunctor whose shapes are coded by bitstrings
spells each of its W-trees as a binary tree with a bitstring at each leaf,
{name}`Geb.BitTree.Tree`: a node with shape {lit}`a` and children
{lit}`c₀, …, cₖ₋₁`, in the enumeration order of its directions, is the left
spine of {lit}`k` forks whose leftmost leaf carries the code of {lit}`a` and
whose right children are the spellings of the children. Under the Elias-length
encoding {name}`Geb.BitTree.Elias.encode` the node reads {lit}`1ᵏ 0`, the
delta-coded length of the label, the label, and the children in order: the
arity in unary before the label. A binary tree of labels is read back as a
W-tree when every leftmost leaf of a spine decodes to a shape with as many
directions as the spine has forks, and the W-tree is admissible when moreover
each child's root shape lies over the input index its direction prescribes.
Both conditions are computed by one fold over the binary tree, which is what
a recognizer of the encodings checks label by label and edge by edge.

# Main definitions

* {lit}`CodedSig` — a finitary slice polynomial endofunctor with a code and
  a decoder for its shapes.
* {lit}`CodedSig.card`, {lit}`CodedSig.dir`, {lit}`CodedSig.idx` — the
  number of directions of a shape and the enumeration of its directions.
* {lit}`spine`, {lit}`CodedSig.toTree`, {lit}`CodedSig.spell` — the left
  spine of a leaf over a list of children, the binary tree spelling a raw
  W-tree, and its Elias-length encoding.
* {lit}`CodedSig.labelSpec`, {lit}`CodedSig.edgeSpec` — a label decodes to a
  shape of a given arity; a child's label lies over the index a parent's
  direction prescribes.
* {lit}`Info`, {lit}`CodedSig.info` — the leftmost label, the spine length
  and the two conditions, folded over a binary tree.
* {lit}`CodedSig.labelsOk`, {lit}`CodedSig.edgesOk` — the two conditions
  on a whole binary tree.
* {lit}`CodedSig.close`, {lit}`CodedSig.open`, {lit}`CodedSig.readW` — a
  node from a label and its children, the open node a binary tree folds to,
  and the raw W-tree a binary tree reads as.

# Main statements

* {lit}`CodedSig.readW_toTree`, {lit}`CodedSig.toTree_of_readW` — reading
  inverts spelling.
* {lit}`CodedSig.readW_isSome_iff` — a binary tree reads as a W-tree exactly
  when its labels are in order.
* {lit}`CodedSig.wValid_iff_edgesOk` — a W-tree read from a binary tree is
  admissible exactly when the tree's edges are in order.
* {lit}`CodedSig.isW_iff` — a word is the spelling of an admissible W-tree
  exactly when it is the encoding of a binary tree whose labels and edges are
  in order.

# Tags

W-type, slice polynomial functor, binary tree, bitstring, encoding
-/

set_option doc.verso true

namespace Geb.SizeBounded.Logspace.WTree

open Geb.BitTree (Tree leaf fork tree_ind)
open scoped FinEnum

public section

/-- A finitary slice polynomial endofunctor over {lit}`I` whose shapes are coded
by bitstrings: an injective code with a decoder that inverts it. -/
structure CodedSig (I : Type) where
  /-- The functor. -/
  P : SlicePFunctor I I
  /-- Every shape has finitely many directions. -/
  finitary : P.toPFunctor.Finitary
  /-- The code of a shape. -/
  code : P.A → List Bool
  /-- The decoder. -/
  decode : List Bool → Option P.A
  /-- The decoder inverts the code. -/
  decode_code : ∀ a, decode (code a) = some a
  /-- A word that decodes is the code of what it decodes to. -/
  code_of_decode : ∀ {w a}, decode w = some a → code a = w

/-- The left spine of forks over a leaf, one fork per child, the children as
the right subtrees from the bottom up. -/
@[expose] def spine : Tree → List Tree → Tree := List.foldl fork

/-- The spine over one more child. -/
theorem spine_concat (t : Tree) (ts : List Tree) (c : Tree) :
    spine t (ts ++ [c]) = fork (spine t ts) c :=
  List.foldl_concat fork t c ts

namespace CodedSig

variable {I : Type} (C : CodedSig I)

/-- The functor's finitarity, as an instance. -/
instance instFinitary : C.P.toPFunctor.Finitary := C.finitary

/-- The number of directions of a shape. -/
@[expose] def card (a : C.P.A) : ℕ := FinEnum.card (C.P.B a)

/-- The directions of a shape in enumeration order. -/
@[expose] def dir (a : C.P.A) : Fin (C.card a) → C.P.B a := FinEnum.equiv.symm

/-- The position of a direction in the enumeration. -/
@[expose] def idx (a : C.P.A) : C.P.B a → Fin (C.card a) := FinEnum.equiv

/-- The enumeration at a direction's position is the direction. -/
theorem dir_idx (a : C.P.A) (b : C.P.B a) : C.dir a (C.idx a b) = b :=
  Equiv.symm_apply_apply _ b

/-- The position of the direction at a position is the position. -/
theorem idx_dir (a : C.P.A) (i : Fin (C.card a)) : C.idx a (C.dir a i) = i :=
  Equiv.apply_symm_apply _ i

/-- The binary tree spelling a raw W-tree: at a node, the spine of its shape's
code over its children's spellings in enumeration order. -/
@[expose] def toTree : C.P.toPFunctor.W → Tree :=
  WType.elim Tree fun x ↦ spine (leaf (C.code x.1)) (List.ofFn fun i ↦ x.2 (C.dir x.1 i))

/-- The spelling of a node. -/
theorem toTree_mk (a : C.P.A) (f : C.P.B a → C.P.toPFunctor.W) :
    C.toTree (WType.mk a f) =
      spine (leaf (C.code a)) (List.ofFn fun i ↦ C.toTree (f (C.dir a i))) := rfl

/-- The word spelling a raw W-tree: the Elias-length encoding of its binary
tree. -/
@[expose] def spell (t : C.P.toPFunctor.W) : List Bool := Geb.BitTree.Elias.encode (C.toTree t)

/-- A label decodes to a shape with the given number of directions. -/
@[expose] def labelSpec (s : List Bool) (k : ℕ) : Bool :=
  match C.decode s with
  | some a => decide (C.card a = k)
  | none => false

/-- A child's label decodes to a shape lying over the input index the parent's
label prescribes at the child's position. -/
@[expose] def edgeSpec [DecidableEq I] (s : List Bool) (j : ℕ) (s' : List Bool) : Bool :=
  match C.decode s, C.decode s' with
  | some a, some c =>
    if h : j < C.card a then decide (C.P.q c = C.P.rCurried a (C.dir a ⟨j, h⟩)) else false
  | _, _ => false

/-- The node with a label's shape over the children, when the label decodes
and the children are as many as the shape's directions. -/
@[expose] def close (s : List Bool) (cs : List C.P.toPFunctor.W) : Option C.P.toPFunctor.W :=
  match C.decode s with
  | some a =>
    if h : cs.length = C.card a then
      some (WType.mk a fun b ↦ cs[(C.idx a b).1]'(Nat.lt_of_lt_of_eq (C.idx a b).2 h.symm))
    else none
  | none => none

/-- The open node a binary tree folds to: its leftmost label with the W-trees
its spine's right subtrees read as, when each reads. -/
@[expose] def «open» : Tree → Option (List Bool × List C.P.toPFunctor.W) :=
  WType.elim (Option (List Bool × List C.P.toPFunctor.W)) fun x ↦
    match x with
    | ⟨some s, _⟩ => some (s, [])
    | ⟨none, f⟩ =>
      match f false, f true with
      | some (s, cs), some (s', cs') =>
        match C.close s' cs' with
        | some c => some (s, cs ++ [c])
        | none => none
      | _, _ => none

/-- The open node at a leaf. -/
theorem open_leaf (s : List Bool) : C.open (leaf s) = some (s, []) := rfl

/-- The open node at a fork. -/
theorem open_fork (l r : Tree) :
    C.open (fork l r) =
      match C.open l, C.open r with
      | some (s, cs), some (s', cs') =>
        match C.close s' cs' with
        | some c => some (s, cs ++ [c])
        | none => none
      | _, _ => none := rfl

/-- The raw W-tree a binary tree reads as: its open node closed. -/
@[expose] def readW (t : Tree) : Option C.P.toPFunctor.W :=
  match C.open t with
  | some (s, cs) => C.close s cs
  | none => none

end CodedSig

/-- What a fold over a binary tree carries: its leftmost label, the length of
its left spine, whether every label below the spine is in order, and whether
every edge is. -/
structure Info where
  /-- The leftmost label. -/
  label : List Bool
  /-- The number of forks on the left spine. -/
  spine : ℕ
  /-- Every label of a completed spine is in order. -/
  labels : Bool
  /-- Every edge is in order. -/
  edges : Bool

namespace CodedSig

variable {I : Type} [DecidableEq I] (C : CodedSig I)

/-- The fold: a leaf is its own label with no forks; a fork extends the left
subtree's spine by one, the right subtree completing a spine whose label is
checked at the spine's length, and adds the edge from the left subtree's label
to the right subtree's at the position the spine had. -/
@[expose] def info : Tree → Info :=
  WType.elim Info fun x ↦
    match x with
    | ⟨some s, _⟩ => ⟨s, 0, true, true⟩
    | ⟨none, f⟩ =>
      ⟨(f false).label, (f false).spine + 1,
        (f false).labels && (f true).labels && C.labelSpec (f true).label (f true).spine,
        (f false).edges && (f true).edges &&
          C.edgeSpec (f false).label (f false).spine (f true).label⟩

/-- The fold at a leaf. -/
theorem info_leaf (s : List Bool) : C.info (leaf s) = ⟨s, 0, true, true⟩ := rfl

/-- The fold at a fork. -/
theorem info_fork (l r : Tree) :
    C.info (fork l r) =
      ⟨(C.info l).label, (C.info l).spine + 1,
        (C.info l).labels && (C.info r).labels && C.labelSpec (C.info r).label (C.info r).spine,
        (C.info l).edges && (C.info r).edges &&
          C.edgeSpec (C.info l).label (C.info l).spine (C.info r).label⟩ := rfl

/-- Every label is in order: those below the spines, and the root's at the
root spine's length. -/
@[expose] def labelsOk (t : Tree) : Bool :=
  (C.info t).labels && C.labelSpec (C.info t).label (C.info t).spine

/-- Every edge is in order. -/
@[expose] def edgesOk (t : Tree) : Bool := (C.info t).edges

end CodedSig

namespace CodedSig

variable {I : Type} (C : CodedSig I)

/-- Closing the code of a shape over its children in enumeration order gives
the node. -/
theorem close_code (a : C.P.A) (f : C.P.B a → C.P.toPFunctor.W) :
    C.close (C.code a) (List.ofFn fun i ↦ f (C.dir a i)) = some (WType.mk a f) := by
  unfold close
  rw [C.decode_code]
  dsimp only
  rw [dif_pos List.length_ofFn]
  congr 2
  funext b
  rw [List.getElem_ofFn, Fin.eta, C.dir_idx]

/-- What a closed node is: the label decodes to its shape, the children are as
many as the shape's directions, and the node is the shape over them. -/
theorem close_eq_some (s : List Bool) (cs : List C.P.toPFunctor.W) (c : C.P.toPFunctor.W)
    (hc : C.close s cs = some c) :
    ∃ (a : C.P.A) (h : cs.length = C.card a), C.decode s = some a ∧
      c = WType.mk a fun b ↦ cs[(C.idx a b).1]'(Nat.lt_of_lt_of_eq (C.idx a b).2 h.symm) := by
  unfold close at hc
  cases hd : C.decode s with
  | none => rw [hd] at hc; cases hc
  | some a =>
    rw [hd] at hc
    dsimp only at hc
    by_cases h : cs.length = C.card a
    · rw [dif_pos h] at hc
      exact ⟨a, h, rfl, (Option.some.inj hc).symm⟩
    · rw [dif_neg h] at hc
      cases hc

/-- A label closes over children exactly when it is in order at their number. -/
theorem close_isSome_iff (s : List Bool) (cs : List C.P.toPFunctor.W) :
    (C.close s cs).isSome = true ↔ C.labelSpec s cs.length = true := by
  unfold close labelSpec
  cases C.decode s with
  | none => simp
  | some a =>
    dsimp only
    by_cases h : cs.length = C.card a
    · rw [dif_pos h]
      simp only [decide_eq_true_iff]
      exact ⟨fun _ ↦ h.symm, fun _ ↦ rfl⟩
    · rw [dif_neg h]
      simp only [decide_eq_true_iff]
      exact ⟨fun h' ↦ absurd h' Bool.false_ne_true, fun h' ↦ absurd h'.symm h⟩

/-- Reading is the open node closed. -/
theorem readW_eq_some_iff (t : Tree) (c : C.P.toPFunctor.W) :
    C.readW t = some c ↔ ∃ s cs, C.open t = some (s, cs) ∧ C.close s cs = some c := by
  unfold readW
  cases C.open t with
  | none => simp
  | some p =>
    rcases p with ⟨s, cs⟩
    simp

/-- The open node of a fork: the left subtree's, extended by the right subtree
closed. -/
theorem open_fork_eq_some_iff (l r : Tree) (s : List Bool) (cs : List C.P.toPFunctor.W) :
    C.open (fork l r) = some (s, cs) ↔
      ∃ cs₀ s' cs' c, C.open l = some (s, cs₀) ∧ C.open r = some (s', cs') ∧
        C.close s' cs' = some c ∧ cs = cs₀ ++ [c] := by
  rw [open_fork]
  cases C.open l with
  | none => simp
  | some p =>
    rcases p with ⟨s₀, cs₀⟩
    cases C.open r with
    | none => simp
    | some p' =>
      rcases p' with ⟨s', cs'⟩
      dsimp only
      cases hc : C.close s' cs' with
      | none => simp [hc]
      | some c =>
        constructor
        · intro h
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
          exact ⟨cs₀, s', cs', c, rfl, rfl, hc, rfl⟩
        · rintro ⟨cs₁, s₁, cs₂, c₁, h₁, h₂, h₃, rfl⟩
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h₁)
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h₂)
          rw [Option.some.inj (h₃.symm.trans hc)]

/-- The open node of a spine over the spellings of a family of W-trees: the
label over the family. -/
theorem open_spine_ofFn (s : List Bool) :
    ∀ (n : ℕ) (ts : Fin n → Tree) (cs : Fin n → C.P.toPFunctor.W),
      (∀ i, C.readW (ts i) = some (cs i)) →
        C.open (spine (leaf s) (List.ofFn ts)) = some (s, List.ofFn cs) :=
  Nat.rec (fun _ _ _ ↦ by rw [List.ofFn_zero, List.ofFn_zero]; rfl) fun n ih ts cs h ↦ by
    rw [List.ofFn_succ' ts, List.concat_eq_append, spine_concat, open_fork,
      ih (fun i ↦ ts i.castSucc) (fun i ↦ cs i.castSucc) (fun i ↦ h _)]
    obtain ⟨s', cs', ho, hc⟩ := (C.readW_eq_some_iff _ _).mp (h (Fin.last n))
    rw [ho, List.ofFn_succ' cs, List.concat_eq_append]
    dsimp only
    rw [hc]

/-- Reading inverts spelling. -/
theorem readW_toTree : ∀ t : C.P.toPFunctor.W, C.readW (C.toTree t) = some t :=
  WType.rec fun a f ih ↦ (C.readW_eq_some_iff _ _).mpr
    ⟨C.code a, List.ofFn fun i ↦ f (C.dir a i),
      C.open_spine_ofFn (C.code a) (C.card a) _ _ (fun i ↦ ih (C.dir a i)), C.close_code a f⟩

/-- The spelling of a closed node is the spine of its label over the spellings
of its children. -/
theorem toTree_close (s : List Bool) (cs : List C.P.toPFunctor.W) (ts : List Tree)
    (c : C.P.toPFunctor.W) (hc : C.close s cs = some c) (hl : ts.length = cs.length)
    (ht : ∀ (i : ℕ) (h : i < cs.length), C.toTree cs[i] = ts[i]'(hl ▸ h)) :
    C.toTree c = spine (leaf s) ts := by
  obtain ⟨a, h, hd, rfl⟩ := C.close_eq_some s cs c hc
  rw [C.toTree_mk, C.code_of_decode hd]
  congr 1
  refine List.ext_getElem (by rw [List.length_ofFn, hl, h]) fun i hi hi' ↦ ?_
  rw [List.getElem_ofFn, C.idx_dir]
  exact ht i (hl ▸ hi')

/-- What a binary tree with an open node is: the spine of the label over
subtrees spelling the node's children. -/
theorem eq_spine_of_open : ∀ (t : Tree) (s : List Bool) (cs : List C.P.toPFunctor.W),
    C.open t = some (s, cs) → ∃ ts : List Tree, t = spine (leaf s) ts ∧
      ∃ hl : ts.length = cs.length,
        ∀ (i : ℕ) (h : i < cs.length), C.toTree cs[i] = ts[i]'(hl ▸ h) :=
  tree_ind
    (fun s₀ s cs h ↦ by
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      exact ⟨[], rfl, rfl, fun i h ↦ absurd h (Nat.not_lt_zero i)⟩)
    fun l r ihl ihr s cs h ↦ by
      obtain ⟨cs₀, s', cs', c, hl, hr, hc, rfl⟩ := (C.open_fork_eq_some_iff l r s cs).mp h
      obtain ⟨ts₀, rfl, hl₀, ht₀⟩ := ihl s cs₀ hl
      obtain ⟨ts', rfl, hl', ht'⟩ := ihr s' cs' hr
      refine ⟨ts₀ ++ [spine (leaf s') ts'], (spine_concat _ _ _).symm,
        by simp only [List.length_append, List.length_singleton, hl₀], fun i hi ↦ ?_⟩
      rw [List.length_append, List.length_singleton] at hi
      by_cases hi₀ : i < cs₀.length
      · rw [List.getElem_append_left hi₀, List.getElem_append_left (hl₀ ▸ hi₀)]
        exact ht₀ i hi₀
      · have hi₁ : i = cs₀.length := by omega
        subst hi₁
        rw [List.getElem_concat_length rfl, List.getElem_concat_length hl₀.symm]
        exact C.toTree_close s' cs' ts' c hc hl' ht'

/-- Spelling inverts reading. -/
theorem toTree_of_readW (t : Tree) (c : C.P.toPFunctor.W) (h : C.readW t = some c) :
    C.toTree c = t := by
  obtain ⟨s, cs, ho, hc⟩ := (C.readW_eq_some_iff t c).mp h
  obtain ⟨ts, rfl, hl, ht⟩ := C.eq_spine_of_open t s cs ho
  exact C.toTree_close s cs ts c hc hl ht

end CodedSig

namespace CodedSig

variable {I : Type} [DecidableEq I] (C : CodedSig I)

/-- A binary tree has an open node exactly when the labels below its spine are
in order, and then the node's label and children count are the fold's. -/
theorem open_info : ∀ t : Tree,
    ((C.open t).isSome = true ↔ (C.info t).labels = true) ∧
      ∀ s cs, C.open t = some (s, cs) → s = (C.info t).label ∧ cs.length = (C.info t).spine :=
  tree_ind
    (fun s₀ ↦ ⟨by rw [open_leaf, info_leaf]; exact ⟨fun _ ↦ rfl, fun _ ↦ rfl⟩, fun s cs h ↦ by
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      exact ⟨rfl, rfl⟩⟩)
    fun l r ⟨ihl, ihl'⟩ ⟨ihr, ihr'⟩ ↦ by
      refine ⟨?_, fun s cs h ↦ ?_⟩
      · rw [info_fork, open_fork]
        simp only [Bool.and_eq_true]
        cases hl : C.open l with
        | none =>
          rw [hl] at ihl
          simp only [Option.isSome_none, Bool.false_eq_true, false_iff] at ihl
          simp [ihl]
        | some p =>
          rcases p with ⟨s₀, cs₀⟩
          rw [hl] at ihl
          simp only [Option.isSome_some, true_iff] at ihl
          cases hr : C.open r with
          | none =>
            rw [hr] at ihr
            simp only [Option.isSome_none, Bool.false_eq_true, false_iff] at ihr
            simp [ihr]
          | some p' =>
            rcases p' with ⟨s', cs'⟩
            rw [hr] at ihr
            simp only [Option.isSome_some, true_iff] at ihr
            obtain ⟨hs', hlen⟩ := ihr' s' cs' hr
            rw [← hs', ← hlen, ← C.close_isSome_iff, ihl, ihr]
            dsimp only
            cases C.close s' cs' <;> simp
      · obtain ⟨cs₀, s', cs', c, hl, hr, _, rfl⟩ := (C.open_fork_eq_some_iff l r s cs).mp h
        obtain ⟨hs, hlen⟩ := ihl' s cs₀ hl
        rw [info_fork, List.length_append, List.length_singleton, hlen]
        exact ⟨hs, rfl⟩

/-- A binary tree reads as a W-tree exactly when its labels are in order. -/
theorem readW_isSome_iff (t : Tree) : (C.readW t).isSome = true ↔ C.labelsOk t = true := by
  obtain ⟨h₁, h₂⟩ := C.open_info t
  unfold readW labelsOk
  cases ho : C.open t with
  | none =>
    rw [ho] at h₁
    simp only [Option.isSome_none, Bool.false_eq_true, false_iff] at h₁
    simp [h₁]
  | some p =>
    rcases p with ⟨s, cs⟩
    rw [ho] at h₁
    simp only [Option.isSome_some, true_iff] at h₁
    obtain ⟨rfl, hlen⟩ := h₂ s cs ho
    rw [C.close_isSome_iff, ← hlen, h₁, Bool.true_and]

/-- The fold over a spine: the label, the number of children, and the edges,
which are those inside the children and those from the label to each child's
label at its position. -/
theorem info_spine_ofFn (s : List Bool) : ∀ (n : ℕ) (ts : Fin n → Tree),
    (C.info (spine (leaf s) (List.ofFn ts))).label = s ∧
      (C.info (spine (leaf s) (List.ofFn ts))).spine = n ∧
        ((C.info (spine (leaf s) (List.ofFn ts))).edges = true ↔
          (∀ i, (C.info (ts i)).edges = true) ∧
            ∀ i : Fin n, C.edgeSpec s i.1 (C.info (ts i)).label = true) :=
  Nat.rec (fun ts ↦ ⟨by rw [List.ofFn_zero]; rfl, by rw [List.ofFn_zero]; rfl, by
      rw [List.ofFn_zero]
      exact ⟨fun _ ↦ ⟨fun i ↦ i.elim0, fun i ↦ i.elim0⟩, fun _ ↦ rfl⟩⟩)
    fun n ih ts ↦ by
      obtain ⟨hl, hs, he⟩ := ih fun i ↦ ts i.castSucc
      rw [List.ofFn_succ' ts, List.concat_eq_append, spine_concat, info_fork, hl, hs]
      refine ⟨rfl, rfl, ?_⟩
      rw [Bool.and_eq_true, Bool.and_eq_true, he, Fin.forall_fin_succ', Fin.forall_fin_succ']
      constructor
      · rintro ⟨⟨⟨h₁, h₂⟩, h₃⟩, h₄⟩
        exact ⟨⟨h₁, h₃⟩, h₂, h₄⟩
      · rintro ⟨⟨h₁, h₃⟩, h₂, h₄⟩
        exact ⟨⟨⟨h₁, h₂⟩, h₃⟩, h₄⟩

/-- The leftmost label of a spelling is the code of the root shape. -/
theorem info_toTree_label (t : C.P.toPFunctor.W) :
    (C.info (C.toTree t)).label = C.code (PFunctor.W.head t) := by
  cases t with
  | mk a f => exact (C.info_spine_ofFn (C.code a) (C.card a) _).1

/-- A node is admissible exactly when the edges of its spelling are in order,
given that its children are. -/
theorem wValid_mk_iff (a : C.P.A) (f : C.P.B a → C.P.toPFunctor.W)
    (ih : ∀ b, C.P.WValid (f b) ↔ C.edgesOk (C.toTree (f b)) = true) :
    C.P.WValid (WType.mk a f) ↔ C.edgesOk (C.toTree (WType.mk a f)) = true := by
  rw [C.P.wValid_mk a f, C.toTree_mk a f]
  unfold edgesOk
  rw [(C.info_spine_ofFn (C.code a) (C.card a) _).2.2]
  unfold SlicePFunctor.ForAll SlicePFunctor.OverInput
  refine and_congr ?_ ?_
  · rw [Equiv.forall_congr_left (FinEnum.equiv (α := C.P.B a))]
    exact forall_congr' fun i ↦ ih (C.dir a i)
  · rw [funext_iff, Equiv.forall_congr_left (FinEnum.equiv (α := C.P.B a))]
    refine forall_congr' fun i ↦ ?_
    rw [C.info_toTree_label, Function.comp_apply]
    unfold edgeSpec
    rw [C.decode_code, C.decode_code]
    dsimp only
    rw [dif_pos (show i.1 < C.card a from i.2), decide_eq_true_iff]
    rfl

/-- A W-tree is admissible exactly when the edges of its spelling are in
order. -/
theorem wValid_iff_edgesOk_toTree : ∀ t : C.P.toPFunctor.W,
    C.P.WValid t ↔ C.edgesOk (C.toTree t) = true :=
  WType.rec fun a f ih ↦ C.wValid_mk_iff a f ih

/-- A W-tree read from a binary tree is admissible exactly when the tree's
edges are in order. -/
theorem wValid_iff_edgesOk (t : Tree) (c : C.P.toPFunctor.W) (h : C.readW t = some c) :
    C.P.WValid c ↔ C.edgesOk t = true := by
  rw [C.wValid_iff_edgesOk_toTree, C.toTree_of_readW t c h]

/-- A word spells an admissible W-tree exactly when it encodes a binary tree
whose labels and edges are in order. -/
theorem isW_iff (w : List Bool) :
    (∃ t, C.P.WValid t ∧ C.spell t = w) ↔
      ∃ t : Tree, Geb.BitTree.Elias.encode t = w ∧ C.labelsOk t = true ∧ C.edgesOk t = true := by
  constructor
  · rintro ⟨t, hv, rfl⟩
    refine ⟨C.toTree t, rfl, ?_, (C.wValid_iff_edgesOk_toTree t).mp hv⟩
    rw [← C.readW_isSome_iff, C.readW_toTree]
    rfl
  · rintro ⟨t, rfl, hl, he⟩
    obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp ((C.readW_isSome_iff t).mpr hl)
    refine ⟨c, (C.wValid_iff_edgesOk t c hc).mpr he, ?_⟩
    unfold spell
    rw [C.toTree_of_readW t c hc]

end CodedSig

end

end Geb.SizeBounded.Logspace.WTree
