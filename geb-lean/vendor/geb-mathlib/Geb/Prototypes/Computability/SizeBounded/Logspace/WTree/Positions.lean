/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
-- Modified from geb-mathlib by scripts/geb-mathlib-backport.patch.
module

public import Geb.Prototypes.Computability.SizeBounded.Logspace.WTree.Spell

set_option doc.verso true in
/-!
# The positions of labels in an encoded tree

A recognizer that reads an encoded tree bit by bit meets each label at a
position of the word. The nodes of a binary tree of labels, read as a rose
tree, are located here by a fold over the tree with the position of its first
bit: each node's label by the position and length of its payload, and each
node's children by their labels' locations, in order. The locations are those
the streaming scanner reaches, and the labels at them are the labels the fold
{name}`Geb.SizeBounded.Logspace.WTree.CodedSig.info` reads, so that the
conditions on labels and edges the fold states are conditions on the words at
the locations.

# Main definitions

* {lit}`Loc`, {lit}`Node`, {lit}`Rose` — a label's location; a node, its label
  and its children's locations; and an open node, with the nodes completed
  below it.
* {lit}`labelAt` — the word at a location.
* {lit}`roseAtAux`, {lit}`roseAt`, {lit}`nodes` — the fold, the open node of
  a tree at a position, and the nodes of the tree, the open node closed last.

# Main statements

* {lit}`roseAtAux_snd`, {lit}`roseAt_leaf`, {lit}`roseAt_fork` — the fold's
  length component is the encoding's length, and the fold at the two
  constructors.
* {lit}`labelAt_append` — the word at a location inside a segment.
* {lit}`roseAt_info` — the open node's label is the fold's leftmost label, its
  children as many as the spine, and the labels and edges below it are in
  order exactly when the fold says so.
* {lit}`labelsOk_iff_nodes`, {lit}`edgesOk_iff_nodes` — the two conditions
  as conditions on the nodes' locations.
* {lit}`pos_roseAt_lt`, {lit}`nodes_pos_bounds` — every label lies within the
  tree's encoding.

# Tags

W-type, binary tree, bitstring, encoding, position
-/

set_option doc.verso true

namespace Geb.SizeBounded.Logspace.WTree

open Geb.BitTree (Tree leaf fork tree_ind)
open Geb.BitTree.Elias (encode encodeNat)

public section

/-- The location of a label: the position and length of its payload. -/
structure Loc where
  /-- The position of the first payload bit. -/
  pos : ℕ
  /-- The length of the payload. -/
  len : ℕ
  deriving DecidableEq, Repr

attribute [nolint unusedArguments] instReprLoc.repr

/-- A node: its label's location and its children's, in order. -/
structure Node where
  /-- The label. -/
  label : Loc
  /-- The children's labels. -/
  children : List Loc
  deriving DecidableEq, Repr

attribute [nolint unusedArguments] instReprNode.repr

/-- The number of children. -/
@[expose] def Node.k (n : Node) : ℕ := n.children.length

/-- An open node: its label, its children so far, and the nodes completed
below it. -/
structure Rose where
  /-- The label. -/
  label : Loc
  /-- The children so far. -/
  children : List Loc
  /-- The completed nodes below. -/
  inner : List Node

/-- The word at a location. -/
@[expose] def labelAt (w : List Bool) (l : Loc) : List Bool := (w.drop l.pos).take l.len

/-- The fold: the open node of a tree as a function of the position of its first
bit, with the length of its encoding. A leaf's label follows its tag and header;
a fork extends the left subtree's spine by the right subtree's root, which it
completes. -/
@[expose] def roseAtAux : Tree → (ℕ → Rose) × ℕ :=
  WType.elim ((ℕ → Rose) × ℕ) fun x ↦
    match x with
    | ⟨some s, _⟩ =>
      (fun p ↦ ⟨⟨p + 1 + (encodeNat s.length).length, s.length⟩, [], []⟩,
        1 + (encodeNat s.length).length + s.length)
    | ⟨none, f⟩ =>
      (fun p ↦
        let l := (f false).1 (p + 1)
        let r := (f true).1 (p + 1 + (f false).2)
        ⟨l.label, l.children ++ [r.label], l.inner ++ r.inner ++ [⟨r.label, r.children⟩]⟩,
        1 + (f false).2 + (f true).2)

/-- The fold's length component is the encoding's length. -/
theorem roseAtAux_snd : ∀ t : Tree, (roseAtAux t).2 = (encode t).length :=
  tree_ind (fun s ↦ by
      change 1 + (encodeNat s.length).length + s.length = _
      rw [Geb.BitTree.Elias.encode_leaf, List.length_cons, List.length_append]
      omega)
    fun l r hl hr ↦ by
      change 1 + (roseAtAux l).2 + (roseAtAux r).2 = _
      rw [hl, hr, Geb.BitTree.Elias.encode_fork, List.length_cons, List.length_append]
      omega

/-- The open node of a tree at a position. -/
@[expose] def roseAt (t : Tree) (p : ℕ) : Rose := (roseAtAux t).1 p

/-- The open node of a leaf. -/
theorem roseAt_leaf (s : List Bool) (p : ℕ) :
    roseAt (leaf s) p = ⟨⟨p + 1 + (encodeNat s.length).length, s.length⟩, [], []⟩ := rfl

/-- The open node of a fork. -/
theorem roseAt_fork (l r : Tree) (p : ℕ) :
    roseAt (fork l r) p =
      ⟨(roseAt l (p + 1)).label,
        (roseAt l (p + 1)).children ++ [(roseAt r (p + 1 + (encode l).length)).label],
        (roseAt l (p + 1)).inner ++ (roseAt r (p + 1 + (encode l).length)).inner ++
          [⟨(roseAt r (p + 1 + (encode l).length)).label,
            (roseAt r (p + 1 + (encode l).length)).children⟩]⟩ := by
  have h : roseAt (fork l r) p =
      ⟨(roseAt l (p + 1)).label,
        (roseAt l (p + 1)).children ++ [(roseAt r (p + 1 + (roseAtAux l).2)).label],
        (roseAt l (p + 1)).inner ++ (roseAt r (p + 1 + (roseAtAux l).2)).inner ++
          [⟨(roseAt r (p + 1 + (roseAtAux l).2)).label,
            (roseAt r (p + 1 + (roseAtAux l).2)).children⟩]⟩ := rfl
  rw [h, roseAtAux_snd]

/-- The nodes of a tree at a position: those completed below its open node, and
the open node closed. -/
@[expose] def nodes (t : Tree) (p : ℕ) : List Node :=
  (roseAt t p).inner ++ [⟨(roseAt t p).label, (roseAt t p).children⟩]

/-- The word at a location inside a segment of a word. -/
theorem labelAt_append (u s v : List Bool) (l : Loc) (hp : l.pos = u.length)
    (hl : l.len = s.length) : labelAt (u ++ s ++ v) l = s := by
  unfold labelAt
  rw [hp, hl, List.append_assoc, List.drop_left, List.take_left]

/-- Every location the fold produces lies past the tree's first bit and within
its encoding: the open node's label, its children, and the nodes below. -/
theorem pos_roseAt_lt : ∀ (t : Tree) (p : ℕ),
    (p < (roseAt t p).label.pos ∧ (roseAt t p).label.pos + (roseAt t p).label.len ≤
      p + (encode t).length) ∧
    (∀ l ∈ (roseAt t p).children, p < l.pos ∧ l.pos + l.len ≤ p + (encode t).length) ∧
    ∀ n ∈ (roseAt t p).inner, (p < n.label.pos ∧
      n.label.pos + n.label.len ≤ p + (encode t).length) ∧
      ∀ l ∈ n.children, p < l.pos ∧ l.pos + l.len ≤ p + (encode t).length :=
  tree_ind (fun s p ↦ by
      rw [roseAt_leaf, Geb.BitTree.Elias.encode_leaf, List.length_cons, List.length_append]
      dsimp only
      exact ⟨⟨by omega, by omega⟩, fun _ h ↦ absurd h List.not_mem_nil,
        fun _ h ↦ absurd h List.not_mem_nil⟩)
    fun l r ihl ihr p ↦ by
      obtain ⟨⟨hl₁, hl₂⟩, hlc, hli⟩ := ihl (p + 1)
      obtain ⟨⟨hr₁, hr₂⟩, hrc, hri⟩ := ihr (p + 1 + (encode l).length)
      rw [roseAt_fork, Geb.BitTree.Elias.encode_fork, List.length_cons, List.length_append]
      dsimp only
      refine ⟨⟨by omega, by omega⟩, fun x hx ↦ ?_, fun n hn ↦ ?_⟩
      · rw [List.mem_append, List.mem_singleton] at hx
        rcases hx with hx | rfl
        · obtain ⟨h₁, h₂⟩ := hlc x hx
          exact ⟨by omega, by omega⟩
        · exact ⟨by omega, by omega⟩
      · rw [List.mem_append, List.mem_append, List.mem_singleton] at hn
        rcases hn with (hn | hn) | rfl
        · obtain ⟨⟨h₁, h₂⟩, h₃⟩ := hli n hn
          exact ⟨⟨by omega, by omega⟩, fun x hx ↦ by
            obtain ⟨h₄, h₅⟩ := h₃ x hx
            exact ⟨by omega, by omega⟩⟩
        · obtain ⟨⟨h₁, h₂⟩, h₃⟩ := hri n hn
          exact ⟨⟨by omega, by omega⟩, fun x hx ↦ by
            obtain ⟨h₄, h₅⟩ := h₃ x hx
            exact ⟨by omega, by omega⟩⟩
        · dsimp only
          exact ⟨⟨by omega, by omega⟩, fun x hx ↦ by
            obtain ⟨h₄, h₅⟩ := hrc x hx
            exact ⟨by omega, by omega⟩⟩

/-- Every node's label lies past the tree's first bit and within its encoding. -/
theorem nodes_pos_bounds (t : Tree) (p : ℕ) (n : Node) (hn : n ∈ nodes t p) :
    p < n.label.pos ∧ n.label.pos + n.label.len ≤ p + (encode t).length := by
  obtain ⟨h₁, _, h₃⟩ := pos_roseAt_lt t p
  unfold nodes at hn
  rw [List.mem_append, List.mem_singleton] at hn
  rcases hn with hn | rfl
  · exact (h₃ n hn).1
  · exact h₁

/-- A location sound in a word: past the first bit, and ending at the word's
end or at least two bits before it, as every node label of an encoding does. -/
@[expose] def Loc.Sound (y : List Bool) (l : Loc) : Prop :=
  1 ≤ l.pos ∧ (l.pos + l.len + 2 ≤ y.length ∨ l.pos + l.len = y.length)

/-- An encoding has at least two bits. -/
theorem two_le_length_encode : ∀ t : Tree, 2 ≤ (encode t).length :=
  tree_ind (fun s ↦ by
      rw [Geb.BitTree.Elias.encode_leaf, List.length_cons, List.length_append]
      have := Geb.BitTree.Elias.length_encodeNat_pos s.length
      omega)
    fun l r hl hr ↦ by
      rw [Geb.BitTree.Elias.encode_fork, List.length_cons, List.length_append]
      omega

/-- Every location the fold produces ends at the encoding's end or at least
two bits before it, and every node has fewer children than the encoding
has bits. -/
theorem end_roseAt : ∀ (t : Tree) (p : ℕ),
    ((roseAt t p).label.pos + (roseAt t p).label.len + 2 ≤ p + (encode t).length ∨
      (roseAt t p).label.pos + (roseAt t p).label.len = p + (encode t).length) ∧
    (roseAt t p).children.length + 1 ≤ (encode t).length ∧
    (∀ l ∈ (roseAt t p).children, l.pos + l.len + 2 ≤ p + (encode t).length ∨
      l.pos + l.len = p + (encode t).length) ∧
    ∀ n ∈ (roseAt t p).inner,
      (n.label.pos + n.label.len + 2 ≤ p + (encode t).length ∨
        n.label.pos + n.label.len = p + (encode t).length) ∧
      n.children.length + 1 ≤ (encode t).length ∧
      ∀ l ∈ n.children, l.pos + l.len + 2 ≤ p + (encode t).length ∨
        l.pos + l.len = p + (encode t).length :=
  tree_ind (fun s p ↦ by
      rw [roseAt_leaf, Geb.BitTree.Elias.encode_leaf, List.length_cons, List.length_append]
      dsimp only
      exact ⟨Or.inr (by omega),
        by rw [List.length_nil]; have := Geb.BitTree.Elias.length_encodeNat_pos s.length; omega,
        fun _ h ↦ absurd h List.not_mem_nil,
        fun _ h ↦ absurd h List.not_mem_nil⟩)
    fun l r ihl ihr p ↦ by
      obtain ⟨⟨hl₁, hl₂⟩, hlc, hli⟩ := pos_roseAt_lt l (p + 1)
      obtain ⟨_, hlk, _, hli'⟩ := ihl (p + 1)
      obtain ⟨hr₁, hrk, hrc, hri⟩ := ihr (p + 1 + (encode l).length)
      have h2 := two_le_length_encode r
      rw [roseAt_fork, Geb.BitTree.Elias.encode_fork, List.length_cons, List.length_append]
      dsimp only
      refine ⟨Or.inl (by omega), ?_, fun x hx ↦ ?_, fun n hn ↦ ?_⟩
      · rw [List.length_append, List.length_singleton]
        omega
      · rw [List.mem_append, List.mem_singleton] at hx
        rcases hx with hx | rfl
        · exact Or.inl (by have := (hlc x hx).2; omega)
        · rcases hr₁ with h | h
          · exact Or.inl (by omega)
          · exact Or.inr (by omega)
      · rw [List.mem_append, List.mem_append, List.mem_singleton] at hn
        rcases hn with (hn | hn) | rfl
        · obtain ⟨⟨_, h₂⟩, h₃⟩ := hli n hn
          refine ⟨Or.inl (by omega), by have := (hli' n hn).2.1; omega, fun x hx ↦ ?_⟩
          exact Or.inl (by have := (h₃ x hx).2; omega)
        · obtain ⟨h₁, h₂, h₃⟩ := hri n hn
          refine ⟨?_, by omega, fun x hx ↦ ?_⟩
          · rcases h₁ with h | h
            · exact Or.inl (by omega)
            · exact Or.inr (by omega)
          · rcases h₃ x hx with h | h
            · exact Or.inl (by omega)
            · exact Or.inr (by omega)
        · dsimp only
          refine ⟨?_, by omega, fun x hx ↦ ?_⟩
          · rcases hr₁ with h | h
            · exact Or.inl (by omega)
            · exact Or.inr (by omega)
          · rcases hrc x hx with h | h
            · exact Or.inl (by omega)
            · exact Or.inr (by omega)

/-- Every child location the fold produces is the label of a node of the tree,
the open node's children and the children of the nodes below alike. -/
theorem children_roseAt : ∀ (t : Tree) (p : ℕ),
    (∀ l ∈ (roseAt t p).children, ∃ n ∈ nodes t p, n.label = l) ∧
    ∀ m ∈ (roseAt t p).inner, ∀ l ∈ m.children, ∃ n ∈ nodes t p, n.label = l :=
  tree_ind (fun s p ↦ by
      rw [roseAt_leaf]
      exact ⟨fun _ h ↦ absurd h List.not_mem_nil, fun _ h ↦ absurd h List.not_mem_nil⟩)
    fun l r ihl ihr p ↦ by
      obtain ⟨hlc, hli⟩ := ihl (p + 1)
      obtain ⟨hrc, hri⟩ := ihr (p + 1 + (encode l).length)
      have hmem : ∀ n ∈ nodes l (p + 1), ∃ n' ∈ nodes (fork l r) p, n'.label = n.label := by
        intro n hn
        unfold nodes at hn ⊢
        rw [roseAt_fork]
        rw [List.mem_append, List.mem_singleton] at hn
        rcases hn with hn | rfl
        · exact ⟨n, List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ hn)),
            rfl⟩
        · exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _), rfl⟩
      have hmemr : ∀ n ∈ nodes r (p + 1 + (encode l).length),
          ∃ n' ∈ nodes (fork l r) p, n'.label = n.label := by
        intro n hn
        unfold nodes at hn ⊢
        rw [roseAt_fork]
        rw [List.mem_append, List.mem_singleton] at hn
        rcases hn with hn | rfl
        · exact ⟨n, List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ hn)),
            rfl⟩
        · exact ⟨_, List.mem_append_left _ (List.mem_append_right _ (List.mem_singleton_self _)),
            rfl⟩
      constructor
      · intro x hx
        rw [roseAt_fork] at hx
        dsimp only at hx
        rw [List.mem_append, List.mem_singleton] at hx
        rcases hx with hx | rfl
        · obtain ⟨n, hn, hnl⟩ := hlc x hx
          obtain ⟨n', hn', hn'l⟩ := hmem n hn
          exact ⟨n', hn', hn'l.trans hnl⟩
        · exact hmemr _ (List.mem_append_right _ (List.mem_singleton_self _))
      · intro m hm x hx
        rw [roseAt_fork] at hm
        dsimp only at hm
        rw [List.mem_append, List.mem_append, List.mem_singleton] at hm
        rcases hm with (hm | hm) | rfl
        · obtain ⟨n, hn, hnl⟩ := hli m hm x hx
          obtain ⟨n', hn', hn'l⟩ := hmem n hn
          exact ⟨n', hn', hn'l.trans hnl⟩
        · obtain ⟨n, hn, hnl⟩ := hri m hm x hx
          obtain ⟨n', hn', hn'l⟩ := hmemr n hn
          exact ⟨n', hn', hn'l.trans hnl⟩
        · obtain ⟨n, hn, hnl⟩ := hrc x hx
          obtain ⟨n', hn', hn'l⟩ := hmemr n hn
          exact ⟨n', hn', hn'l.trans hnl⟩

/-- Every child of a node of an encoding is the label of a node. -/
theorem children_mem_nodes (t : Tree) (n : Node) (hn : n ∈ nodes t 0) (l : Loc)
    (hl : l ∈ n.children) : ∃ n' ∈ nodes t 0, n'.label = l := by
  obtain ⟨hc, hi⟩ := children_roseAt t 0
  unfold nodes at hn
  rw [List.mem_append, List.mem_singleton] at hn
  rcases hn with hn | rfl
  · exact hi n hn l hl
  · exact hc l hl

/-- Every node of an encoding has a sound label, fewer children than the
encoding has bits, and sound children. -/
theorem nodes_sound (t : Tree) (n : Node) (hn : n ∈ nodes t 0) :
    Loc.Sound (encode t) n.label ∧ n.k + 1 ≤ (encode t).length ∧
      ∀ l ∈ n.children, Loc.Sound (encode t) l := by
  obtain ⟨⟨h₁, _⟩, hc, hi⟩ := pos_roseAt_lt t 0
  obtain ⟨e₁, ek, ec, ei⟩ := end_roseAt t 0
  rw [Nat.zero_add] at e₁ ec ei
  unfold nodes at hn
  rw [List.mem_append, List.mem_singleton] at hn
  rcases hn with hn | rfl
  · obtain ⟨⟨h₃, _⟩, h₄⟩ := hi n hn
    obtain ⟨e₃, e₄, e₅⟩ := ei n hn
    exact ⟨⟨h₃, e₃⟩, e₄, fun l hl ↦ ⟨(h₄ l hl).1, e₅ l hl⟩⟩
  · exact ⟨⟨h₁, e₁⟩, ek, fun l hl ↦ ⟨(hc l hl).1, ec l hl⟩⟩

namespace CodedSig

variable {I : Type} [DecidableEq I] (C : CodedSig I)

/-- The open node against the fold over the tree, at a tree encoded inside a
word: its label is the fold's leftmost label, its children are as many as the
spine, and the labels and edges below it are in order exactly when the fold
says so, the edges of the open spine counted with the spine's. -/
theorem roseAt_info : ∀ (t : Tree) (u v : List Bool),
    labelAt (u ++ encode t ++ v) (roseAt t u.length).label = (C.info t).label ∧
    (roseAt t u.length).children.length = (C.info t).spine ∧
    ((C.info t).labels = true ↔ ∀ n ∈ (roseAt t u.length).inner,
      C.labelSpec (labelAt (u ++ encode t ++ v) n.label) n.k = true) ∧
    ((C.info t).edges = true ↔
      (∀ n ∈ (roseAt t u.length).inner, ∀ (i : ℕ) (h : i < n.k),
        C.edgeSpec (labelAt (u ++ encode t ++ v) n.label) i
          (labelAt (u ++ encode t ++ v) n.children[i]) = true) ∧
      ∀ (i : ℕ) (h : i < (roseAt t u.length).children.length),
        C.edgeSpec (labelAt (u ++ encode t ++ v) (roseAt t u.length).label) i
          (labelAt (u ++ encode t ++ v) (roseAt t u.length).children[i]) = true) :=
  tree_ind (fun s u v ↦ by
      rw [roseAt_leaf, C.info_leaf, Geb.BitTree.Elias.encode_leaf]
      dsimp only
      refine ⟨?_, rfl, ?_, ?_⟩
      · rw [show u ++ false :: (encodeNat s.length ++ s) ++ v =
          (u ++ false :: encodeNat s.length) ++ s ++ v by
            simp only [List.append_assoc, List.cons_append]]
        exact labelAt_append _ s v _ (by simp only [List.length_append, List.length_cons]; omega)
          rfl
      · exact ⟨fun _ _ h ↦ absurd h List.not_mem_nil, fun _ ↦ rfl⟩
      · exact ⟨fun _ ↦ ⟨fun _ h ↦ absurd h List.not_mem_nil,
          fun _ h ↦ absurd h (Nat.not_lt_zero _)⟩, fun _ ↦ rfl⟩)
    fun l r ihl ihr u v ↦ by
      have el : u ++ encode (fork l r) ++ v = (u ++ [true]) ++ encode l ++ (encode r ++ v) := by
        simp only [Geb.BitTree.Elias.encode_fork, List.append_assoc, List.cons_append,
          List.nil_append]
      have er : u ++ encode (fork l r) ++ v = (u ++ true :: encode l) ++ encode r ++ v := by
        simp only [Geb.BitTree.Elias.encode_fork, List.append_assoc, List.cons_append]
      have hlu : (u ++ [true]).length = u.length + 1 := by
        rw [List.length_append, List.length_singleton]
      have hru : (u ++ true :: encode l).length = u.length + 1 + (encode l).length := by
        rw [List.length_append, List.length_cons]
        omega
      obtain ⟨hl₁, hl₂, hl₃, hl₄⟩ := ihl (u ++ [true]) (encode r ++ v)
      obtain ⟨hr₁, hr₂, hr₃, hr₄⟩ := ihr (u ++ true :: encode l) v
      rw [← el] at hl₁ hl₃ hl₄
      rw [← er] at hr₁ hr₃ hr₄
      rw [hlu] at hl₁ hl₂ hl₃ hl₄
      rw [hru] at hr₁ hr₂ hr₃ hr₄
      rw [roseAt_fork, C.info_fork]
      dsimp only
      refine ⟨hl₁, by rw [List.length_append, List.length_singleton, hl₂], ?_, ?_⟩
      · rw [Bool.and_eq_true, Bool.and_eq_true, hl₃, hr₃, ← hr₁, ← hr₂]
        constructor
        · rintro ⟨⟨h₁, h₂⟩, h₃⟩ n hn
          rw [List.mem_append, List.mem_append, List.mem_singleton] at hn
          rcases hn with (hn | hn) | rfl
          · exact h₁ n hn
          · exact h₂ n hn
          · exact h₃
        · intro h
          exact ⟨⟨fun n hn ↦ h n
              (by rw [List.mem_append, List.mem_append]; exact Or.inl (Or.inl hn)),
            fun n hn ↦ h n (by rw [List.mem_append, List.mem_append]; exact Or.inl (Or.inr hn))⟩,
            h ⟨(roseAt r (u.length + 1 + (encode l).length)).label,
              (roseAt r (u.length + 1 + (encode l).length)).children⟩
              (by rw [List.mem_append, List.mem_singleton]; exact Or.inr rfl)⟩
      · rw [Bool.and_eq_true, Bool.and_eq_true, hl₄, hr₄, ← hl₁, ← hr₁, ← hl₂]
        constructor
        · rintro ⟨⟨⟨h₁, h₂⟩, h₃, h₄⟩, h₅⟩
          refine ⟨fun n hn ↦ ?_, fun i hi ↦ ?_⟩
          · rw [List.mem_append, List.mem_append, List.mem_singleton] at hn
            rcases hn with (hn | hn) | rfl
            · exact h₁ n hn
            · exact h₃ n hn
            · exact h₄
          · rw [List.length_append, List.length_singleton] at hi
            by_cases hi' : i < (roseAt l (u.length + 1)).children.length
            · rw [List.getElem_append_left hi']
              exact h₂ i hi'
            · have hi'' : i = (roseAt l (u.length + 1)).children.length := by omega
              subst hi''
              rw [List.getElem_concat_length rfl]
              exact h₅
        · rintro ⟨h₁, h₂⟩
          have hspine : ∀ (i : ℕ) (hi : i < (roseAt l (u.length + 1)).children.length),
              C.edgeSpec (labelAt (u ++ encode (fork l r) ++ v) (roseAt l (u.length + 1)).label) i
                (labelAt (u ++ encode (fork l r) ++ v)
                  (roseAt l (u.length + 1)).children[i]) = true := fun i hi ↦ by
            have := h₂ i (by rw [List.length_append, List.length_singleton]; omega)
            rwa [List.getElem_append_left hi] at this
          have hlast := h₂ (roseAt l (u.length + 1)).children.length
            (by rw [List.length_append, List.length_singleton]; omega)
          rw [List.getElem_concat_length rfl] at hlast
          exact ⟨⟨⟨fun n hn ↦ h₁ n
              (by rw [List.mem_append, List.mem_append]; exact Or.inl (Or.inl hn)), hspine⟩,
            fun n hn ↦ h₁ n (by rw [List.mem_append, List.mem_append]; exact Or.inl (Or.inr hn)),
            h₁ ⟨(roseAt r (u.length + 1 + (encode l).length)).label,
              (roseAt r (u.length + 1 + (encode l).length)).children⟩
              (by rw [List.mem_append, List.mem_singleton]; exact Or.inr rfl)⟩, hlast⟩

/-- The labels are in order exactly when every node's label decodes to a shape
with as many directions as the node has children. -/
theorem labelsOk_iff_nodes (t : Tree) :
    C.labelsOk t = true ↔
      ∀ n ∈ nodes t 0, C.labelSpec (labelAt (encode t) n.label) n.k = true := by
  obtain ⟨h₁, h₂, h₃, _⟩ := C.roseAt_info t [] []
  simp only [List.nil_append, List.append_nil, List.length_nil] at h₁ h₂ h₃
  unfold labelsOk nodes
  rw [Bool.and_eq_true, h₃, ← h₁, ← h₂]
  constructor
  · rintro ⟨h, h'⟩ n hn
    rw [List.mem_append, List.mem_singleton] at hn
    rcases hn with hn | rfl
    · exact h n hn
    · exact h'
  · intro h
    exact ⟨fun n hn ↦ h n (by rw [List.mem_append]; exact Or.inl hn),
      h ⟨(roseAt t 0).label, (roseAt t 0).children⟩
        (by rw [List.mem_append, List.mem_singleton]; exact Or.inr rfl)⟩

/-- The edges are in order exactly when, at every node, each child's label
lies over the index the node's label prescribes at the child's position. -/
theorem edgesOk_iff_nodes (t : Tree) :
    C.edgesOk t = true ↔
      ∀ n ∈ nodes t 0, ∀ (i : ℕ) (h : i < n.k),
        C.edgeSpec (labelAt (encode t) n.label) i (labelAt (encode t) n.children[i]) = true := by
  obtain ⟨_, _, _, h₄⟩ := C.roseAt_info t [] []
  simp only [List.nil_append, List.append_nil, List.length_nil] at h₄
  unfold edgesOk nodes
  rw [h₄]
  constructor
  · rintro ⟨h, h'⟩ n hn
    rw [List.mem_append, List.mem_singleton] at hn
    rcases hn with hn | rfl
    · exact h n hn
    · exact h'
  · intro h
    exact ⟨fun n hn ↦ h n (by rw [List.mem_append]; exact Or.inl hn),
      h ⟨(roseAt t 0).label, (roseAt t 0).children⟩
        (by rw [List.mem_append, List.mem_singleton]; exact Or.inr rfl)⟩

end CodedSig

end

end Geb.SizeBounded.Logspace.WTree
