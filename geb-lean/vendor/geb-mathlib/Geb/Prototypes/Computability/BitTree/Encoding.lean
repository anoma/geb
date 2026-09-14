/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
-- Modified from geb-mathlib by scripts/geb-mathlib-backport.patch.
module

public import Geb.Prototypes.Computability.BitTree.Scanner
public import Mathlib.Data.W.Basic

set_option doc.verso true

/-!
# Binary trees with bitstrings at the leaves

The W-type of the polynomial {lit}`X ↦ List Bool + X × X` has a direct binary
encoding. A fork is {lit}`1`, a leaf starts with {lit}`0`, each payload bit
{lit}`b` is escaped as {lit}`1b`, and {lit}`0` terminates the payload.

## Main definitions

* {lit}`Tree` is the W-type, with constructors {lit}`leaf` and {lit}`fork`.
* {lit}`encode` serializes a tree.
* {lit}`validBool` scans a word once, retaining a mode and a pending-tree count.

## Main statements

* {lit}`validBool_iff` characterizes acceptance by existence of an encoded tree.
* {lit}`encode_injective` states uniqueness of the encoded tree.
* {lit}`length_encode` counts the bits in the representation.

## Tags

binary tree, bitstring, encoding, recognizer, W-type
-/

@[expose] public section

namespace Geb.BitTree

/-- Node shapes: a labelled leaf or a binary fork. -/
abbrev Shape := Option (List Bool)

/-- Leaves have no children; forks have two children indexed by booleans. -/
def Arity : Shape → Type
  | some _ => Empty
  | none => Bool

/-- The initial algebra of {lit}`X ↦ List Bool + X × X`. -/
abbrev Tree := WType Arity

/-- A leaf carrying a bitstring. -/
def leaf (s : List Bool) : Tree := WType.mk (some s) Empty.elim

/-- A binary fork, with the left child indexed by false. -/
def fork (l r : Tree) : Tree := WType.mk none fun b : Bool ↦ if b then r else l

/-- The two-constructor induction principle of the underlying W-type. -/
theorem tree_ind {P : Tree → Prop} (hl : ∀ s, P (leaf s))
    (hf : ∀ l r, P l → P r → P (fork l r)) : ∀ t, P t :=
  WType.rec fun a f ih ↦ by
    cases a with
    | some s =>
      have h : f = Empty.elim := funext fun e ↦ e.elim
      subst f
      exact hl s
    | none =>
      have h : (fun b : Bool ↦ if b then f true else f false) = f :=
        funext fun b ↦ by cases b <;> rfl
      exact h ▸ hf (f false) (f true) (ih false) (ih true)

/-- Escape payload bits and terminate the string. -/
def encodeString (s : List Bool) : List Bool := s.foldr (fun b w ↦ true :: b :: w) [false]

@[simp] theorem encodeString_nil : encodeString [] = [false] := rfl

@[simp] theorem encodeString_cons (b : Bool) (s : List Bool) :
    encodeString (b :: s) = true :: b :: encodeString s := rfl

/-- Preorder encoding with a mode-dependent code for leaves and their payloads. -/
def encode : Tree → List Bool := WType.elim (List Bool) fun x ↦
  match x with
  | ⟨some s, _⟩ => false :: encodeString s
  | ⟨none, f⟩ => true :: (f false ++ f true)

@[simp] theorem encode_leaf (s : List Bool) : encode (leaf s) = false :: encodeString s := rfl

@[simp] theorem encode_fork (l r : Tree) :
    encode (fork l r) = true :: (encode l ++ encode r) := rfl

/-- Scanning an escaped string completes one pending tree. -/
theorem foldl_encodeString (s : List Bool) (n : Nat) :
    (encodeString s).foldl step (.string, n) = finish n :=
  List.rec rfl (fun b s ih ↦ by simpa [encodeString, step] using ih) s

/-- Scanning one encoded tree completes exactly one pending tree. -/
theorem foldl_encode (t : Tree) : ∀ n, 0 < n →
    (encode t).foldl step (.tree, n) = finish n :=
  tree_ind (P := fun t ↦ ∀ n, 0 < n → (encode t).foldl step (.tree, n) = finish n)
    (fun s n _ ↦ by simpa [step] using foldl_encodeString s n)
    (fun l r ihl ihr n hn ↦ by
      simp only [encode_fork, List.foldl_cons, step, List.foldl_append, ↓reduceIte]
      rw [ihl (n + 1) (by omega)]
      have h : finish (n + 1) = (.tree, n) := by
        rw [finish, if_neg (show n + 1 ≠ 1 by omega)]
        rfl
      rw [h, ihr n hn]) t

/-- Every encoded tree is accepted. -/
@[simp] theorem validBool_encode (t : Tree) : validBool (encode t) = true := by
  simp [validBool, scan, foldl_encode t 1 (by omega), finish]

/-- An escaped string can be cancelled from a prefix without losing its boundary. -/
theorem encodeString_append_injective (s : List Bool) : ∀ t u v,
    encodeString s ++ u = encodeString t ++ v → s = t ∧ u = v :=
  List.rec
    (fun t u v h ↦ by
      cases t with
      | nil => exact ⟨rfl, (List.cons.inj h).2⟩
      | cons _ _ => simp at h)
    (fun b s ih t u v h ↦ by
      cases t with
      | nil => simp at h
      | cons c t =>
        obtain ⟨hbc, hrest⟩ := List.cons.inj (List.cons.inj h).2
        obtain ⟨hst, huv⟩ := ih t u v hrest
        exact ⟨by simp [hbc, hst], huv⟩) s

/-- An encoded tree determines both its value and its boundary in a longer word. -/
theorem encode_append_injective (t : Tree) : ∀ t' u v,
    encode t ++ u = encode t' ++ v → t = t' ∧ u = v :=
  tree_ind
    (P := fun t ↦ ∀ t' u v, encode t ++ u = encode t' ++ v → t = t' ∧ u = v)
    (fun s t' ↦ tree_ind
      (P := fun t' ↦ ∀ u v, encode (leaf s) ++ u = encode t' ++ v →
        leaf s = t' ∧ u = v)
      (fun s' u v h ↦ by
        obtain ⟨hs, huv⟩ := encodeString_append_injective s s' u v (List.cons.inj h).2
        exact ⟨congrArg leaf hs, huv⟩)
      (fun _ _ _ _ u v h ↦ by simp at h) t')
    (fun l r ihl ihr t' ↦ tree_ind
      (P := fun t' ↦ ∀ u v, encode (fork l r) ++ u = encode t' ++ v →
        fork l r = t' ∧ u = v)
      (fun _ u v h ↦ by simp at h)
      (fun l' r' _ _ u v h ↦ by
        have he : encode l ++ (encode r ++ u) = encode l' ++ (encode r' ++ v) := by
          have he' := congrArg List.tail h
          change (encode l ++ encode r) ++ u = (encode l' ++ encode r') ++ v at he'
          simpa only [List.append_assoc] using he'
        obtain ⟨hl, hr⟩ := ihl l' (encode r ++ u) (encode r' ++ v) he
        obtain ⟨hr', huv⟩ := ihr r' u v hr
        exact ⟨by rw [hl, hr'], huv⟩) t') t

/-- The direct binary encoding is injective. -/
theorem encode_injective : Function.Injective encode := fun t t' h ↦
  (encode_append_injective t t' [] [] (by simpa using h)).1

/-- Forest encoding is the concatenation of its component encodings. -/
def encodeForest (ts : List Tree) : List Bool := ts.flatMap encode

/-- The grammar of the remaining suffix in each scanner mode. -/
def Completion (s : State) (w : List Bool) : Prop :=
  match s.1 with
  | .tree => ∃ ts, ts.length = s.2 ∧ w = encodeForest ts
  | .string => ∃ bs ts, ts.length + 1 = s.2 ∧ w = encodeString bs ++ encodeForest ts
  | .bit => ∃ b bs ts, ts.length + 1 = s.2 ∧
      w = b :: (encodeString bs ++ encodeForest ts)
  | .done => w = []
  | .dead => False

/-- A successful scan supplies a grammatical decomposition of its whole suffix. -/
theorem completion_of_accept (w : List Bool) : ∀ s, Active s →
    (w.foldl step s).1 = .done → Completion s w :=
  List.rec
    (fun s _ h ↦ by rcases s with ⟨m, n⟩; cases m <;> simp_all [Completion])
    (fun b w ih s hs ha ↦ by
      have hc := ih (step s b) (active_step s b hs) ha
      rcases s with ⟨m, n⟩
      cases m with
      | tree =>
        have hn : 0 < n := hs (Or.inl rfl)
        cases b with
        | false =>
          obtain ⟨bs, ts, ht, hw⟩ := hc
          exact ⟨leaf bs :: ts, ht, by simp [encodeForest, hw]⟩
        | true =>
          change ∃ ts, ts.length = n + 1 ∧ w = encodeForest ts at hc
          obtain ⟨ts, ht, hw⟩ := hc
          cases ts with
          | nil =>
            exfalso
            change 0 = n + 1 at ht
            omega
          | cons l ts =>
            cases ts with
            | nil =>
              exfalso
              change 1 = n + 1 at ht
              omega
            | cons r ts =>
              refine ⟨fork l r :: ts, by simp only [List.length_cons] at ht ⊢; omega, ?_⟩
              simp [encodeForest, hw, List.append_assoc]
      | string =>
        cases b with
        | false =>
          by_cases hn : n = 1
          · have hw : w = [] := by simpa [step, finish, hn, Completion] using hc
            exact ⟨[], [], by simpa using hn.symm, by simp [hw, encodeForest]⟩
          · obtain ⟨ts, ht, hw⟩ : ∃ ts, ts.length = n - 1 ∧ w = encodeForest ts := by
              simpa [step, finish, hn, Completion] using hc
            have hp := hs (Or.inr (Or.inl rfl))
            exact ⟨[], ts, by omega, by simp [hw]⟩
        | true =>
          obtain ⟨c, bs, ts, ht, hw⟩ := hc
          exact ⟨c :: bs, ts, ht, by simp [hw]⟩
      | bit =>
        obtain ⟨bs, ts, ht, hw⟩ := hc
        exact ⟨b, bs, ts, ht, by simp [hw]⟩
      | done => exact False.elim hc
      | dead => exact False.elim hc) w

/-- Acceptance is equivalent to being the encoding of a binary tree of bitstrings. -/
theorem validBool_iff (w : List Bool) : validBool w = true ↔ ∃ t, encode t = w := by
  constructor
  · intro h
    have hc := completion_of_accept w (.tree, 1) (by simp [Active])
      (of_decide_eq_true h)
    obtain ⟨ts, ht, hw⟩ := hc
    cases ts with
    | nil => simp at ht
    | cons t ts =>
      have he : ts = [] := List.eq_nil_of_length_eq_zero (by change ts.length + 1 = 1 at ht; omega)
      subst ts
      exact ⟨t, by simpa [encodeForest] using hw.symm⟩
  · rintro ⟨t, rfl⟩
    exact validBool_encode t

/-- Every accepted word represents exactly one tree. -/
theorem validBool_iff_existsUnique (w : List Bool) :
    validBool w = true ↔ ∃! t, encode t = w := by
  rw [validBool_iff]
  constructor
  · rintro ⟨t, ht⟩
    exact ⟨t, ht, fun t' ht' ↦ encode_injective (ht'.trans ht.symm)⟩
  · rintro ⟨t, ht, _⟩
    exact ⟨t, ht⟩

/-- The number of forks, leaves, and payload bits, respectively. -/
def counts : Tree → Nat × Nat × Nat := WType.elim (Nat × Nat × Nat) fun x ↦
  match x with
  | ⟨some s, _⟩ => (0, 1, s.length)
  | ⟨none, f⟩ => (1 + (f false).1 + (f true).1,
      (f false).2.1 + (f true).2.1, (f false).2.2 + (f true).2.2)

@[simp] theorem counts_leaf (s : List Bool) : counts (leaf s) = (0, 1, s.length) := rfl

@[simp] theorem counts_fork (l r : Tree) :
    counts (fork l r) = ((counts l).1 + (counts r).1 + 1,
      (counts l).2.1 + (counts r).2.1, (counts l).2.2 + (counts r).2.2) := by
  change (1 + (counts l).1 + (counts r).1, _, _) = _
  congr 1
  omega

/-- A full binary tree has one more leaf than fork. -/
theorem leaves_eq_forks_add_one (t : Tree) : (counts t).2.1 = (counts t).1 + 1 :=
  tree_ind (P := fun t ↦ (counts t).2.1 = (counts t).1 + 1)
    (fun s ↦ rfl) (fun l r ihl ihr ↦ by simp only [counts_fork]; omega) t

/-- Escaping uses two bits per payload bit and one terminator. -/
@[simp] theorem length_encodeString (s : List Bool) :
    (encodeString s).length = 2 * s.length + 1 :=
  List.rec rfl (fun b s ih ↦ by simp only [encodeString_cons, List.length_cons]; omega) s

/-- The encoding uses one bit per fork, two per leaf, and two per payload bit. -/
theorem length_encode (t : Tree) :
    (encode t).length = (counts t).1 + 2 * (counts t).2.1 + 2 * (counts t).2.2 :=
  tree_ind (P := fun t ↦ (encode t).length =
      (counts t).1 + 2 * (counts t).2.1 + 2 * (counts t).2.2)
    (fun s ↦ by
      change (false :: encodeString s).length = 0 + 2 * 1 + 2 * s.length
      simp; omega)
    (fun l r ihl ihr ↦ by
      simp only [encode_fork, List.length_cons, List.length_append]
      change _ = (1 + (counts l).1 + (counts r).1) +
        2 * ((counts l).2.1 + (counts r).2.1) +
        2 * ((counts l).2.2 + (counts r).2.2)
      omega) t

/-- Counting leaves through the full-binary-tree identity eliminates one parameter. -/
theorem length_encode_forks (t : Tree) :
    (encode t).length = 3 * (counts t).1 + 2 + 2 * (counts t).2.2 := by
  rw [length_encode, leaves_eq_forks_add_one]
  omega

end Geb.BitTree
