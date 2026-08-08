/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Mathlib.Data.Tree.Binary

/-!
# The preorder encoding of binary trees as bitstrings

A leaf is spelled by one `false` bit, a node by a `true` bit followed by
its two children's spellings. The encoding is a bijection onto the
bitstrings satisfying `Valid`, the condition that the stack depth read
right to left reads every node bit at depth at least two, and ends at
one.

The idea is that of prefix notation, in which a symbol is followed by
exactly as many operands as its arity. Here the two unlabelled shapes
play those roles, the node bit taking two operands and the leaf bit
none.

`Valid` is stated as two conditions, in the manner of mathlib's
`DyckWord`, whose fields `count_U_eq_count_D` and `count_D_le_count_U`
play the roles that `depth w = 1` and `ok` play here, and in the
direction a single right-to-left pass carrying a counter can scan.

## Main definitions

* `BinTree.print` — the encoding.
* `BinTree.parseStep`, `BinTree.parseAux`, `BinTree.parse` — the
  fuel-bounded recursive-descent decoding.
* `BinTree.depth` — the stack depth, read right to left, truncated at
  zero.
* `BinTree.ok` — every node bit is read at depth at least two.
* `BinTree.Valid` — the two conditions together.

## Main statements

* `BinTree.parse_print` — the retraction law.
* `BinTree.parseAux_eq_some` — whatever the descent reads, it reads a
  spelling.
* `BinTree.parse_eq_some_iff` — the decoding is the inverse of the
  encoding, on the nose.
* `BinTree.print_injective` — distinct trees have distinct spellings.
* `BinTree.valid_print` — every spelling is valid.
* `BinTree.valid_iff_exists_print` — the valid words are exactly the
  spellings.
* `BinTree.valid_iff_isSome_parse` — `parse` decides `Valid`.

## Implementation notes

`parseAux` recurses on an explicit `ℕ` bound rather than on its input:
the second child is parsed from a remainder the first call computes,
which is not a structural subterm. `parse` supplies the input's length,
and `length_print` shows that bound admits every tree `print` emits.

Fuel exhaustion is not a rejection mechanism of its own, beyond the
three the parser has: empty input and a child's failure, both from
`parseStep`, and the trailing input `parse` rejects. Each `parseStep`
layer consumes at least the head bit before delegating to the next, so
the invariant `fuel ≥ remaining length` holds from `parse`'s initial
`w.length` all the way down; when the fuel reaches zero the remaining
input is already empty, and `parseStep []` returns `none` whatever fuel
it is given.

`exists_print_append_of_ok_of_one_le_depth` is likewise bounded by an
explicit `ℕ` and driven by `Nat.rec`. Its node case applies the
hypothesis to a proper suffix and then to a suffix of that; both uses sit
at the same bound, so no well-founded recursion is needed.

## Tags

binary tree, preorder, prefix notation, encoding, retraction
-/

namespace BinTree

public section

/-- The preorder encoding: a leaf is one `false` bit, a node a `true` bit
followed by its two children's encodings. -/
@[expose] def print : BinTree → List Bool :=
  WType.elim (List Bool) fun x ↦
    match x with
    | ⟨.leaf, _⟩ => [false]
    | ⟨.node, ch⟩ => true :: (ch (0 : Fin 2) ++ ch (1 : Fin 2))

@[simp] theorem print_leaf : print leaf = [false] := rfl

@[simp] theorem print_node (l r : BinTree) :
    print (node l r) = true :: (print l ++ print r) := rfl

/-- One layer of the recursive descent: read one tree, delegating each
child to `child`, and return it with the unconsumed remainder. -/
@[expose] def parseStep (child : List Bool → Option (BinTree × List Bool)) :
    List Bool → Option (BinTree × List Bool)
  | [] => none
  | false :: rest => some (leaf, rest)
  | true :: rest =>
    match child rest with
    | none => none
    | some (l, rest₁) =>
      match child rest₁ with
      | none => none
      | some (r, rest₂) => some (node l r, rest₂)

/-- Recursive descent bounded by an explicit `ℕ`. -/
@[expose] def parseAux : ℕ → List Bool → Option (BinTree × List Bool) :=
  Nat.rec (fun _ ↦ none) fun _ ih ↦ parseStep ih

theorem parseAux_succ (f : ℕ) :
    parseAux (f + 1) = parseStep (parseAux f) := rfl

/-- The decoding, rejecting trailing input. -/
@[expose] def parse (w : List Bool) : Option BinTree :=
  match parseAux w.length w with
  | some (t, []) => some t
  | _ => none

/-- The stack depth of a bitstring read right to left: a leaf bit pushes,
a node bit pops two and pushes one. Subtraction is truncated at zero;
`ok` is the separate condition under which each pop has two operands. -/
@[expose] def depth : List Bool → ℕ :=
  List.rec 0 fun b _ ih ↦ if b then ih - 1 else ih + 1

@[simp] theorem depth_nil : depth [] = 0 := rfl

@[simp] theorem depth_cons_false (v : List Bool) :
    depth (false :: v) = depth v + 1 := rfl

@[simp] theorem depth_cons_true (v : List Bool) :
    depth (true :: v) = depth v - 1 := rfl

/-- Every node bit is read at a depth of at least two, so that popping
two operands is defined. This is strictly stronger than absence of
truncation: `[true, false]` truncates nowhere, since `depth [false] = 1`
and `1 - 1` is exact, yet fails `ok`. -/
@[expose] def ok : List Bool → Bool :=
  List.rec true fun b v ih ↦ ih && (if b then decide (2 ≤ depth v) else true)

@[simp] theorem ok_nil : ok [] = true := rfl

@[simp] theorem ok_cons_false (v : List Bool) : ok (false :: v) = ok v := by
  simp [ok]

@[simp] theorem ok_cons_true (v : List Bool) :
    ok (true :: v) = (ok v && decide (2 ≤ depth v)) := rfl

/-- A bitstring spells a tree: `ok` holds of it, and it leaves a single
tree on the stack. The tree is unique, by `print_injective`. -/
@[expose] def Valid (w : List Bool) : Prop := ok w = true ∧ depth w = 1

/-- A spelling's length is the tree's node count, so the input length is
fuel enough for `parseAux` to read anything `print` emits. -/
theorem length_print (t : BinTree) : (print t).length = t.size :=
  BinTree.induction (motive := fun t ↦ (print t).length = t.size)
    rfl
    (fun l r ihl ihr ↦ by
      simp only [print_node, List.length_cons, List.length_append, ihl, ihr,
        size_node]) t

/-- The parser inverts the printer on printed input, given fuel at least
the tree's node count, and returns the unconsumed remainder. -/
theorem parseAux_print (t : BinTree) :
    ∀ (f : ℕ) (rest : List Bool), t.size ≤ f →
      parseAux f (print t ++ rest) = some (t, rest) :=
  BinTree.induction (motive := fun t ↦ ∀ (f : ℕ) (rest : List Bool), t.size ≤ f →
      parseAux f (print t ++ rest) = some (t, rest))
    (fun f rest hf ↦ by
      cases f with
      | zero => simp at hf
      | succ f => simp [parseAux_succ, parseStep])
    (fun l r ihl ihr f rest hf ↦ by
      cases f with
      | zero => simp at hf
      | succ f =>
        have hl : l.size ≤ f := by simp at hf; omega
        have hr : r.size ≤ f := by simp at hf; omega
        simp only [print_node, List.cons_append, parseAux_succ, parseStep,
          List.append_assoc]
        rw [ihl f _ hl]
        -- reduce the match on the `some` just produced, exposing the
        -- second child
        simp only []
        rw [ihr f _ hr]) t

/-- Whatever the descent reads, it reads a spelling: the tree returned,
spelled and followed by the remainder, is the input. -/
theorem parseAux_eq_some : ∀ (f : ℕ) (w : List Bool) (t : BinTree)
    (rest : List Bool), parseAux f w = some (t, rest) → print t ++ rest = w :=
  Nat.rec
    (fun _ _ _ h ↦ nomatch h)
    (fun f ih w t rest h ↦ by
      match w with
      | [] =>
        rw [parseAux_succ, parseStep] at h
        contradiction
      | false :: v =>
        rw [parseAux_succ, parseStep] at h
        have h' := Option.some.inj h
        injection h' with ht hrest
        subst ht; subst hrest
        rfl
      | true :: v =>
        rw [parseAux_succ, parseStep] at h
        split at h
        · contradiction
        · rename_i l rest₁ h₁
          split at h
          · contradiction
          · rename_i r rest₂ h₂
            have h' := Option.some.inj h
            injection h' with ht hrest
            subst ht; subst hrest
            rw [print_node, List.cons_append, List.append_assoc,
              ih rest₁ r rest₂ h₂, ih v l rest₁ h₁])

/-- The retraction law: the parser recovers every tree the printer
spells. -/
theorem parse_print (t : BinTree) : parse (print t) = some t := by
  have h := parseAux_print t (print t).length [] (le_of_eq (length_print t).symm)
  rw [List.append_nil] at h
  simp [parse, h]

/-- The parser succeeds exactly on the spellings, returning the tree
spelled: `parse` and `print` are mutually inverse. -/
theorem parse_eq_some_iff {w : List Bool} {t : BinTree} :
    parse w = some t ↔ print t = w := by
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ parse_print t⟩
  rw [parse] at h
  split at h
  · rename_i t' hp
    rw [← Option.some.inj h]
    simpa using parseAux_eq_some w.length w t' [] hp
  · contradiction

/-- Distinct trees have distinct spellings. -/
theorem print_injective : Function.Injective print := by
  intro a b h
  have ha := parse_print a
  rw [h, parse_print b] at ha
  exact (Option.some.inj ha).symm

/-- A spelling followed by anything leaves the depth one higher. -/
theorem depth_print (t : BinTree) :
    ∀ rest : List Bool, depth (print t ++ rest) = depth rest + 1 :=
  BinTree.induction (motive := fun t ↦ ∀ rest : List Bool,
      depth (print t ++ rest) = depth rest + 1)
    (fun rest ↦ by simp)
    (fun l r ihl ihr rest ↦ by
      simp only [print_node, List.cons_append, List.append_assoc,
        depth_cons_true, ihl, ihr]
      omega) t

/-- A spelling followed by anything satisfies `ok` exactly when what
follows it does. -/
theorem ok_print (t : BinTree) :
    ∀ rest : List Bool, ok (print t ++ rest) = ok rest :=
  BinTree.induction (motive := fun t ↦ ∀ rest : List Bool,
      ok (print t ++ rest) = ok rest)
    (fun rest ↦ by simp)
    (fun l r ihl ihr rest ↦ by
      simp only [print_node, List.cons_append, List.append_assoc,
        ok_cons_true, ihl, ihr, depth_print]
      simp) t

/-- A word satisfying `ok` that carries at least one tree has a complete
tree as a prefix. -/
theorem exists_print_append_of_ok_of_one_le_depth :
    ∀ (n : ℕ) (w : List Bool), w.length ≤ n → ok w = true →
      1 ≤ depth w → ∃ t rest, print t ++ rest = w ∧ depth rest + 1 = depth w ∧
        ok rest = true :=
  Nat.rec
    (fun w hw _ hd ↦ by
      have hnil : w = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.mp hw)
      subst hnil; simp at hd)
    (fun n ih w hw hok hd ↦ by
      match w with
      | [] => simp at hd
      | false :: v => exact ⟨leaf, v, by simp, by simp, by simpa using hok⟩
      | true :: v =>
        rw [ok_cons_true] at hok
        rw [depth_cons_true] at hd
        have hokv : ok v = true := (Bool.and_eq_true _ _ |>.mp hok).1
        have hdv : 2 ≤ depth v := by
          have := (Bool.and_eq_true _ _ |>.mp hok).2
          simpa using this
        have hwv : v.length ≤ n := by simp at hw; omega
        obtain ⟨l, rest₁, hl, hd₁, hok₁⟩ := ih v hwv hokv (by omega)
        have hrest₁ : rest₁.length ≤ n := by
          have : rest₁.length ≤ v.length := by
            rw [← hl, List.length_append]; omega
          omega
        obtain ⟨r, rest₂, hr, hd₂, hok₂⟩ :=
          ih rest₁ hrest₁ hok₁ (by omega)
        refine ⟨node l r, rest₂, ?_, by rw [depth_cons_true]; omega, hok₂⟩
        rw [print_node, List.cons_append, List.append_assoc, hr, hl])

/-- A word satisfying `ok` that carries no tree is empty. -/
theorem eq_nil_of_ok_of_depth_eq_zero (w : List Bool) (h : ok w = true)
    (hd : depth w = 0) : w = [] := by
  match w with
  | [] => rfl
  | false :: v => simp at hd
  | true :: v =>
    rw [ok_cons_true] at h
    have := (Bool.and_eq_true _ _ |>.mp h).2
    simp only [decide_eq_true_eq] at this
    rw [depth_cons_true] at hd
    omega

/-- Every valid word is a spelling: the converse of `valid_print`. -/
theorem exists_print_of_valid {w : List Bool} (h : Valid w) :
    ∃ t, print t = w := by
  obtain ⟨hok, hd⟩ := h
  obtain ⟨t, rest, he, hd', hok'⟩ :=
    exists_print_append_of_ok_of_one_le_depth w.length w le_rfl hok (by omega)
  have hz : depth rest = 0 := by omega
  have hnil : rest = [] := eq_nil_of_ok_of_depth_eq_zero rest hok' hz
  subst hnil
  exact ⟨t, by simpa using he⟩

/-- Every spelling is valid. -/
theorem valid_print (t : BinTree) : Valid (print t) := by
  constructor
  · have := ok_print t []; rw [List.append_nil] at this; simp [this]
  · have := depth_print t []; rw [List.append_nil] at this; simp [this]

/-- The encoding's image is exactly the valid words: the characterization
the recognizer's correctness is stated against. -/
theorem valid_iff_exists_print (w : List Bool) : Valid w ↔ ∃ t, print t = w :=
  ⟨exists_print_of_valid, fun ⟨t, ht⟩ ↦ ht ▸ valid_print t⟩

/-- `parse` decides `Valid`: a word is valid exactly when the parser
accepts it. -/
theorem valid_iff_isSome_parse (w : List Bool) : Valid w ↔ (parse w).isSome := by
  rw [valid_iff_exists_print]
  refine ⟨fun ⟨t, ht⟩ ↦ ?_, fun h ↦ ?_⟩
  · rw [← ht, parse_print]; rfl
  · obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp h
    exact ⟨t, parse_eq_some_iff.mp ht⟩

end

end BinTree
