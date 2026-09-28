/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
-- Modified from geb-mathlib by scripts/geb-mathlib-backport.patch.
module

public import Geb.Prototypes.Computability.BitTree.Elias.ScannerHeader
public import Geb.Prototypes.Computability.BitTree.Elias.Tree

set_option doc.verso true in
/-!
# Correctness of the streaming tree recognizer

One pending subtree is discharged by each complete tree encoding. Conversely, an accepting
scan with several pending subtrees determines a forest of exactly that many trees. The
single-root instance identifies the streaming recognizer with the canonical tree decoder.

## Main statements

* {lit}`foldl_encode` describes the scanner's action on any encoded tree.
* {lit}`forest_of_accept` reconstructs a forest from an accepting scan.
* {lit}`validBool_eq` identifies the scanner and decoder decisions.

## Tags

Elias delta code, binary tree, recognizer correctness
-/

set_option doc.verso true

@[expose] public section

namespace Geb.BitTree.Elias.Scanner

/-- An encoded tree completes exactly one pending subtree. -/
theorem foldl_encode (t : Tree) : ∀ n, 0 < n →
    (Elias.encode t).foldl step (.tree, n) = finish n :=
  tree_ind (P := fun t ↦ ∀ n, 0 < n →
      (Elias.encode t).foldl step (.tree, n) = finish n)
    (fun s n _ ↦ by
      rw [Elias.encode_leaf, List.foldl_cons]
      change (encodeNat s.length ++ s).foldl step (.zeros 0, n) = _
      rw [List.foldl_append, foldl_encodeNat]
      cases s with
      | nil => rfl
      | cons b bs =>
        rw [if_neg (by simp only [List.length_cons]; omega)]
        exact foldl_payload (b :: bs) n (by intro h; cases h))
    (fun l r hl hr n hn ↦ by
      rw [Elias.encode_fork, List.foldl_cons]
      change (Elias.encode l ++ Elias.encode r).foldl step (.tree, n + 1) = _
      rw [List.foldl_append, hl (n + 1) (by omega)]
      have hf : finish (n + 1) = (.tree, n) := by
        rw [finish, if_neg (by omega), Nat.add_sub_cancel]
      rw [hf, hr n hn]) t

/-- Acceptance from several pending roots reconstructs an ordered forest. -/
theorem forest_of_accept (w : List Bool) (n : ℕ) (hn : 0 < n)
    (h : (w.foldl step (.tree, n)).1 = .done) :
    ∃ ts : List Tree, ts.length = n ∧ w = ts.flatMap Elias.encode := by
  have aux : ∀ k, ∀ w : List Bool, w.length = k → ∀ n, 0 < n →
      (w.foldl step (.tree, n)).1 = .done →
      ∃ ts : List Tree, ts.length = n ∧ w = ts.flatMap Elias.encode := fun k ↦
    Nat.strongRecOn k fun k ih w hw n hn h ↦ by
      cases w with
      | nil => cases h
      | cons b bs =>
        have hbs : bs.length < k := by simp only [List.length_cons] at hw; omega
        cases b with
        | true =>
          change (bs.foldl step (.tree, n + 1)).1 = .done at h
          obtain ⟨ts, ht, he⟩ := ih bs.length hbs bs rfl (n + 1) (by omega) h
          cases ts with
          | nil => exfalso; simp only [List.length_nil] at ht; omega
          | cons l ts =>
            cases ts with
            | nil => exfalso; simp only [List.length_cons, List.length_nil] at ht; omega
            | cons r ts =>
              refine ⟨fork l r :: ts, ?_, ?_⟩
              · simp only [List.length_cons] at ht ⊢
                omega
              · rw [he]
                simp only [List.flatMap_cons, Elias.encode_fork, List.cons_append,
                  List.append_assoc]
        | false =>
          change (bs.foldl step (.zeros 0, n)).1 = .done at h
          cases hh : readNat bs with
          | none => exact (header_reject bs n hh h).elim
          | some p =>
            rcases p with ⟨m, suffix⟩
            rw [foldl_header bs m suffix n hh] at h
            obtain ⟨s, rest, hs, hsuf, hr⟩ := payload_of_accept suffix m n h
            have he : bs = encodeNat s.length ++ s ++ rest := by
              rw [readNat_eq_some bs m suffix hh, hsuf, hs, List.append_assoc]
            by_cases hn1 : n = 1
            · subst n
              change (rest.foldl step (.done, 0)).1 = .done at hr
              have hrest := (foldl_done rest 0).mp hr
              refine ⟨[leaf s], rfl, ?_⟩
              rw [he, hrest]
              simp only [List.append_nil, List.flatMap_cons, List.flatMap_nil,
                Elias.encode_leaf]
            · rw [finish, if_neg hn1] at hr
              have hrest : rest.length < k := by
                have heLen := congrArg List.length he
                simp only [List.length_append] at heLen
                omega
              obtain ⟨ts, ht, htenc⟩ :=
                ih rest.length hrest rest rfl (n - 1) (by omega) hr
              refine ⟨leaf s :: ts, ?_, ?_⟩
              · simp only [List.length_cons, ht]
                omega
              · rw [he, htenc]
                simp only [List.flatMap_cons, Elias.encode_leaf, List.cons_append]
  exact aux w.length w rfl n hn h

/-- The streaming recognizer accepts every canonical tree encoding. -/
theorem validBool_encode (t : Tree) : validBool (Elias.encode t) = true := by
  simp only [validBool, scan, foldl_encode t 1 (by decide), finish, ↓reduceIte,
    decide_true]

/-- The streaming recognizer accepts exactly the canonical tree encodings. -/
theorem validBool_iff (w : List Bool) :
    validBool w = true ↔ ∃ t : Tree, Elias.encode t = w := by
  constructor
  · intro h
    have ha : (w.foldl step (.tree, 1)).1 = .done := of_decide_eq_true h
    obtain ⟨ts, ht, he⟩ := forest_of_accept w 1 (by decide) ha
    cases ts with
    | nil => cases ht
    | cons t ts =>
      have hts : ts = [] := List.eq_nil_of_length_eq_zero (by
        simp only [List.length_cons] at ht
        omega)
      subst ts
      exact ⟨t, by simpa only [List.flatMap_cons, List.flatMap_nil, List.append_nil] using
        he.symm⟩
  · rintro ⟨t, rfl⟩
    exact validBool_encode t

/-- Streaming and recursive parsing make the same Boolean decision. -/
theorem validBool_eq (w : List Bool) : validBool w = Elias.validBool w := by
  apply Bool.eq_iff_iff.mpr
  rw [validBool_iff, Elias.validBool_iff]

end Geb.BitTree.Elias.Scanner
