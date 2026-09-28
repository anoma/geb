/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
-- Modified from geb-mathlib by scripts/geb-mathlib-backport.patch.
module

public import Geb.Prototypes.Computability.SizeBounded.Logspace.WTree.NodeExpr
public import Geb.Prototypes.Computability.SizeBounded.Logspace.WTree.ChildExpr
public import Geb.Prototypes.Computability.SizeBounded.Logspace.WTree.Recognize

set_option doc.verso true in
/-!
# The recognizer of the W-trees of a coded signature as a successor-free expression

The recognizer {name}`Geb.SizeBounded.Logspace.WTree.CodedSig.recognize` as an
expression of the logspace subalgebra: the scan over the nodes whose check
at a node is the conjunction of a label check with the scan over the node's
children, each scan the expression of its module, and the label and edge
checks parameters of arity four and six. When the two parameters compute a
coded signature's label and edge conditions, the expression accepts exactly
the words the recognizer accepts, the spellings of the signature's admissible
W-trees. The scans, being simultaneous recursions with a fixed number of
registers each an end segment of the input or a bounded word, are what the
subalgebra's soundness theorem compiles to a logarithmic-space machine.

# Main definitions

* {lit}`checkExpr` — the check at a node: the label check conjoined with the
  scan over the children.
* {lit}`recognizeExpr` — the recognizer.
* {lit}`CodedSig.ComputesLabel`, {lit}`CodedSig.ComputesEdge` — an
  expression computes a signature's label condition, or its edge condition,
  at every sound location of a word.

# Main statements

* {lit}`nodeScan_congr` — scans whose checks agree within the word agree.
* {lit}`checkB_checkExpr` — the check the expression defines is the
  signature's, at the nodes of an encoding.
* {lit}`CodedSig.recognizeExprSem_eq`,
  {lit}`CodedSig.recognizeExprSem_eq_singleton_iff` — the expression's value
  is the recognizer's verdict as a word, and it accepts exactly the words the
  recognizer accepts.
* {lit}`CodedSig.recognizeExprSem_eq_singleton_iff_isW` — the expression
  accepts exactly the spellings of admissible W-trees.

# References

* \[Kristiansen2005\]

# Tags

logspace, simultaneous recursion on notation, W-type, recognizer
-/

set_option doc.verso true

namespace Geb.SizeBounded.Logspace.WTree

open Geb.BitTree.Elias.Scanner (scan)
open Geb.BitTree (Tree)
open Geb.BitTree.Elias (encode)

public section

/-- The check at a node: the label check, read as a flag, conjoined with the
scan over the node's children. -/
@[expose] def checkExpr (label : LOf 4) (edge : LOf 6) : LOf 4 :=
  andOkAt (flagOf label) (ChildExpr.childScanExpr edge)

/-- The recognizer: the scan over the nodes with the check. -/
@[expose] def recognizeExpr (label : LOf 4) (edge : LOf 6) : LOf 1 :=
  NodeExpr.nodeScanExpr (checkExpr label edge)

/-- Scans whose checks agree at every location within the word, at every
count within its length, agree. -/
theorem nodeScan_congr (c₁ c₂ : Loc → ℕ → Bool) (w : List Bool)
    (h : ∀ (l : Loc) (k : ℕ), l.pos ≤ w.length → k ≤ w.length → c₁ l k = c₂ l k) :
    nodeScan c₁ w = nodeScan c₂ w := by
  have key : ∀ (p : List Bool) (s : Ext NodeReg), s.pos + p.length ≤ w.length →
      s.extra.k ≤ s.pos →
      p.foldl (extStep (nodeUpd c₁)) s = p.foldl (extStep (nodeUpd c₂)) s ∧
        (p.foldl (extStep (nodeUpd c₁)) s).extra.k ≤ (p.foldl (extStep (nodeUpd c₁)) s).pos :=
    List.rec (fun s _ hk ↦ ⟨rfl, hk⟩) fun b p ih s hp hk ↦ by
      rw [List.length_cons] at hp
      have hstep : extStep (nodeUpd c₁) s b = extStep (nodeUpd c₂) s b := by
        unfold extStep nodeUpd
        cases hpl : (eventS s.state b).payload with
        | none => rfl
        | some L =>
          simp only
          rw [h ⟨s.pos + 1, L⟩ s.extra.k (by dsimp only; omega) (by omega)]
      have hk' : (extStep (nodeUpd c₁) s b).extra.k ≤ (extStep (nodeUpd c₁) s b).pos := by
        unfold extStep nodeUpd
        dsimp only
        split_ifs <;> omega
      rw [List.foldl_cons, List.foldl_cons, ← hstep]
      exact ih _ (by change s.pos + 1 + p.length ≤ w.length; omega) hk'
  exact (key w ⟨(.tree, 1), 0, ⟨0, true⟩⟩ (by simp) (Nat.le_refl 0)).1

namespace CodedSig

variable {I : Type} [DecidableEq I] (C : CodedSig I)

/-- An expression computes the signature's label condition on a word: at every
sound location, and every count below the word's length, its value at the
word, the remaining word from the location, the word dropped by one more than
the location's length, and the word dropped by the count, read as a flag, is
the condition on the word at the location with the count. The bounds are those
of a node label and its arity in an encoding, {name}`nodes_sound`. -/
@[expose] def ComputesLabel (label : LOf 4) (y : List Bool) : Prop :=
  ∀ (l : Loc) (k : ℕ), Loc.Sound y l → k + 1 ≤ y.length →
    isTrueWord (label.sem ![y, y.drop l.pos, y.drop (l.len + 1), y.drop k]) =
      C.labelSpec (labelAt y l) k

/-- An expression computes the signature's edge condition on a word: at every
two sound locations whose words decode, and every position below the word's
length, its value at the word, the two locations' remaining words and length
counters, and the word dropped by the position, read as a flag, is the
condition on the words at the locations with the position. A location whose
word does not decode fails the label condition, so the edge condition there
does not reach the recognizer's verdict. -/
@[expose] def ComputesEdge (edge : LOf 6) (y : List Bool) : Prop :=
  ∀ (l l' : Loc) (j : ℕ), Loc.Sound y l → Loc.Sound y l' → j + 1 ≤ y.length →
    (C.decode (labelAt y l)).isSome = true → (C.decode (labelAt y l')).isSome = true →
    isTrueWord (edge.sem ![y, y.drop l.pos, y.drop (l.len + 1), y.drop l'.pos,
      y.drop (l'.len + 1), y.drop j]) = C.edgeSpec (labelAt y l) j (labelAt y l')

/-- At a node of an encoding whose label and children's labels decode, the scan
over the children with an expression computing the edge condition accepts
exactly when the scan with the condition does. -/
theorem childScan_ok_edgeB (edge : LOf 6) (t : Tree) (he : C.ComputesEdge edge (encode t))
    (hD : ∀ n ∈ nodes t 0, (C.decode (labelAt (encode t) n.label)).isSome = true) (n : Node)
    (hn : n ∈ nodes t 0) :
    (childScan n.label n.k (ChildExpr.edgeB edge (encode t) n.label) (encode t)).extra.ok =
      (childScan n.label n.k
        (fun l' j ↦ C.edgeSpec (labelAt (encode t) n.label) j (labelAt (encode t) l'))
        (encode t)).extra.ok := by
  obtain ⟨hs, hk, hc⟩ := nodes_sound t n hn
  have key : ∀ (i : ℕ) (h : i < n.k),
      ChildExpr.edgeB edge (encode t) n.label n.children[i] i =
        C.edgeSpec (labelAt (encode t) n.label) i (labelAt (encode t) n.children[i]) := by
    intro i h
    obtain ⟨n', hn', hl⟩ := children_mem_nodes t n hn _ (List.getElem_mem h)
    refine he n.label n.children[i] i hs (hc _ (List.getElem_mem h)) (by omega) (hD n hn) ?_
    rw [← hl]
    exact hD n' hn'
  rw [Bool.eq_iff_iff, childScan_ok_iff _ t n hn, childScan_ok_iff _ t n hn]
  constructor
  · intro h i hi
    rw [← key i hi]
    exact h i hi
  · intro h i hi
    rw [key i hi]
    exact h i hi

/-- At a node of an encoding whose labels decode, the check the expression
defines is the signature's node check. -/
theorem checkB_checkExpr (label : LOf 4) (edge : LOf 6) (t : Tree)
    (hl : C.ComputesLabel label (encode t)) (he : C.ComputesEdge edge (encode t))
    (hD : ∀ n ∈ nodes t 0, (C.decode (labelAt (encode t) n.label)).isSome = true) (n : Node)
    (hn : n ∈ nodes t 0) :
    NodeExpr.checkB (checkExpr label edge) (encode t) n.label n.k =
      C.nodeCheck (encode t) n.label n.k := by
  obtain ⟨hs, hk, _⟩ := nodes_sound t n hn
  unfold NodeExpr.checkB checkExpr nodeCheck
  rw [andOkAt, sem_cond4L, sem_flagOf, sem_constL,
    ChildExpr.childScanExprSem_eq edge _ n.label n.k (by rcases hs.2 with h | h <;> omega)
      (by omega),
    cond4Sem_boolWord, isTrueWord_boolWord, hl n.label n.k hs hk,
    C.childScan_ok_edgeB edge t he hD n hn]

/-- At a node of an encoding whose label does not decode, the check the
expression defines and the signature's node check both fail. -/
theorem checkB_checkExpr_of_none (label : LOf 4) (edge : LOf 6) (t : Tree)
    (hl : C.ComputesLabel label (encode t)) (n : Node) (hn : n ∈ nodes t 0)
    (hD : (C.decode (labelAt (encode t) n.label)).isSome = false) :
    NodeExpr.checkB (checkExpr label edge) (encode t) n.label n.k = false ∧
      C.nodeCheck (encode t) n.label n.k = false := by
  obtain ⟨hs, hk, _⟩ := nodes_sound t n hn
  have hspec : C.labelSpec (labelAt (encode t) n.label) n.k = false := by
    unfold labelSpec
    cases hd : C.decode (labelAt (encode t) n.label)
    · rfl
    · rw [hd] at hD
      cases hD
  unfold NodeExpr.checkB checkExpr nodeCheck
  rw [andOkAt, sem_cond4L, sem_flagOf, sem_constL, hl n.label n.k hs hk, hspec]
  exact ⟨rfl, rfl⟩

/-- A list that does not all satisfy a test has a member failing it. -/
theorem exists_of_all_eq_false {α : Type} (p : α → Bool) : ∀ l : List α, l.all p = false →
    ∃ x ∈ l, p x = false :=
  List.rec (fun h ↦ by cases h) fun a l ih h ↦ by
    rw [List.all_cons] at h
    cases ha : p a with
    | false => exact ⟨a, List.mem_cons_self, ha⟩
    | true =>
      rw [ha, Bool.true_and] at h
      obtain ⟨x, hx, hpx⟩ := ih h
      exact ⟨x, List.mem_cons_of_mem a hx, hpx⟩

/-- The expression's value, when its parameters compute the signature's
conditions on the word: {lit}`[true]` when the recognizer accepts, the empty
word otherwise. -/
theorem recognizeExprSem_eq (label : LOf 4) (edge : LOf 6) (y : List Bool)
    (hl : C.ComputesLabel label y) (he : C.ComputesEdge edge y) :
    (recognizeExpr label edge).sem ![y] = if C.recognize y then [true] else [] := by
  rw [recognizeExpr, NodeExpr.nodeScanExprSem_eq, recognize,
    Geb.BitTree.Elias.Scanner.validBool]
  by_cases hd : (scan y).1 = .done
  · obtain ⟨t, rfl⟩ := (Geb.BitTree.Elias.Scanner.validBool_iff y).mp (decide_eq_true hd)
    have hok : (nodeScan (NodeExpr.checkB (checkExpr label edge) (encode t)) (encode t)).extra.ok =
        (nodeScan (C.nodeCheck (encode t)) (encode t)).extra.ok := by
      rw [Bool.eq_iff_iff, nodeScan_ok_iff _ t, nodeScan_ok_iff _ t]
      cases hD : (nodes t 0).all fun n ↦ (C.decode (labelAt (encode t) n.label)).isSome with
      | true =>
        rw [List.all_eq_true] at hD
        constructor
        · intro h n hn
          rw [← C.checkB_checkExpr label edge t hl he hD n hn]
          exact h n hn
        · intro h n hn
          rw [C.checkB_checkExpr label edge t hl he hD n hn]
          exact h n hn
      | false =>
        obtain ⟨n, hn, hne⟩ := exists_of_all_eq_false _ _ hD
        obtain ⟨h₁, h₂⟩ := C.checkB_checkExpr_of_none label edge t hl n hn hne
        exact ⟨fun h ↦ absurd (h n hn) (by rw [h₁]; decide),
          fun h ↦ absurd (h n hn) (by rw [h₂]; decide)⟩
    rw [hok]
    by_cases ho : (nodeScan (C.nodeCheck (encode t)) (encode t)).extra.ok = true
    · rw [if_pos ⟨hd, ho⟩, decide_eq_true hd, ho]
      rfl
    · rw [if_neg (fun h ↦ ho h.2), decide_eq_true hd, Bool.eq_false_iff.mpr ho]
      rfl
  · rw [if_neg (fun h ↦ hd h.1), decide_eq_false hd]
    rfl

/-- The expression accepts exactly the words the recognizer accepts, when its
parameters compute the signature's conditions on the word. -/
theorem recognizeExprSem_eq_singleton_iff (label : LOf 4) (edge : LOf 6) (y : List Bool)
    (hl : C.ComputesLabel label y) (he : C.ComputesEdge edge y) :
    (recognizeExpr label edge).sem ![y] = [true] ↔ C.recognize y = true := by
  rw [C.recognizeExprSem_eq label edge y hl he]
  cases C.recognize y <;> simp

/-- The expression accepts exactly the spellings of admissible W-trees, when
its parameters compute the signature's conditions on the word. -/
theorem recognizeExprSem_eq_singleton_iff_isW (label : LOf 4) (edge : LOf 6) (y : List Bool)
    (hl : C.ComputesLabel label y) (he : C.ComputesEdge edge y) :
    (recognizeExpr label edge).sem ![y] = [true] ↔ ∃ t, C.P.WValid t ∧ C.spell t = y :=
  (C.recognizeExprSem_eq_singleton_iff label edge y hl he).trans (C.recognize_iff y)

end CodedSig

end

end Geb.SizeBounded.Logspace.WTree
