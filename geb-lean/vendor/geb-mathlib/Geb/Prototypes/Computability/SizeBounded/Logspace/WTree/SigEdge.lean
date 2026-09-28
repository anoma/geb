/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
-- Modified from geb-mathlib by scripts/geb-mathlib-backport.patch.
module

public import Geb.Prototypes.Computability.SizeBounded.Logspace.WTree.SigLabel

set_option doc.verso true in
/-!
# The edge check of the algebra's signature as an expression

The edge condition of the algebra's coded signature,
{name}`Geb.SizeBounded.Logspace.WTree.Sig.sigCoded`, as an expression of
arity six: at the word, a parent label's remaining word and length counter, a
child label's, and the word dropped by the child's position, it decides
whether the child's shape produces the arity the parent's shape requires at
that position, given that both labels decode. The parent's tag selects the
case: a constant, a projection or a successor has no directions; a
substitution requires its second field of its head and its first field of
its arguments; a recursion requires its first field of its bases and one more
than the sum of its two fields of its steps. The child's arity is its first
field, two for a successor, or one more than its first field for a
recursion, so that each comparison is an equality test, a sum check or a
test of the counter for two.

# Main definitions

* {lit}`orF`, {lit}`isTwo`, {lit}`isZero`, {lit}`isOne` — a disjunction and
  the tests of a numeral for two, zero and one.
* {lit}`arityIs`, {lit}`arityIsSum` — the child's arity is the number at a
  pointer, or one more than the sum of the numbers at two pointers.
* {lit}`edgeOk` — the edge check.

# Main statements

* {lit}`computesEdge` — the edge check computes the signature's edge
  condition on every word.

# References

* \[Kristiansen2005\]
* \[Mazzanti2016\]

# Tags

logspace, size-bounded algebra, edge, recognizer
-/

set_option doc.verso true

namespace Geb.SizeBounded.Logspace.WTree.SigEdge

open Numeral NumExpr NumArith NumSum Sig SigLabel
open Geb.SizeBounded (Shape sig)

public section

variable {n : ℕ}

/-- The disjunction of two flags. -/
@[expose] def orF (a b : LOf n) : LOf n := cond4L a b (constL n [true]) (constL n [true])

/-- The disjunction's meaning. -/
theorem sem_orF (a b : LOf n) (x : Fin n → List Bool) (A B : Bool) (ha : a.sem x = boolWord A)
    (hb : b.sem x = boolWord B) : (orF a b).sem x = boolWord (A || B) := by
  rw [orF, sem_cond4L, ha, hb, sem_constL, cond4Sem_boolWord_same]
  cases A <;> cases B <;> rfl

/-- The word. -/
@[expose] def W6 : LOf 6 := projL 6 0

/-- The remaining word from the parent's label. -/
@[expose] def L6 : LOf 6 := projL 6 1

/-- The remaining word from the child's label. -/
@[expose] def C6 : LOf 6 := projL 6 3

/-- The word dropped by the child's position. -/
@[expose] def J6 : LOf 6 := projL 6 5

/-- The first field of a label, past its tag. -/
@[expose] def field1 (p : LOf 6) : LOf 6 := tailAppL (tailAppL (tailAppL p))

/-- The pointer to the parent's first field. -/
@[expose] def pF1 : LOf 6 := field1 L6

/-- The pointer past the parent's first field, to its second. -/
@[expose] def pE1 : LOf 6 := numEndAt W6 pF1

/-- The number at a pointer is two. -/
@[expose] def isTwo (p : LOf 6) : LOf 6 := eqSeg (tailAppL (tailAppL W6)) (natValueAt W6 p)

/-- The number at a pointer is zero. -/
@[expose] def isZero (p : LOf 6) : LOf 6 := isNil (isZeroSeg (natValueAt W6 p) W6)

/-- The number at a pointer is one. -/
@[expose] def isOne (p : LOf 6) : LOf 6 := eqSeg (tailAppL W6) (natValueAt W6 p)

/-- The child's arity is the number at a pointer, given a pointer to a coded
zero: by the child's tag, its first field equals the number, two equals it,
or its first field and zero and one sum to it. -/
@[expose] def arityIs (cL target zero : LOf 6) : LOf 6 :=
  onBitAt cL (constL 6 [])
    (onBitAt (tailAppL cL) (constL 6 []) (constL 6 [])
      (onBitAt (tailAppL (tailAppL cL)) (constL 6 []) (constL 6 [])
        (natSumAt true W6 (field1 cL) zero target)))
    (onBitAt (tailAppL cL) (constL 6 [])
      (onBitAt (tailAppL (tailAppL cL)) (constL 6 []) (natEqAt W6 (field1 cL) target)
        (isTwo target))
      (onBitAt (tailAppL (tailAppL cL)) (constL 6 []) (natEqAt W6 (field1 cL) target)
        (natEqAt W6 (field1 cL) target)))

/-- The child's arity is one more than the sum of the numbers at two pointers:
by the child's tag, the two numbers and one sum to its first field, they sum
to one, or they sum to its first field. -/
@[expose] def arityIsSum (cL pA pB : LOf 6) : LOf 6 :=
  onBitAt cL (constL 6 [])
    (onBitAt (tailAppL cL) (constL 6 []) (constL 6 [])
      (onBitAt (tailAppL (tailAppL cL)) (constL 6 []) (constL 6 [])
        (natSumAt false W6 pA pB (field1 cL))))
    (onBitAt (tailAppL cL) (constL 6 [])
      (onBitAt (tailAppL (tailAppL cL)) (constL 6 []) (natSumAt true W6 pB pA (field1 cL))
        (orF (andF (isZero pA) (isOne pB)) (andF (isOne pA) (isZero pB))))
      (onBitAt (tailAppL (tailAppL cL)) (constL 6 []) (natSumAt true W6 pB pA (field1 cL))
        (natSumAt true W6 pB pA (field1 cL))))

/-- The reading of the parent's second field. -/
@[expose] def V6 : LOf 6 := natValueAt W6 pE1

/-- The edge of a substitution: the position below one more than the second
field, and the child's arity the second field at the head, the first field
otherwise; the parent's tag's second bit is a coded zero. -/
@[expose] def compEdge : LOf 6 :=
  andF (leSeg J6 V6)
    (cond4L (isZeroSeg J6 W6) (arityIs C6 pE1 (tailAppL L6)) (arityIs C6 pF1 (tailAppL L6))
      (arityIs C6 pF1 (tailAppL L6)))

/-- The edge of a recursion: the position below three times the second field,
and the child's arity the first field at a base, one more than the sum of the
two fields at a step; the parent's tag's first bit is a coded zero. -/
@[expose] def srnEdge : LOf 6 :=
  andF (leSeg (tailAppL J6) (addSeg V6 (addSeg V6 V6 W6) W6))
    (cond4L (leSeg (tailAppL J6) V6) (arityIsSum C6 pF1 pE1) (arityIs C6 pF1 L6)
      (arityIs C6 pF1 L6))

/-- The edge check: the dispatch on the parent's tag. -/
@[expose] def edgeOk : LOf 6 :=
  onBitAt L6 (constL 6 [])
    (onBitAt (tailAppL L6) (constL 6 []) (constL 6 [])
      (onBitAt (tailAppL (tailAppL L6)) (constL 6 []) (constL 6 []) srnEdge))
    (onBitAt (tailAppL L6) (constL 6 [])
      (onBitAt (tailAppL (tailAppL L6)) (constL 6 []) compEdge (constL 6 []))
      (onBitAt (tailAppL (tailAppL L6)) (constL 6 []) (constL 6 []) (constL 6 [])))

/-- The environment of the edge check at two labels and a position. -/
@[expose] def envE (y : List Bool) (l l' : Loc) (j : ℕ) : Fin 6 → List Bool :=
  ![y, y.drop l.pos, y.drop (l.len + 1), y.drop l'.pos, y.drop (l'.len + 1), y.drop j]

variable (y : List Bool) (l l' : Loc) (j : ℕ)

/-- The word's meaning. -/
theorem sem_W6 : W6.sem (envE y l l' j) = y := rfl

/-- The parent pointer's meaning. -/
theorem sem_L6 : L6.sem (envE y l l' j) = y.drop l.pos := rfl

/-- The child pointer's meaning. -/
theorem sem_C6 : C6.sem (envE y l l' j) = y.drop l'.pos := rfl

/-- The position's meaning. -/
theorem sem_J6 : J6.sem (envE y l l' j) = y.drop j := rfl

/-- The first field of a pointer to three bits. -/
theorem sem_field1 (p : LOf 6) (x : Fin 6 → List Bool) (pos : ℕ) (hp : p.sem x = y.drop pos) :
    (field1 p).sem x = y.drop (pos + 3) := by
  rw [field1, sem_tailAppL, sem_tailAppL, sem_tailAppL, hp, List.tail_drop, List.tail_drop,
    List.tail_drop]

/-- The count of a substitution's directions. -/
theorem card_comp (m m' : ℕ) : sigCoded.card (.comp m m') = m' + 1 := rfl

/-- The count of a recursion's directions. -/
theorem card_srn (a b : ℕ) (i : Fin b) : sigCoded.card (.srn a b i) = 3 * b := rfl

/-- The first direction of a substitution is its head. -/
theorem dir_comp_zero (m m' : ℕ) (h : 0 < sigCoded.card (.comp m m')) :
    sigCoded.dir (.comp m m') ⟨0, h⟩ = .inl () := rfl

/-- The later directions of a substitution are its arguments. -/
theorem dir_comp_succ (m m' i : ℕ) (h : i + 1 < sigCoded.card (.comp m m')) :
    sigCoded.dir (.comp m m') ⟨i + 1, h⟩ = .inr ⟨i, by change i + 1 < m' + 1 at h; omega⟩ := rfl

/-- The directions of a recursion: the bases, then the steps on either bit. -/
theorem dir_srn (a b : ℕ) (i : Fin b) (k : ℕ) (h : k < sigCoded.card (.srn a b i)) :
    sigCoded.dir (.srn a b i) ⟨k, h⟩ =
      if h1 : k < b then .inl ⟨k, h1⟩
      else if h2 : k < 2 * b then .inr (.inl ⟨k - b, by omega⟩)
      else .inr (.inr ⟨k - 2 * b, by change k < 3 * b at h; omega⟩) := rfl

/-- The arity a substitution requires at a direction. -/
theorem rCurried_comp (m m' : ℕ) (d : Unit ⊕ Fin m') :
    sigCoded.P.rCurried (.comp m m') d = match d with | .inl _ => m' | .inr _ => m := by
  cases d <;> rfl

/-- The arity a recursion requires at a direction. -/
theorem rCurried_srn (a b : ℕ) (i : Fin b) (d : Fin b ⊕ (Fin b ⊕ Fin b)) :
    sigCoded.P.rCurried (.srn a b i) d = match d with | .inl _ => a | .inr _ => b + a + 1 := by
  rcases d with _ | _ <;> rfl

/-- The arity a recursion requires at the direction at a position: its first
field at a base, one more than the sum of its fields at a step. -/
theorem rc_dir_srn (a b : ℕ) (i : Fin b) (k : ℕ) (h : k < sigCoded.card (.srn a b i)) :
    sigCoded.P.rCurried (.srn a b i) (sigCoded.dir (.srn a b i) ⟨k, h⟩) =
      if k < b then a else b + a + 1 := by
  change Geb.SizeBounded.rc (.srn a b i) ((srnEquiv b).symm ⟨k, h⟩) = _
  rw [show (srnEquiv b).symm ⟨k, h⟩ = (if h1 : k < b then .inl ⟨k, h1⟩
    else if h2 : k < 2 * b then .inr (.inl ⟨k - b, by omega⟩)
    else .inr (.inr ⟨k - 2 * b, by change k < 3 * b at h; omega⟩) : Fin b ⊕ (Fin b ⊕ Fin b)) from
    rfl]
  split_ifs <;> rfl


section Semantics

variable (x : Fin 6 → List Bool) (hW : W6.sem x = y) (T tp : ℕ) (uT rT : List Bool)
  (target : LOf 6) (ht : target.sem x = y.drop tp) (huT : uT.length = tp)
  (hT : y = uT ++ natCode T ++ rT)

include hW ht huT hT in
/-- The test for two, at a pointer to a coded number, in a word of three bits
or more. -/
theorem sem_isTwo (h3 : 3 ≤ y.length) : (isTwo target).sem x = boolWord (decide (2 = T)) := by
  rw [isTwo, sem_eqSeg _ _ _ y 2 (min T y.length)
    (by rw [sem_tailAppL, sem_tailAppL, hW, ← List.drop_one (l := y),
      ← List.drop_one (l := y.drop 1), List.drop_drop])
    (by rw [natValueAt_natCode _ y W6 target uT rT T tp hW ht huT hT, drop_min_length])
    (by omega) (Nat.min_le_right _ _)]
  exact boolWord_decide_congr _ _ ⟨fun h ↦ by omega, fun h ↦ by omega⟩

include hW ht huT hT in
/-- The test for zero, at a pointer to a coded number, in a nonempty word. -/
theorem sem_isZero (h1 : 1 ≤ y.length) : (isZero target).sem x = boolWord (decide (T = 0)) := by
  rw [isZero, sem_isNil, sem_isZeroSeg _ _ _ y T (natValueAt_natCode _ y W6 target uT rT T tp hW
    ht huT hT) hW]
  refine boolWord_decide_congr _ _ ?_
  rw [List.drop_eq_nil_iff]
  exact ⟨fun h ↦ by omega, fun h ↦ by omega⟩

include hW ht huT hT in
/-- The test for one, at a pointer to a coded number, in a word of two bits or
more. -/
theorem sem_isOne (h2 : 2 ≤ y.length) : (isOne target).sem x = boolWord (decide (T = 1)) := by
  rw [isOne, sem_eqSeg _ _ _ y 1 (min T y.length)
    (by rw [sem_tailAppL, hW, ← List.drop_one])
    (by rw [natValueAt_natCode _ y W6 target uT rT T tp hW ht huT hT, drop_min_length])
    (by omega) (Nat.min_le_right _ _)]
  exact boolWord_decide_congr _ _ ⟨fun h ↦ by omega, fun h ↦ by omega⟩

/-- A child label's first field, as a coded number at a position of the
word, from its code. -/
theorem child_field (pc : ℕ) (z rc : List Bool) (b0 b1 b2 : Bool)
    (hc : y.drop pc = b0 :: b1 :: b2 :: (z ++ rc)) :
    y.drop (pc + 3) = z ++ rc ∧ pc + 3 ≤ y.length := by
  have hl := congrArg List.length hc
  rw [List.length_drop, List.length_cons, List.length_cons, List.length_cons] at hl
  refine ⟨?_, by omega⟩
  rw [← List.drop_drop, hc]
  rfl

end Semantics

section Arity

variable (x : Fin 6 → List Bool) (hW : W6.sem x = y) (cL target zero : LOf 6) (c : Shape) (pc : ℕ)
  (rc : List Bool) (hcL : cL.sem x = y.drop pc) (hc : y.drop pc = Sig.code c ++ rc) (T tp : ℕ)
  (uT rT : List Bool)
  (ht : target.sem x = y.drop tp) (huT : uT.length = tp) (hT : y = uT ++ natCode T ++ rT)
  (tz : ℕ) (uZ rZ : List Bool) (hz : zero.sem x = y.drop tz) (huZ : uZ.length = tz)
  (hZ : y = uZ ++ natCode 0 ++ rZ)

/-- The dispatch on a child's tag. -/
theorem sem_child_tag (b0 b1 b2 : Bool) (r : List Bool) (h : cL.sem x = b0 :: b1 :: b2 :: r)
    (e0 e1 e2 e3 e4 e5 : LOf 6) :
    (onBitAt cL e0
      (onBitAt (tailAppL cL) e0 e0 (onBitAt (tailAppL (tailAppL cL)) e0 e0 e1))
      (onBitAt (tailAppL cL) e0
        (onBitAt (tailAppL (tailAppL cL)) e0 e2 e3)
        (onBitAt (tailAppL (tailAppL cL)) e0 e4 e5))).sem x =
      (match b0, b1, b2 with
        | true, false, false => e1
        | false, true, true => e2
        | false, true, false => e3
        | false, false, true => e4
        | false, false, false => e5
        | true, _, _ => e0).sem x := by
  have h1 : (tailAppL cL).sem x = b1 :: b2 :: r := by rw [sem_tailAppL, h]; rfl
  have h2 : (tailAppL (tailAppL cL)).sem x = b2 :: r := by rw [sem_tailAppL, sem_tailAppL, h]; rfl
  rw [sem_onBitAt _ _ _ _ _ b0 _ h]
  cases b0
  · rw [if_neg (by decide), sem_onBitAt _ _ _ _ _ b1 _ h1]
    cases b1
    · rw [if_neg (by decide), sem_onBitAt _ _ _ _ _ b2 _ h2]
      cases b2
      · rw [if_neg (by decide)]
      · rw [if_pos rfl]
    · rw [if_pos rfl, sem_onBitAt _ _ _ _ _ b2 _ h2]
      cases b2
      · rw [if_neg (by decide)]
      · rw [if_pos rfl]
  · rw [if_pos rfl, sem_onBitAt _ _ _ _ _ b1 _ h1]
    cases b1
    · rw [if_neg (by decide), sem_onBitAt _ _ _ _ _ b2 _ h2]
      cases b2
      · rw [if_neg (by decide)]
      · rw [if_pos rfl]
    · rw [if_pos rfl]

include hcL hc in
/-- The first field of a child's label, at its position, from its code with
one field. -/
theorem field1_natCode (b0 b1 b2 : Bool) (m : ℕ) (z : List Bool)
    (hcode : Sig.code c ++ rc = b0 :: b1 :: b2 :: (natCode m ++ z)) :
    (field1 cL).sem x = y.drop (pc + 3) ∧
      y = y.take (pc + 3) ++ natCode m ++ z ∧ (y.take (pc + 3)).length = pc + 3 := by
  rw [hcode] at hc
  obtain ⟨hf, h3⟩ := child_field y pc (natCode m) z b0 b1 b2 hc
  obtain ⟨hy, hu⟩ := split_at y (pc + 3) _ (natCode_append_ne_nil m z) hf
  exact ⟨sem_field1 y cL x pc hcL, by rw [List.append_assoc]; exact hy, hu⟩

include hW hcL hc ht huT hT hz huZ hZ in
/-- The child's arity is the number at the pointer. -/
theorem sem_arityIs (h3 : 3 ≤ y.length) :
    (arityIs cL target zero).sem x = boolWord (decide (sigCoded.P.q c = T)) := by
  unfold arityIs
  cases c with
  | const m w =>
    rw [sem_child_tag x cL false false false _ (hcL.trans hc) _ _ _ _ _ _]
    obtain ⟨hf, hy, hu⟩ := field1_natCode y x cL _ pc rc hcL hc
      false false false m (w ++ rc) (by
        simp only [Sig.code, List.cons_append, List.append_assoc])
    exact natEqAt_natCode _ y W6 (field1 cL) target _ _ uT rT m T (pc + 3) tp hW hf ht hu hy huT hT
  | proj m i =>
    rw [sem_child_tag x cL false false true _ (hcL.trans hc) _ _ _ _ _ _]
    obtain ⟨hf, hy, hu⟩ := field1_natCode y x cL _ pc rc hcL hc
      false false true m (natCode i ++ rc) (by
        simp only [Sig.code, List.cons_append, List.append_assoc])
    exact natEqAt_natCode _ y W6 (field1 cL) target _ _ uT rT m T (pc + 3) tp hW hf ht hu hy huT hT
  | sbs b =>
    rw [sem_child_tag x cL false true false _ (hcL.trans hc) _ _ _ _ _ _]
    exact sem_isTwo y x hW T tp uT rT target ht huT hT h3
  | comp m m' =>
    rw [sem_child_tag x cL false true true _ (hcL.trans hc) _ _ _ _ _ _]
    obtain ⟨hf, hy, hu⟩ := field1_natCode y x cL _ pc rc hcL hc
      false true true m (natCode m' ++ rc) (by
        simp only [Sig.code, List.cons_append, List.append_assoc])
    exact natEqAt_natCode _ y W6 (field1 cL) target _ _ uT rT m T (pc + 3) tp hW hf ht hu hy huT hT
  | srn a b i =>
    rw [sem_child_tag x cL true false false _ (hcL.trans hc) _ _ _ _ _ _]
    obtain ⟨hf, hy, hu⟩ := field1_natCode y x cL _ pc rc hcL hc
      true false false a (natCode b ++ natCode i ++ rc) (by
        simp only [Sig.code, List.cons_append, List.append_assoc])
    rw [natSumAt_natCode _ y true W6 (field1 cL) zero target _ _ uZ rZ uT rT a 0 T (pc + 3) tz tp
      hW hf hz ht hu hy huZ hZ huT hT, Bool.toNat_true]
    exact boolWord_decide_congr _ _ ⟨fun h ↦ by change a + 1 = T; omega, fun h ↦ by
      change a + 1 = T at h; omega⟩

end Arity

section AritySum

variable (x : Fin 6 → List Bool) (hW : W6.sem x = y) (cL pA pB : LOf 6) (c : Shape) (pc : ℕ)
  (rc : List Bool) (hcL : cL.sem x = y.drop pc) (hc : y.drop pc = Sig.code c ++ rc) (A B ta tb : ℕ)
  (uA rA uB rB : List Bool) (ha : pA.sem x = y.drop ta) (huA : uA.length = ta)
  (hA : y = uA ++ natCode A ++ rA) (hb : pB.sem x = y.drop tb) (huB : uB.length = tb)
  (hB : y = uB ++ natCode B ++ rB)

include hW hcL hc ha huA hA hb huB hB in
/-- The child's arity is one more than the sum of the numbers at the two
pointers. -/
theorem sem_arityIsSum (h3 : 3 ≤ y.length) :
    (arityIsSum cL pA pB).sem x = boolWord (decide (sigCoded.P.q c = B + A + 1)) := by
  unfold arityIsSum
  cases c with
  | const m w =>
    rw [sem_child_tag x cL false false false _ (hcL.trans hc) _ _ _ _ _ _]
    obtain ⟨hf, hy, hu⟩ := field1_natCode y x cL _ pc rc hcL hc
      false false false m (w ++ rc) (by
        simp only [Sig.code, List.cons_append, List.append_assoc])
    rw [natSumAt_natCode _ y true W6 pB pA (field1 cL) uB rB uA rA _ _ B A m tb ta (pc + 3) hW hb
      ha hf huB hB huA hA hu hy]
    rfl
  | proj m i =>
    rw [sem_child_tag x cL false false true _ (hcL.trans hc) _ _ _ _ _ _]
    obtain ⟨hf, hy, hu⟩ := field1_natCode y x cL _ pc rc hcL hc
      false false true m (natCode i ++ rc) (by
        simp only [Sig.code, List.cons_append, List.append_assoc])
    rw [natSumAt_natCode _ y true W6 pB pA (field1 cL) uB rB uA rA _ _ B A m tb ta (pc + 3) hW hb
      ha hf huB hB huA hA hu hy]
    rfl
  | sbs b =>
    rw [sem_child_tag x cL false true false _ (hcL.trans hc) _ _ _ _ _ _]
    rw [sem_orF _ _ _ _ _
      (sem_andF _ _ _ _ _ (sem_isZero y x hW A ta uA rA pA ha huA hA (by omega))
        (sem_isOne y x hW B tb uB rB pB hb huB hB (by omega)))
      (sem_andF _ _ _ _ _ (sem_isOne y x hW A ta uA rA pA ha huA hA (by omega))
        (sem_isZero y x hW B tb uB rB pB hb huB hB (by omega))),
      ← Bool.decide_and, ← Bool.decide_and, ← Bool.decide_or]
    refine boolWord_decide_congr _ _ ⟨fun h ↦ ?_, fun h ↦ ?_⟩
    · change 2 = B + A + 1
      rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
    · change 2 = B + A + 1 at h
      by_cases hA0 : A = 0
      · exact Or.inl ⟨hA0, by omega⟩
      · exact Or.inr ⟨by omega, by omega⟩
  | comp m m' =>
    rw [sem_child_tag x cL false true true _ (hcL.trans hc) _ _ _ _ _ _]
    obtain ⟨hf, hy, hu⟩ := field1_natCode y x cL _ pc rc hcL hc
      false true true m (natCode m' ++ rc) (by
        simp only [Sig.code, List.cons_append, List.append_assoc])
    rw [natSumAt_natCode _ y true W6 pB pA (field1 cL) uB rB uA rA _ _ B A m tb ta (pc + 3) hW hb
      ha hf huB hB huA hA hu hy]
    rfl
  | srn a b i =>
    rw [sem_child_tag x cL true false false _ (hcL.trans hc) _ _ _ _ _ _]
    obtain ⟨hf, hy, hu⟩ := field1_natCode y x cL _ pc rc hcL hc
      true false false a (natCode b ++ natCode i ++ rc) (by
        simp only [Sig.code, List.cons_append, List.append_assoc])
    rw [natSumAt_natCode _ y false W6 pA pB (field1 cL) uA rA uB rB _ _ A B a ta tb (pc + 3) hW
      ha hb hf huA hA huB hB hu hy, Bool.toNat_false]
    exact boolWord_decide_congr _ _ ⟨fun h ↦ by change a + 1 = B + A + 1; omega, fun h ↦ by
      change a + 1 = B + A + 1 at h; omega⟩

end AritySum


section Main

variable (l l' : Loc) (j : ℕ)

/-- The environment's word. -/
theorem sem_W6' : W6.sem (envE y l l' j) = y := rfl

/-- The parent's remaining word, from its label's code. -/
theorem parent_code (a : Shape) (ha : labelAt y l = sigCoded.code a) :
    y.drop l.pos = Sig.code a ++ y.drop (l.pos + l.len) := by
  rw [← label_append y l, ha]
  rfl

/-- The edge condition of a shape with no directions is false. -/
theorem edgeSpec_none (a c : Shape) (h : sigCoded.card a = 0) :
    (if h : j < sigCoded.card a then
      decide (sigCoded.P.q c = sigCoded.P.rCurried a (sigCoded.dir a ⟨j, h⟩)) else false) = false :=
  dif_neg (by rw [h]; exact Nat.not_lt_zero j)

/-- The word dropped by the position, and by one more, as end segments within
the word. -/
theorem sem_J6_tail : (tailAppL J6).sem (envE y l l' j) = y.drop (j + 1) := by
  rw [sem_tailAppL, sem_J6, List.tail_drop]

/-- The edge check computes the signature's edge condition on every word. -/
theorem computesEdge : sigCoded.ComputesEdge edgeOk y := by
  intro l l' j hs hs' hj hd hd'
  obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp hd
  obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp hd'
  have hla : labelAt y l = sigCoded.code a := (sigCoded.code_of_decode ha).symm
  have hlc : labelAt y l' = sigCoded.code c := (sigCoded.code_of_decode hc).symm
  change isTrueWord (edgeOk.sem (envE y l l' j)) = sigCoded.edgeSpec (labelAt y l) j (labelAt y l')
  have hpa := parent_code y l a hla
  have hpc := parent_code y l' c hlc
  have hlen := lend_le y l hs
  have h3 : 3 ≤ y.length := by
    have h4 := four_le_length_code a
    have hl := length_label y l hs
    rw [hla] at hl
    change (Sig.code a).length = l.len at hl
    omega
  unfold CodedSig.edgeSpec
  rw [ha, hc]
  dsimp only
  rw [edgeOk]
  cases a with
  | const m w =>
    rw [sem_child_tag (envE y l l' j) L6 false false false _ ((sem_L6 y l l' j).trans hpa)
      _ _ _ _ _ _, sem_constL,
      edgeSpec_none j _ c rfl]
    rfl
  | proj m i =>
    rw [sem_child_tag (envE y l l' j) L6 false false true _ ((sem_L6 y l l' j).trans hpa)
      _ _ _ _ _ _, sem_constL,
      edgeSpec_none j _ c rfl]
    rfl
  | sbs b =>
    rw [sem_child_tag (envE y l l' j) L6 false true false _ ((sem_L6 y l l' j).trans hpa)
      _ _ _ _ _ _, sem_constL,
      edgeSpec_none j _ c rfl]
    rfl
  | comp m m' =>
    rw [sem_child_tag (envE y l l' j) L6 false true true _ ((sem_L6 y l l' j).trans hpa)
      _ _ _ _ _ _]
    dsimp only
    -- the parent's fields
    obtain ⟨hf, hpf⟩ := child_field y l.pos (natCode m ++ natCode m') (y.drop (l.pos + l.len))
      false true true (by rw [hpa]; simp only [Sig.code, List.cons_append, List.append_assoc])
    rw [List.append_assoc] at hf
    obtain ⟨hy1, hu1⟩ := split_at y (l.pos + 3) _ (natCode_append_ne_nil m _) hf
    have hF1 : pF1.sem (envE y l l' j) = y.drop (l.pos + 3) := sem_field1 y L6 _ l.pos rfl
    have hE1 : pE1.sem (envE y l l' j) = y.drop (l.pos + 3 + (natCode m).length) :=
      (numOkAt_natCode _ y W6 pF1 _ _ m (l.pos + 3) rfl hF1 hu1
        (by rw [List.append_assoc]; exact hy1)).2
    have hf2 : y.drop (l.pos + 3 + (natCode m).length) = natCode m' ++ y.drop (l.pos + l.len) := by
      rw [← List.drop_drop, hf, List.drop_left]
    obtain ⟨hy2, hu2⟩ := split_at y _ _ (natCode_append_ne_nil m' _) hf2
    have hV : V6.sem (envE y l l' j) = y.drop m' :=
      natValueAt_natCode _ y W6 pE1 _ _ m' _ rfl hE1 hu2 (by rw [List.append_assoc]; exact hy2)
    -- the zero at the tag's second bit
    have hz : (tailAppL L6).sem (envE y l l' j) = y.drop (l.pos + 1) := by
      rw [sem_tailAppL, sem_L6, List.tail_drop]
    have hz0 : y.drop (l.pos + 1) = natCode 0 ++ (true :: (natCode m ++ natCode m' ++
        y.drop (l.pos + l.len))) := by
      rw [← List.drop_drop, hpa]
      simp only [Sig.code, List.cons_append, List.append_assoc]
      rfl
    obtain ⟨hyz, huz⟩ := split_at y (l.pos + 1) _ (natCode_append_ne_nil 0 _) hz0
    have hzc : y = y.take (l.pos + 1) ++ natCode 0 ++
        (true :: (natCode m ++ natCode m' ++ y.drop (l.pos + l.len))) := by
      rw [List.append_assoc]
      exact hyz
    rw [Bool.eq_iff_iff, compEdge, isTrueWord_andF_iff _ _ _ _
      (sem_leSeg J6 V6 _ y j (min m' y.length) (sem_J6 y l l' j) (by rw [hV, drop_min_length])),
      sem_cond4L, sem_isZeroSeg J6 W6 _ y j (sem_J6 y l l' j) rfl,
      cond4Sem_drop_length_sub y j (by omega)]
    cases j with
    | zero =>
      rw [if_pos rfl, sem_arityIs y _ rfl C6 pE1 (tailAppL L6) c l'.pos _ (sem_C6 y l l' 0) hpc
        m' _ _ _ hE1 hu2 (by rw [List.append_assoc]; exact hy2) _ _ _ hz huz hzc h3,
        isTrueWord_boolWord,
        dif_pos (show 0 < sigCoded.card (.comp m m') from Nat.succ_pos m'), dir_comp_zero,
        rCurried_comp]
      simp only [decide_eq_true_eq]
      exact ⟨fun h ↦ h.2, fun h ↦ ⟨by omega, h⟩⟩
    | succ i =>
      rw [if_neg (Nat.succ_ne_zero i), sem_arityIs y _ rfl C6 pF1 (tailAppL L6) c l'.pos _
        (sem_C6 y l l' (i + 1)) hpc m _ _ _ hF1 hu1 (by rw [List.append_assoc]; exact hy1) _ _ _
        hz huz hzc h3, isTrueWord_boolWord]
      by_cases hlt : i + 1 < m' + 1
      · rw [dif_pos (show i + 1 < sigCoded.card (.comp m m') from hlt), dir_comp_succ,
          rCurried_comp]
        simp only [decide_eq_true_eq]
        exact ⟨fun h ↦ h.2, fun h ↦ ⟨by omega, h⟩⟩
      · rw [dif_neg (show ¬i + 1 < sigCoded.card (.comp m m') from hlt)]
        simp only [decide_eq_true_eq]
        exact ⟨fun h ↦ absurd h.1 (by omega), fun h ↦ absurd h (by decide)⟩
  | srn a b i0 =>
    rw [sem_child_tag (envE y l l' j) L6 true false false _ ((sem_L6 y l l' j).trans hpa)
      _ _ _ _ _ _]
    dsimp only
    obtain ⟨hf, hpf⟩ := child_field y l.pos (natCode a ++ natCode b ++ natCode i0)
      (y.drop (l.pos + l.len)) true false false
      (by rw [hpa]; simp only [Sig.code, List.cons_append, List.append_assoc])
    rw [List.append_assoc, List.append_assoc] at hf
    obtain ⟨hy1, hu1⟩ := split_at y (l.pos + 3) _ (natCode_append_ne_nil a _) hf
    have hF1 : pF1.sem (envE y l l' j) = y.drop (l.pos + 3) := sem_field1 y L6 _ l.pos rfl
    have hE1 : pE1.sem (envE y l l' j) = y.drop (l.pos + 3 + (natCode a).length) :=
      (numOkAt_natCode _ y W6 pF1 _ _ a (l.pos + 3) rfl hF1 hu1
        (by rw [List.append_assoc]; exact hy1)).2
    have hf2 : y.drop (l.pos + 3 + (natCode a).length) =
        natCode b ++ (natCode i0 ++ y.drop (l.pos + l.len)) := by
      rw [← List.drop_drop, hf, List.drop_left]
    obtain ⟨hy2, hu2⟩ := split_at y _ _ (natCode_append_ne_nil b _) hf2
    have hV : V6.sem (envE y l l' j) = y.drop b :=
      natValueAt_natCode _ y W6 pE1 _ _ b _ rfl hE1 hu2 (by rw [List.append_assoc]; exact hy2)
    -- the zero at the tag's first bit
    have hz0 : y.drop l.pos = natCode 0 ++ (false :: false :: (natCode a ++ natCode b ++
        natCode i0 ++ y.drop (l.pos + l.len))) := by
      rw [hpa]
      simp only [Sig.code, List.cons_append, List.append_assoc]
      rfl
    obtain ⟨hyz, huz⟩ := split_at y l.pos _ (natCode_append_ne_nil 0 _) hz0
    have hzc : y = y.take l.pos ++ natCode 0 ++
        (false :: false :: (natCode a ++ natCode b ++ natCode i0 ++ y.drop (l.pos + l.len))) := by
      rw [List.append_assoc]
      exact hyz
    have hT : (addSeg V6 (addSeg V6 V6 W6) W6).sem (envE y l l' j) = y.drop (b + b + b) :=
      sem_addSeg V6 _ W6 _ y b (b + b) hV (sem_addSeg V6 V6 W6 _ y b b hV hV rfl) rfl
    rw [Bool.eq_iff_iff, srnEdge, isTrueWord_andF_iff _ _ _ _
      (sem_leSeg _ _ _ y (j + 1) (min (b + b + b) y.length) (sem_J6_tail y l l' j)
        (by rw [hT, drop_min_length])),
      sem_cond4L, sem_leSeg _ _ _ y (j + 1) (min b y.length) (sem_J6_tail y l l' j)
        (by rw [hV, drop_min_length]), cond4Sem_boolWord_same]
    by_cases hjb : j < b
    · rw [if_pos (decide_eq_true (by omega)), sem_arityIs y _ rfl C6 pF1 L6 c l'.pos _
        (sem_C6 y l l' j) hpc a _ _ _ hF1 hu1 (by rw [List.append_assoc]; exact hy1) _ _ _
        (sem_L6 y l l' j) huz hzc h3, isTrueWord_boolWord,
        dif_pos (show j < sigCoded.card (.srn a b i0) by change j < 3 * b; omega), rc_dir_srn,
        if_pos hjb]
      simp only [decide_eq_true_eq]
      exact ⟨fun h ↦ h.2, fun h ↦ ⟨by omega, h⟩⟩
    · rw [if_neg (by rw [decide_eq_true_eq]; omega), sem_arityIsSum y _ rfl C6 pF1 pE1 c
        l'.pos _ (sem_C6 y l l' j) hpc a b (l.pos + 3) _ _ _ _ _ hF1 hu1
        (by rw [List.append_assoc]; exact hy1) hE1 hu2 (by rw [List.append_assoc]; exact hy2) h3,
        isTrueWord_boolWord]
      by_cases h3b : j < 3 * b
      · rw [dif_pos (show j < sigCoded.card (.srn a b i0) from h3b), rc_dir_srn,
          if_neg hjb]
        simp only [decide_eq_true_eq]
        exact ⟨fun h ↦ h.2, fun h ↦ ⟨by omega, h⟩⟩
      · rw [dif_neg (show ¬j < sigCoded.card (.srn a b i0) from h3b)]
        simp only [decide_eq_true_eq]
        exact ⟨fun h ↦ absurd h.1 (by omega), fun h ↦ absurd h (by decide)⟩

end Main

end

end Geb.SizeBounded.Logspace.WTree.SigEdge
