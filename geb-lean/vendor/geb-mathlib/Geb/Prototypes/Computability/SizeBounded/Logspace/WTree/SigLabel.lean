/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
-- Modified from geb-mathlib by scripts/geb-mathlib-backport.patch.
module

public import Geb.Prototypes.Computability.SizeBounded.Logspace.WTree.Sig
public import Geb.Prototypes.Computability.SizeBounded.Logspace.WTree.NumSum
public import Geb.Prototypes.Computability.SizeBounded.Logspace.WTree.RecognizeExpr

set_option doc.verso true in
/-!
# The label check of the algebra's signature as an expression

The label condition of the algebra's coded signature,
{name}`Geb.SizeBounded.Logspace.WTree.Sig.sigCoded`, as an expression of
arity four: at the word, the remaining word from a label, the word dropped by
one more than the label's length, and the word dropped by a node's arity, it
decides whether the label is the code of a shape with that arity. The tag is
read off the first three bits, the numeric fields are scanned by
{name}`Geb.SizeBounded.Logspace.WTree.NumExpr.numOk` from successive
positions, the last field's end is compared with the label's end, the
constraints of a projection and a recursion are decided by
{name}`Geb.SizeBounded.Logspace.WTree.NumArith.natLt`, and the arity is
compared with a field read into a counter by
{name}`Geb.SizeBounded.Logspace.WTree.NumArith.natValue`. The comparisons
with the label's end are exact at sound locations,
{name}`Geb.SizeBounded.Logspace.WTree.Loc.Sound`, which every node label of
an encoding is.

# Main definitions

* {lit}`isNil`, {lit}`notNil`, {lit}`andF`, {lit}`leSeg` — flags and the
  order of counters.
* {lit}`endsAt`, {lit}`within` — a pointer ending at the label's end, and
  within it.
* {lit}`numOkAt`, {lit}`numEndAt`, {lit}`natLtAt`, {lit}`natEqAt`,
  {lit}`natValueAt`, {lit}`natSumAt` — the numeral operations at pointers.
* {lit}`labelOk` — the label check.

# Main statements

* {lit}`computesLabel` — the label check computes the signature's label
  condition on every word.

# References

* \[Kristiansen2005\]
* \[Mazzanti2016\]

# Tags

logspace, size-bounded algebra, label, recognizer
-/

set_option doc.verso true

namespace Geb.SizeBounded.Logspace.WTree.SigLabel

open Numeral NumExpr NumArith NumSum Sig
open Geb.SizeBounded (Shape sig)

public section

variable {n : ℕ}

/-- A flag decided by a proposition. -/
theorem boolWord_decide (P : Prop) [Decidable P] :
    boolWord (decide P) = if P then [true] else [] := by
  by_cases h : P
  · rw [decide_eq_true h, if_pos h]
    rfl
  · rw [decide_eq_false h, if_neg h]
    rfl

/-- Flags decided by equivalent propositions agree. -/
theorem boolWord_decide_congr (P Q : Prop) [Decidable P] [Decidable Q] (h : P ↔ Q) :
    boolWord (decide P) = boolWord (decide Q) := by
  rw [boolWord_decide, boolWord_decide]
  by_cases hp : P
  · rw [if_pos hp, if_pos (h.mp hp)]
  · rw [if_neg hp, if_neg (fun hq ↦ hp (h.mpr hq))]

/-- The emptiness of a word, as a flag. -/
@[expose] def isNil (e : LOf n) : LOf n := cond4L e (constL n [true]) (constL n []) (constL n [])

/-- The emptiness test's meaning. -/
theorem sem_isNil (e : LOf n) (x : Fin n → List Bool) :
    (isNil e).sem x = boolWord (decide (e.sem x = [])) := by
  rw [isNil, sem_cond4L, sem_constL, sem_constL, EliasTree.cond4Sem_same, boolWord_decide]

/-- The nonemptiness of a word, as a flag. -/
@[expose] def notNil (e : LOf n) : LOf n :=
  cond4L e (constL n []) (constL n [true]) (constL n [true])

/-- The nonemptiness test's meaning. -/
theorem sem_notNil (e : LOf n) (x : Fin n → List Bool) :
    (notNil e).sem x = boolWord (decide (e.sem x ≠ [])) := by
  rw [notNil, sem_cond4L, sem_constL, sem_constL, EliasTree.cond4Sem_same, boolWord_decide]
  by_cases h : e.sem x = []
  · rw [if_pos h, if_neg (fun h' ↦ h' h)]
  · rw [if_neg h, if_pos h]

/-- The conjunction of two flags. -/
@[expose] def andF (a b : LOf n) : LOf n := andOkAt a b

/-- The conjunction's meaning. -/
theorem sem_andF (a b : LOf n) (x : Fin n → List Bool) (A B : Bool) (ha : a.sem x = boolWord A)
    (hb : b.sem x = boolWord B) : (andF a b).sem x = boolWord (A && B) := by
  rw [andF, andOkAt, sem_cond4L, ha, hb, sem_constL, cond4Sem_boolWord]

/-- The order of two counters held as end segments of the word: the first, cut
off at the word's length, is at most the second. -/
@[expose] def leSeg (a b : LOf n) : LOf n := isNil (dropByApp a b)

/-- The order test's meaning. -/
theorem sem_leSeg (a b : LOf n) (x : Fin n → List Bool) (y : List Bool) (A B : ℕ)
    (ha : a.sem x = y.drop A) (hb : b.sem x = y.drop B) :
    (leSeg a b).sem x = boolWord (decide (min A y.length ≤ B)) := by
  rw [leSeg, sem_isNil, sem_dropByApp, ha, hb, List.length_drop, List.drop_drop]
  refine boolWord_decide_congr _ _ ?_
  rw [List.drop_eq_nil_iff]
  constructor
  · intro h
    omega
  · intro h
    omega

/-- The pointer one past a label's end, from the pointer to the label and the
counter one more than its length. -/
@[expose] def pastEnd (W L Q : LOf n) : LOf n := dropByApp (dropByApp Q W) L

/-- The pointer's meaning. -/
theorem sem_pastEnd (W L Q : LOf n) (x : Fin n → List Bool) (y : List Bool) (pos len : ℕ)
    (hW : W.sem x = y) (hL : L.sem x = y.drop pos) (hQ : Q.sem x = y.drop (len + 1)) :
    (pastEnd W L Q).sem x = y.drop (pos + len + 1) := by
  rw [pastEnd, sem_dropByApp, sem_dropByApp, hQ, hW, hL, List.length_drop, List.length_drop,
    show y.length - (y.length - (len + 1)) = min (len + 1) y.length by omega, List.drop_drop,
    drop_add_min, Nat.add_assoc]

/-- A pointer, held as an end segment, ends at the label's end, given the
pointer one past that end: when the word ends there, the pointer is empty;
otherwise the pointer's tail is the given one. -/
@[expose] def endsAt (E R : LOf n) : LOf n :=
  cond4L R (isNil E) (eqSeg (tailAppL E) R) (eqSeg (tailAppL E) R)

/-- The tail of an end segment is the end segment one further, cut off at the
word's length. -/
theorem tail_drop_min (y : List Bool) (e : ℕ) :
    (y.drop e).tail = y.drop (min (e + 1) y.length) := by
  rw [List.tail_drop, drop_min_length]

/-- The end test's meaning at a sound label. -/
theorem sem_endsAt (E R : LOf n) (x : Fin n → List Bool) (y : List Bool) (e Lend : ℕ)
    (hE : E.sem x = y.drop e) (he : e ≤ y.length) (hR : R.sem x = y.drop (Lend + 1))
    (hs : Lend + 2 ≤ y.length ∨ Lend = y.length) :
    (endsAt E R).sem x = boolWord (decide (e = Lend)) := by
  rw [endsAt, sem_cond4L, hR, EliasTree.cond4Sem_same]
  rcases hs with hs | hs
  · rw [if_neg (by rw [List.drop_eq_nil_iff]; omega),
      sem_eqSeg _ _ x y (min (e + 1) y.length) (Lend + 1)
        (by rw [sem_tailAppL, hE, tail_drop_min]) hR (Nat.min_le_right _ _) (by omega)]
    refine boolWord_decide_congr _ _ ⟨fun h ↦ by omega, fun h ↦ by omega⟩
  · rw [if_pos (by rw [List.drop_eq_nil_iff]; omega), sem_isNil, hE]
    refine boolWord_decide_congr _ _ ?_
    rw [List.drop_eq_nil_iff]
    exact ⟨fun h ↦ by omega, fun h ↦ by omega⟩

/-- A pointer, held as an end segment, lies within the label, given the pointer
one past the label's end. -/
@[expose] def within (E R : LOf n) : LOf n :=
  cond4L R (constL n [true]) (leSeg (tailAppL E) R) (leSeg (tailAppL E) R)

/-- The containment test's meaning at a sound label. -/
theorem sem_within (E R : LOf n) (x : Fin n → List Bool) (y : List Bool) (e Lend : ℕ)
    (hE : E.sem x = y.drop e) (he : e ≤ y.length) (hR : R.sem x = y.drop (Lend + 1))
    (hs : Lend + 2 ≤ y.length ∨ Lend = y.length) :
    (within E R).sem x = boolWord (decide (e ≤ Lend)) := by
  rw [within, sem_cond4L, hR, EliasTree.cond4Sem_same]
  rcases hs with hs | hs
  · rw [if_neg (by rw [List.drop_eq_nil_iff]; omega),
      sem_leSeg _ _ x y (min (e + 1) y.length) (Lend + 1)
        (by rw [sem_tailAppL, hE, tail_drop_min]) hR]
    refine boolWord_decide_congr _ _ ⟨fun h ↦ by omega, fun h ↦ by omega⟩
  · rw [if_pos (by rw [List.drop_eq_nil_iff]; omega), sem_constL,
      show [true] = boolWord (decide (e ≤ Lend)) by rw [decide_eq_true (by omega)]; rfl]

/-- The acceptance of the numeral scanner at a pointer. -/
@[expose] def numOkAt (W p : LOf n) : LOf n := compL numOk ![W, p, W]

/-- The end position of the numeral scanner at a pointer. -/
@[expose] def numEndAt (W p : LOf n) : LOf n := compL numEnd ![W, p, W]

/-- The order test of the numerals at two pointers. -/
@[expose] def natLtAt (W p q : LOf n) : LOf n := compL natLt ![W, p, q, W]

/-- The equality test of the numerals at two pointers. -/
@[expose] def natEqAt (W p q : LOf n) : LOf n := compL natEq ![W, p, q, W]

/-- The reading of the numeral at a pointer into a counter. -/
@[expose] def natValueAt (W p : LOf n) : LOf n := compL natValue ![W, p, W, W]

/-- The sum check of the numerals at three pointers. -/
@[expose] def natSumAt (cin : Bool) (W p q r : LOf n) : LOf n := compL (natSum cin) ![W, p, q, r]

variable (x : Fin n → List Bool) (y : List Bool)

/-- The environment of a numeral operation on the word and a pointer. -/
theorem env3 (W p : LOf n) (tp : ℕ) (hW : W.sem x = y) (hp : p.sem x = y.drop tp) :
    (fun i ↦ (![W, p, W] i).sem x) = ![y, y.drop tp, y.drop 0] :=
  funext fun i ↦ match i with
    | 0 => hW
    | 1 => hp
    | 2 => by rw [List.drop_zero]; exact hW

/-- The environment of a numeral operation on the word and three pointers. -/
theorem env4 (W p q r : LOf n) (tp tq tr : ℕ) (hW : W.sem x = y) (hp : p.sem x = y.drop tp)
    (hq : q.sem x = y.drop tq) (hr : r.sem x = y.drop tr) :
    (fun i ↦ (![W, p, q, r] i).sem x) = ![y, y.drop tp, y.drop tq, y.drop tr] :=
  funext fun i ↦ match i with
    | 0 => hW
    | 1 => hp
    | 2 => hq
    | 3 => hr

/-- The acceptance and the end at a pointer to a coded number. -/
theorem numOkAt_natCode (W p : LOf n) (u rest : List Bool) (m tp : ℕ) (hW : W.sem x = y)
    (hp : p.sem x = y.drop tp) (hu : u.length = tp) (hy : y = u ++ natCode m ++ rest) :
    (numOkAt W p).sem x = [true] ∧ (numEndAt W p).sem x = y.drop (tp + (natCode m).length) := by
  rw [numOkAt, numEndAt, sem_compL, sem_compL, env3 x y W p tp hW hp]
  obtain ⟨h1, h2, _⟩ := num_natCode u rest y m tp 0 hu hy (Nat.zero_le _)
  exact ⟨h1, h2⟩

/-- A coded number at a pointer where the scanner accepts, with the end. -/
theorem numOkAt_eq (W p : LOf n) (tp : ℕ) (hW : W.sem x = y) (hp : p.sem x = y.drop tp)
    (htp : tp ≤ y.length) (h : (numOkAt W p).sem x = [true]) :
    ∃ m rest, y.drop tp = natCode m ++ rest ∧
      (numEndAt W p).sem x = y.drop (tp + (natCode m).length) := by
  rw [numOkAt, sem_compL, env3 x y W p tp hW hp] at h
  rw [numEndAt, sem_compL, env3 x y W p tp hW hp]
  obtain ⟨m, rest, h1, h2, _⟩ := num_of_ok y tp 0 htp (Nat.zero_le _) h
  exact ⟨m, rest, h1, h2⟩

/-- The order test at pointers to coded numbers. -/
theorem natLtAt_natCode (W p q : LOf n) (uA rA uB rB : List Bool) (A B pA pB : ℕ)
    (hW : W.sem x = y) (hp : p.sem x = y.drop pA) (hq : q.sem x = y.drop pB) (huA : uA.length = pA)
    (hyA : y = uA ++ natCode A ++ rA) (huB : uB.length = pB) (hyB : y = uB ++ natCode B ++ rB) :
    (natLtAt W p q).sem x = boolWord (decide (A < B)) := by
  rw [natLtAt, sem_compL, env4 x y W p q W pA pB 0 hW hp hq (by rw [List.drop_zero]; exact hW)]
  exact natLt_natCode y uA rA uB rB A B pA pB 0 huA hyA huB hyB (Nat.zero_le _)

/-- The equality test at pointers to coded numbers. -/
theorem natEqAt_natCode (W p q : LOf n) (uA rA uB rB : List Bool) (A B pA pB : ℕ)
    (hW : W.sem x = y) (hp : p.sem x = y.drop pA) (hq : q.sem x = y.drop pB) (huA : uA.length = pA)
    (hyA : y = uA ++ natCode A ++ rA) (huB : uB.length = pB) (hyB : y = uB ++ natCode B ++ rB) :
    (natEqAt W p q).sem x = boolWord (decide (A = B)) := by
  rw [natEqAt, sem_compL, env4 x y W p q W pA pB 0 hW hp hq (by rw [List.drop_zero]; exact hW)]
  exact natEq_natCode y uA rA uB rB A B pA pB 0 huA hyA huB hyB (Nat.zero_le _)

/-- The reading at a pointer to a coded number. -/
theorem natValueAt_natCode (W p : LOf n) (uA rA : List Bool) (A pA : ℕ) (hW : W.sem x = y)
    (hp : p.sem x = y.drop pA) (huA : uA.length = pA) (hyA : y = uA ++ natCode A ++ rA) :
    (natValueAt W p).sem x = y.drop A := by
  rw [natValueAt, sem_compL, env4 x y W p W W pA 0 0 hW hp (by rw [List.drop_zero]; exact hW)
    (by rw [List.drop_zero]; exact hW)]
  exact natValue_natCode y uA rA A pA 0 0 huA hyA (Nat.zero_le _) (Nat.zero_le _)

/-- The sum check at pointers to coded numbers. -/
theorem natSumAt_natCode (cin : Bool) (W p q r : LOf n) (uA rA uB rB uC rC : List Bool)
    (A B C pA pB pC : ℕ) (hW : W.sem x = y) (hp : p.sem x = y.drop pA) (hq : q.sem x = y.drop pB)
    (hr : r.sem x = y.drop pC) (huA : uA.length = pA) (hyA : y = uA ++ natCode A ++ rA)
    (huB : uB.length = pB) (hyB : y = uB ++ natCode B ++ rB) (huC : uC.length = pC)
    (hyC : y = uC ++ natCode C ++ rC) :
    (natSumAt cin W p q r).sem x = boolWord (decide (C = A + B + cin.toNat)) := by
  rw [natSumAt, sem_compL, env4 x y W p q r pA pB pC hW hp hq hr]
  exact natSum_natCode y uA rA uB rB uC rC A B C pA pB pC cin huA hyA huB hyB huC hyC

/-- The scanner's end position lies within the word. -/
theorem nrunFrom_endPos_le (m tp i : ℕ) (v : List Bool) : ∀ (x : NState) (pos : ℕ),
    x.endPos ≤ pos → (nrunFrom m tp i x pos v).1.endPos ≤ pos + v.length :=
  List.rec (fun x pos h ↦ by rw [nrunFrom]; exact h) (fun b v ih x pos h ↦ by
    rw [nrunFrom_cons, List.length_cons, show pos + (v.length + 1) = pos + 1 + v.length by omega]
    refine ih _ (pos + 1) ?_
    unfold nstep
    cases x.mode <;> dsimp only <;> (try split_ifs) <;> (try cases b) <;> (try dsimp only) <;>
      omega) v

/-- The scanner's end position lies within the word. -/
theorem nrun_endPos_le (tp i : ℕ) (y : List Bool) : (nrun tp i y).endPos ≤ y.length := by
  have := nrunFrom_endPos_le y.length tp i y nstart 0 (Nat.le_refl 0)
  rwa [Nat.zero_add] at this

/-- The scanner's acceptance at a position, as a flag. -/
@[expose] def nrunOk (y : List Bool) (tp : ℕ) : Bool :=
  decide ((nrun tp 0 y).mode = .done) && (nrun tp 0 y).ok

/-- The acceptance at a pointer, as a flag. -/
theorem sem_numOkAt (W p : LOf n) (tp : ℕ) (hW : W.sem x = y) (hp : p.sem x = y.drop tp)
    (htp : tp ≤ y.length) : (numOkAt W p).sem x = boolWord (nrunOk y tp) := by
  rw [numOkAt, sem_compL, env3 x y W p tp hW hp, sem_numOk y tp 0 htp (Nat.zero_le _)]
  rfl

/-- The end at a pointer, as an end segment within the word. -/
theorem sem_numEndAt (W p : LOf n) (tp : ℕ) (hW : W.sem x = y) (hp : p.sem x = y.drop tp)
    (htp : tp ≤ y.length) : (numEndAt W p).sem x = y.drop (nrun tp 0 y).endPos := by
  rw [numEndAt, sem_compL, env3 x y W p tp hW hp, sem_numEnd y tp 0 htp (Nat.zero_le _)]

/-- The label condition holds exactly when the word is the code of a shape
with the count as its number of directions. -/
theorem labelSpec_eq_true_iff {I : Type} (C : CodedSig I) (s : List Bool) (k : ℕ) :
    C.labelSpec s k = true ↔ ∃ a, s = C.code a ∧ C.card a = k := by
  unfold CodedSig.labelSpec
  cases hd : C.decode s with
  | none =>
    refine ⟨fun h ↦ (nomatch h), fun h ↦ ?_⟩
    obtain ⟨a, hs, _⟩ := h
    rw [hs, C.decode_code] at hd
    cases hd
  | some a =>
    rw [decide_eq_true_eq]
    refine ⟨fun h ↦ ⟨a, (C.code_of_decode hd).symm, h⟩, fun h ↦ ?_⟩
    obtain ⟨a', hs, hk⟩ := h
    rw [hs, C.decode_code] at hd
    obtain rfl := Option.some.inj hd
    exact hk

section Label

/-- The word. -/
@[expose] def W4 : LOf 4 := projL 4 0

/-- The remaining word from the label. -/
@[expose] def L4 : LOf 4 := projL 4 1

/-- The word dropped by one more than the label's length. -/
@[expose] def Q4 : LOf 4 := projL 4 2

/-- The word dropped by the arity. -/
@[expose] def K4 : LOf 4 := projL 4 3

/-- The pointer one past the label's end. -/
@[expose] def R4 : LOf 4 := pastEnd W4 L4 Q4

/-- The pointer to the first field, past the tag. -/
@[expose] def F1 : LOf 4 := tailAppL (tailAppL (tailAppL L4))

/-- The pointer past the first field. -/
@[expose] def E1 : LOf 4 := numEndAt W4 F1

/-- The pointer past the second field. -/
@[expose] def E2 : LOf 4 := numEndAt W4 E1

/-- The pointer past the third field. -/
@[expose] def E3 : LOf 4 := numEndAt W4 E2

/-- The arity is zero. -/
@[expose] def kZero : LOf 4 := isNil (isZeroSeg K4 W4)

/-- The reading of the second field. -/
@[expose] def V2 : LOf 4 := natValueAt W4 E1

/-- A constant: a field within the label, with no direction. -/
@[expose] def constCase : LOf 4 := andF (numOkAt W4 F1) (andF (within E1 R4) kZero)

/-- A projection: two fields ending at the label's end, the second below the
first, with no direction. -/
@[expose] def projCase : LOf 4 :=
  andF (numOkAt W4 F1)
    (andF (numOkAt W4 E1) (andF (endsAt E2 R4) (andF (natLtAt W4 E1 F1) kZero)))

/-- A successor: one more bit, ending the label, with no direction. -/
@[expose] def sbsCase : LOf 4 := andF (notNil F1) (andF (endsAt (tailAppL F1) R4) kZero)

/-- A substitution: two fields ending at the label's end, with one more
direction than the second. -/
@[expose] def compCase : LOf 4 :=
  andF (numOkAt W4 F1)
    (andF (numOkAt W4 E1) (andF (endsAt E2 R4) (eqSeg K4 (tailAppL V2))))

/-- A recursion: three fields ending at the label's end, the third below the
second, with three times the second as directions. -/
@[expose] def srnCase : LOf 4 :=
  andF (numOkAt W4 F1)
    (andF (numOkAt W4 E1)
      (andF (numOkAt W4 E2)
        (andF (endsAt E3 R4)
          (andF (natLtAt W4 E2 E1) (eqSeg K4 (addSeg V2 (addSeg V2 V2 W4) W4))))))

/-- The label check: the dispatch on the tag, then the case of the shape. -/
@[expose] def labelOk : LOf 4 :=
  onBitAt L4 (constL 4 [])
    (onBitAt (tailAppL L4) (constL 4 []) (constL 4 [])
      (onBitAt (tailAppL (tailAppL L4)) (constL 4 []) (constL 4 []) srnCase))
    (onBitAt (tailAppL L4) (constL 4 [])
      (onBitAt (tailAppL (tailAppL L4)) (constL 4 []) compCase sbsCase)
      (onBitAt (tailAppL (tailAppL L4)) (constL 4 []) projCase constCase))

/-- The environment of the label check at a label and an arity. -/
@[expose] def envL (y : List Bool) (l : Loc) (k : ℕ) : Fin 4 → List Bool :=
  ![y, y.drop l.pos, y.drop (l.len + 1), y.drop k]

variable (l : Loc) (k : ℕ)

/-- The word's meaning. -/
theorem sem_W4 : W4.sem (envL y l k) = y := rfl

/-- The label pointer's meaning. -/
theorem sem_L4 : L4.sem (envL y l k) = y.drop l.pos := rfl

/-- The length counter's meaning. -/
theorem sem_Q4 : Q4.sem (envL y l k) = y.drop (l.len + 1) := rfl

/-- The arity counter's meaning. -/
theorem sem_K4 : K4.sem (envL y l k) = y.drop k := rfl

/-- The end pointer's meaning. -/
theorem sem_R4 : R4.sem (envL y l k) = y.drop (l.pos + l.len + 1) :=
  sem_pastEnd W4 L4 Q4 _ y l.pos l.len rfl rfl rfl

/-- The first field pointer's meaning. -/
theorem sem_F1 : F1.sem (envL y l k) = y.drop (l.pos + 3) := by
  rw [F1, sem_tailAppL, sem_tailAppL, sem_tailAppL, sem_L4, List.tail_drop, List.tail_drop,
    List.tail_drop]

/-- The arity test's meaning. -/
theorem sem_kZero (hk : k ≤ y.length) : kZero.sem (envL y l k) = boolWord (decide (k = 0)) := by
  rw [kZero, sem_isNil, sem_isZeroSeg K4 W4 _ y k rfl rfl]
  exact boolWord_decide_congr _ _ (drop_length_sub_eq_nil_iff y k hk)


/-- The dispatch on an empty remaining-input register selects the first
expression. -/
theorem sem_onBitAt_nil {m : ℕ} (rest e t f : LOf m) (x : Fin m → List Bool)
    (hx : rest.sem x = []) : (onBitAt rest e t f).sem x = e.sem x := by
  rw [onBitAt, sem_cond4L, hx]
  rfl

/-- End segments within the word that agree have the same number. -/
theorem drop_inj (a b : ℕ) (ha : a ≤ y.length) (hb : b ≤ y.length) (h : y.drop a = y.drop b) :
    a = b := by
  have := congrArg List.length h
  rw [List.length_drop, List.length_drop] at this
  omega

/-- The scanner accepts at a position exactly when a coded number lies there. -/
theorem nrunOk_iff (tp : ℕ) : nrunOk y tp = true ↔ ∃ m rest, y.drop tp = natCode m ++ rest := by
  unfold nrunOk
  rw [Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · intro h
    obtain ⟨m, rest, hw, _⟩ := nrun_done tp 0 y h.1 h.2
    exact ⟨m, rest, hw⟩
  · intro h
    obtain ⟨m, rest, hw⟩ := h
    have htp : tp < y.length := by
      have := congrArg List.length hw
      rw [List.length_drop, List.length_append] at this
      have := length_natCode m
      omega
    obtain ⟨hd, hok, _⟩ := nrun_natCode tp 0 (y.take tp) rest y m (List.length_take_of_le
      (Nat.le_of_lt htp)) (by rw [List.append_assoc, ← hw, List.take_append_drop])
    exact ⟨hd, hok⟩

/-- The scanner's end at a coded number. -/
theorem endPos_of (tp m : ℕ) (rest : List Bool) (hw : y.drop tp = natCode m ++ rest) :
    (nrun tp 0 y).endPos = tp + (natCode m).length := by
  have htp : tp < y.length := by
    have := congrArg List.length hw
    rw [List.length_drop, List.length_append] at this
    have := length_natCode m
    omega
  exact (nrun_natCode tp 0 (y.take tp) rest y m (List.length_take_of_le (Nat.le_of_lt htp))
    (by rw [List.append_assoc, ← hw, List.take_append_drop])).2.2.1

section Correct

variable (hs : Loc.Sound y l) (hk : k + 1 ≤ y.length)

include hs in
/-- The label lies within the word. -/
theorem lend_le : l.pos + l.len ≤ y.length := by
  rcases hs.2 with h | h <;> omega

omit hs in
/-- The remaining word from the label is the label followed by the remaining
word past it. -/
theorem label_append : labelAt y l ++ y.drop (l.pos + l.len) = y.drop l.pos := by
  unfold labelAt
  rw [← List.drop_drop, List.take_append_drop]

include hs in
/-- The label's length is the location's. -/
theorem length_label : (labelAt y l).length = l.len := by
  unfold labelAt
  rw [List.length_take, List.length_drop]
  have := lend_le y l hs
  omega

/-- Three bits at the label: the field pointer past them, within the word. -/
theorem three_bits (b0 b1 b2 : Bool) (r : List Bool) (h0 : y.drop l.pos = b0 :: b1 :: b2 :: r) :
    l.pos + 3 ≤ y.length ∧ y.drop (l.pos + 3) = r := by
  have hl := congrArg List.length h0
  rw [List.length_drop, List.length_cons, List.length_cons, List.length_cons] at hl
  refine ⟨by omega, ?_⟩
  rw [← List.drop_drop, h0]
  rfl

/-- The label with three bits and the rest cut at its length. -/
theorem label_take (b0 b1 b2 : Bool) (r : List Bool) (h0 : y.drop l.pos = b0 :: b1 :: b2 :: r)
    (h3 : 3 ≤ l.len) : labelAt y l = b0 :: b1 :: b2 :: r.take (l.len - 3) := by
  unfold labelAt
  obtain ⟨j, hj⟩ : ∃ j, l.len = j + 3 := ⟨l.len - 3, by omega⟩
  rw [h0, hj, List.take_succ_cons, List.take_succ_cons, List.take_succ_cons, Nat.add_sub_cancel]

/-- The environment's first field pointer, at three bits of the label. -/
theorem sem_F1_bits (b0 b1 b2 : Bool) (r : List Bool)
    (h0 : y.drop l.pos = b0 :: b1 :: b2 :: r) : F1.sem (envL y l k) = r := by
  rw [sem_F1, (three_bits y l b0 b1 b2 r h0).2]

/-- The acceptance at the first field pointer. -/
theorem sem_ok1 (b0 b1 b2 : Bool) (r : List Bool) (h0 : y.drop l.pos = b0 :: b1 :: b2 :: r) :
    (numOkAt W4 F1).sem (envL y l k) = boolWord (nrunOk y (l.pos + 3)) :=
  sem_numOkAt _ y W4 F1 (l.pos + 3) rfl (sem_F1 y l k) (three_bits y l b0 b1 b2 r h0).1

/-- The pointer past the first field. -/
theorem sem_E1 (b0 b1 b2 : Bool) (r : List Bool) (h0 : y.drop l.pos = b0 :: b1 :: b2 :: r) :
    E1.sem (envL y l k) = y.drop (nrun (l.pos + 3) 0 y).endPos :=
  sem_numEndAt _ y W4 F1 (l.pos + 3) rfl (sem_F1 y l k) (three_bits y l b0 b1 b2 r h0).1

/-- The acceptance at the second field pointer. -/
theorem sem_ok2 (b0 b1 b2 : Bool) (r : List Bool) (h0 : y.drop l.pos = b0 :: b1 :: b2 :: r) :
    (numOkAt W4 E1).sem (envL y l k) = boolWord (nrunOk y (nrun (l.pos + 3) 0 y).endPos) :=
  sem_numOkAt _ y W4 E1 _ rfl (sem_E1 y l k b0 b1 b2 r h0) (nrun_endPos_le _ _ _)

/-- The pointer past the second field. -/
theorem sem_E2 (b0 b1 b2 : Bool) (r : List Bool) (h0 : y.drop l.pos = b0 :: b1 :: b2 :: r) :
    E2.sem (envL y l k) = y.drop (nrun (nrun (l.pos + 3) 0 y).endPos 0 y).endPos :=
  sem_numEndAt _ y W4 E1 _ rfl (sem_E1 y l k b0 b1 b2 r h0) (nrun_endPos_le _ _ _)

/-- The acceptance at the third field pointer. -/
theorem sem_ok3 (b0 b1 b2 : Bool) (r : List Bool) (h0 : y.drop l.pos = b0 :: b1 :: b2 :: r) :
    (numOkAt W4 E2).sem (envL y l k) =
      boolWord (nrunOk y (nrun (nrun (l.pos + 3) 0 y).endPos 0 y).endPos) :=
  sem_numOkAt _ y W4 E2 _ rfl (sem_E2 y l k b0 b1 b2 r h0) (nrun_endPos_le _ _ _)

/-- The pointer past the third field. -/
theorem sem_E3 (b0 b1 b2 : Bool) (r : List Bool) (h0 : y.drop l.pos = b0 :: b1 :: b2 :: r) :
    E3.sem (envL y l k) =
      y.drop (nrun (nrun (nrun (l.pos + 3) 0 y).endPos 0 y).endPos 0 y).endPos :=
  sem_numEndAt _ y W4 E2 _ rfl (sem_E2 y l k b0 b1 b2 r h0) (nrun_endPos_le _ _ _)

/-- A segment cut past a first part is the first part and the rest cut. -/
theorem take_append_add {α : Type} (l₂ : List α) (j : ℕ) : ∀ l₁ : List α,
    (l₁ ++ l₂).take (l₁.length + j) = l₁ ++ l₂.take j :=
  List.rec (by rw [List.length_nil, Nat.zero_add]; rfl) fun a l ih ↦ by
    rw [List.cons_append, List.length_cons, show l.length + 1 + j = l.length + j + 1 by omega,
      List.take_succ_cons, ih]
    rfl

/-- A word starting with the constant tag is the code of a constant, if of any
shape. -/
theorem shape_of_const (a : Shape) (z r : List Bool)
    (h : Sig.code a ++ z = false :: false :: false :: r) : ∃ m w, a = .const m w := by
  cases a <;> simp only [Sig.code, List.cons_append, List.cons.injEq,
    Bool.true_eq_false, false_and, and_false] at h
  exact ⟨_, _, rfl⟩

include hs hk in
/-- The constant case decides the label condition at a label with the constant
tag. -/
theorem constCase_iff (r : List Bool) (h0 : y.drop l.pos = false :: false :: false :: r) :
    isTrueWord (constCase.sem (envL y l k)) = true ↔
      ∃ a, labelAt y l = Sig.code a ∧ sigCoded.card a = k := by
  obtain ⟨h3, hr⟩ := three_bits y l false false false r h0
  have hLend := lend_le y l hs
  rw [constCase, sem_andF _ _ _ _ _ (sem_ok1 y l k _ _ _ r h0)
      (sem_andF _ _ _ _ _ (sem_within E1 R4 _ y _ (l.pos + l.len) (sem_E1 y l k _ _ _ r h0)
        (nrun_endPos_le _ _ _) (sem_R4 y l k) hs.2) (sem_kZero y l k (by omega))),
    isTrueWord_boolWord, Bool.and_eq_true, Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq,
    nrunOk_iff]
  constructor
  · intro h
    obtain ⟨⟨m, rest, hw⟩, hend, hk0⟩ := h
    rw [endPos_of y _ m rest hw] at hend
    have hlw := congrArg List.length hw
    rw [List.length_drop, List.length_append] at hlw
    obtain ⟨j, hj⟩ : ∃ j, l.len - 3 = (natCode m).length + j :=
      ⟨l.len - 3 - (natCode m).length, by omega⟩
    refine ⟨.const m (rest.take j), ?_, hk0.symm⟩
    rw [hr] at hw
    rw [label_take y l false false false r h0 (by omega), hw, hj, take_append_add]
    rfl
  · intro h
    obtain ⟨a, ha, hka⟩ := h
    have hlab := label_append y l
    rw [ha] at hlab
    obtain ⟨m, w, rfl⟩ := shape_of_const a _ r (hlab.trans h0)
    have hlen := length_label y l hs
    rw [ha, Sig.code, List.length_cons, List.length_cons, List.length_cons, List.length_append]
      at hlen
    have hw : y.drop (l.pos + 3) = natCode m ++ (w ++ y.drop (l.pos + l.len)) := by
      rw [hr]
      rw [Sig.code, List.cons_append, List.cons_append, List.cons_append] at hlab
      have := (hlab.trans h0)
      simp only [List.cons.injEq, true_and] at this
      rw [← this, List.append_assoc]
    refine ⟨⟨m, _, hw⟩, ?_, hka.symm⟩
    rw [endPos_of y _ m _ hw]
    omega


/-- A conjunction whose first flag is known holds exactly when both do. -/
theorem isTrueWord_andF_iff {m : ℕ} (a b : LOf m) (x : Fin m → List Bool) (A : Bool)
    (ha : a.sem x = boolWord A) :
    isTrueWord ((andF a b).sem x) = true ↔ A = true ∧ isTrueWord (b.sem x) = true := by
  rw [andF, andOkAt, sem_cond4L, ha, sem_constL, cond4Sem_boolWord_same]
  cases A
  · rw [if_neg (by decide)]
    exact ⟨fun h ↦ absurd h (by decide), fun h ↦ absurd h.1 (by decide)⟩
  · rw [if_pos rfl]
    exact ⟨fun h ↦ ⟨rfl, h⟩, fun h ↦ h.2⟩

/-- A word from a position holds a coded number exactly when the word splits
there. -/
theorem split_at (tp : ℕ) (z : List Bool) (hz : z ≠ []) (hw : y.drop tp = z) :
    y = y.take tp ++ z ∧ (y.take tp).length = tp := by
  have htp : tp < y.length := by
    have := congrArg List.length hw
    rw [List.length_drop] at this
    cases z with
    | nil => exact absurd rfl hz
    | cons c cs => rw [List.length_cons] at this; omega
  exact ⟨by rw [← hw, List.take_append_drop], List.length_take_of_le (Nat.le_of_lt htp)⟩

/-- A coded number followed by a rest is nonempty. -/
theorem natCode_append_ne_nil (m : ℕ) (rest : List Bool) : natCode m ++ rest ≠ [] := by
  intro h
  have := congrArg List.length h
  rw [List.length_append, List.length_nil] at this
  have := length_natCode m
  omega

/-- The order test at the second and first field pointers, given coded numbers
there. -/
theorem natLtAt_E1_F1 (m1 m2 : ℕ) (rest1 rest2 : List Bool)
    (h1 : y.drop (l.pos + 3) = natCode m1 ++ rest1)
    (h2 : y.drop (nrun (l.pos + 3) 0 y).endPos = natCode m2 ++ rest2) :
    (natLtAt W4 E1 F1).sem (envL y l k) = boolWord (decide (m2 < m1)) := by
  obtain ⟨hy1, hu1⟩ := split_at y (l.pos + 3) _ (natCode_append_ne_nil m1 rest1) h1
  obtain ⟨hy2, hu2⟩ := split_at y _ _ (natCode_append_ne_nil m2 rest2) h2
  exact natLtAt_natCode _ y W4 E1 F1 _ rest2 _ rest1 m2 m1 _ (l.pos + 3) rfl
    (by rw [E1, sem_numEndAt _ y W4 F1 (l.pos + 3) rfl (sem_F1 y l k)
      (by
        have h := congrArg List.length h1
        rw [List.length_drop, List.length_append] at h
        have := length_natCode m1
        omega)])
    (sem_F1 y l k) hu2 (by rw [List.append_assoc]; exact hy2) hu1
    (by rw [List.append_assoc]; exact hy1)

/-- A word starting with the projection tag is the code of a projection, if
of any shape. -/
theorem shape_of_proj (a : Shape) (z r : List Bool)
    (h : Sig.code a ++ z = false :: false :: true :: r) : ∃ m i, a = .proj m i := by
  cases a <;> simp only [Sig.code, List.cons_append, List.cons.injEq, Bool.true_eq_false,
    Bool.false_eq_true, false_and, and_false] at h
  exact ⟨_, _, rfl⟩

/-- A word starting with the successor tag is the code of a successor, if of
any shape. -/
theorem shape_of_sbs (a : Shape) (z r : List Bool)
    (h : Sig.code a ++ z = false :: true :: false :: r) : ∃ b, a = .sbs b := by
  cases a <;> simp only [Sig.code, List.cons_append, List.cons.injEq, Bool.true_eq_false,
    Bool.false_eq_true, false_and, and_false] at h
  exact ⟨_, rfl⟩

/-- A word starting with the substitution tag is the code of a substitution,
if of any shape. -/
theorem shape_of_comp (a : Shape) (z r : List Bool)
    (h : Sig.code a ++ z = false :: true :: true :: r) : ∃ m m', a = .comp m m' := by
  cases a <;> simp only [Sig.code, List.cons_append, List.cons.injEq, Bool.true_eq_false,
    Bool.false_eq_true, false_and, and_false] at h
  exact ⟨_, _, rfl⟩

/-- A word starting with the recursion tag is the code of a recursion, if of
any shape. -/
theorem shape_of_srn (a : Shape) (z r : List Bool)
    (h : Sig.code a ++ z = true :: false :: false :: r) : ∃ m m' j, a = .srn m m' j := by
  cases a <;> simp only [Sig.code, List.cons_append, List.cons.injEq, Bool.false_eq_true,
    false_and] at h
  exact ⟨_, _, _, rfl⟩

/-- No code starts with a tag of two set bits, or with the set, clear, set
tag. -/
theorem no_shape (a : Shape) (z r : List Bool) (b1 b2 : Bool)
    (h : Sig.code a ++ z = true :: b1 :: b2 :: r) (hb : b1 = true ∨ b2 = true) : False := by
  cases a <;> simp only [Sig.code, List.cons_append, List.cons.injEq, Bool.false_eq_true,
    false_and] at h
  obtain ⟨-, rfl, rfl, -⟩ := h
  rcases hb with h | h <;> cases h

include hs hk in
/-- The projection case decides the label condition at a label with the
projection tag. -/
theorem projCase_iff (r : List Bool) (h0 : y.drop l.pos = false :: false :: true :: r) :
    isTrueWord (projCase.sem (envL y l k)) = true ↔
      ∃ a, labelAt y l = Sig.code a ∧ sigCoded.card a = k := by
  obtain ⟨h3, hr⟩ := three_bits y l false false true r h0
  have hLend := lend_le y l hs
  rw [projCase, isTrueWord_andF_iff _ _ _ _ (sem_ok1 y l k _ _ _ r h0),
    isTrueWord_andF_iff _ _ _ _ (sem_ok2 y l k _ _ _ r h0),
    isTrueWord_andF_iff _ _ _ _ (sem_endsAt E2 R4 _ y _ (l.pos + l.len) (sem_E2 y l k _ _ _ r h0)
      (nrun_endPos_le _ _ _) (sem_R4 y l k) hs.2),
    nrunOk_iff, nrunOk_iff, decide_eq_true_eq]
  constructor
  · intro h
    obtain ⟨⟨m1, rest1, hw1⟩, ⟨m2, rest2, hw2⟩, hend, hlt⟩ := h
    rw [isTrueWord_andF_iff _ _ _ _ (natLtAt_E1_F1 y l k m1 m2 rest1 rest2 hw1 hw2),
      sem_kZero y l k (by omega), isTrueWord_boolWord, decide_eq_true_eq, decide_eq_true_eq] at hlt
    obtain ⟨hlt, hk0⟩ := hlt
    rw [endPos_of y _ m1 rest1 hw1] at hw2 hend
    rw [endPos_of y _ m2 rest2 hw2] at hend
    have hrest1 : rest1 = natCode m2 ++ rest2 := by
      rw [← hw2, ← List.drop_drop, hw1, List.drop_left]
    refine ⟨.proj m1 ⟨m2, hlt⟩, ?_, hk0.symm⟩
    rw [label_take y l false false true r h0 (by omega), ← hr, hw1, hrest1, ← List.append_assoc,
      show l.len - 3 = (natCode m1 ++ natCode m2).length by
        rw [List.length_append]; omega,
      List.take_left]
    rfl
  · intro h
    obtain ⟨a, ha, hka⟩ := h
    have hlab := label_append y l
    rw [ha] at hlab
    obtain ⟨m1, i, rfl⟩ := shape_of_proj a _ r (hlab.trans h0)
    have hlen := length_label y l hs
    rw [ha, Sig.code, List.length_cons, List.length_cons, List.length_cons, List.length_append]
      at hlen
    have hw1 : y.drop (l.pos + 3) = natCode m1 ++ (natCode i ++ y.drop (l.pos + l.len)) := by
      rw [hr]
      rw [Sig.code, List.cons_append, List.cons_append, List.cons_append] at hlab
      have := (hlab.trans h0)
      simp only [List.cons.injEq, true_and] at this
      rw [← this, List.append_assoc]
    have hw2 : y.drop (l.pos + 3 + (natCode m1).length) =
        natCode i ++ y.drop (l.pos + l.len) := by
      rw [← List.drop_drop, hw1, List.drop_left]
    have hw2' : y.drop (nrun (l.pos + 3) 0 y).endPos = natCode i ++ y.drop (l.pos + l.len) := by
      rw [endPos_of y _ m1 _ hw1]
      exact hw2
    refine ⟨⟨m1, _, hw1⟩, ⟨i, _, hw2'⟩, ?_, ?_⟩
    · rw [endPos_of y _ m1 _ hw1, endPos_of y _ i _ hw2]
      omega
    · rw [isTrueWord_andF_iff _ _ _ _ (natLtAt_E1_F1 y l k m1 i _ _ hw1 hw2'),
        sem_kZero y l k (by omega), isTrueWord_boolWord, decide_eq_true_eq, decide_eq_true_eq]
      exact ⟨i.2, hka.symm⟩

include hs hk in
/-- The successor case decides the label condition at a label with the
successor tag. -/
theorem sbsCase_iff (r : List Bool) (h0 : y.drop l.pos = false :: true :: false :: r) :
    isTrueWord (sbsCase.sem (envL y l k)) = true ↔
      ∃ a, labelAt y l = Sig.code a ∧ sigCoded.card a = k := by
  obtain ⟨h3, hr⟩ := three_bits y l false true false r h0
  have hLend := lend_le y l hs
  rw [sbsCase, isTrueWord_andF_iff _ _ _ _ (by rw [sem_notNil, sem_F1_bits y l k _ _ _ r h0]),
    decide_eq_true_eq]
  constructor
  · intro h
    obtain ⟨hne, h⟩ := h
    cases hcr : r with
    | nil => exact absurd hcr hne
    | cons b r' =>
      have h4 : l.pos + 4 ≤ y.length := by
        have := congrArg List.length hr
        rw [List.length_drop, hcr, List.length_cons] at this
        omega
      rw [isTrueWord_andF_iff _ _ _ _ (sem_endsAt (tailAppL F1) R4 _ y (l.pos + 4) (l.pos + l.len)
          (by rw [sem_tailAppL, sem_F1, List.tail_drop]) h4 (sem_R4 y l k) hs.2),
        sem_kZero y l k (by omega), isTrueWord_boolWord, decide_eq_true_eq, decide_eq_true_eq] at h
      obtain ⟨hend, hk0⟩ := h
      refine ⟨.sbs b, ?_, hk0.symm⟩
      rw [label_take y l false true false r h0 (by omega), hcr, show l.len - 3 = 0 + 1 by omega,
        List.take_succ_cons, List.take_zero]
      rfl
  · intro h
    obtain ⟨a, ha, hka⟩ := h
    have hlab := label_append y l
    rw [ha] at hlab
    obtain ⟨b, rfl⟩ := shape_of_sbs a _ r (hlab.trans h0)
    have hlen := length_label y l hs
    rw [ha] at hlen
    change 4 = l.len at hlen
    have hcr : r = b :: y.drop (l.pos + l.len) := by
      have := hlab.trans h0
      simp only [Sig.code, List.cons_append, List.nil_append, List.cons.injEq, true_and] at this
      exact this.symm
    refine ⟨by rw [hcr]; exact List.cons_ne_nil _ _, ?_⟩
    rw [isTrueWord_andF_iff _ _ _ _ (sem_endsAt (tailAppL F1) R4 _ y (l.pos + 4) (l.pos + l.len)
        (by rw [sem_tailAppL, sem_F1, List.tail_drop, show l.pos + 3 + 1 = l.pos + 4 by omega])
        (by omega) (sem_R4 y l k) hs.2),
      sem_kZero y l k (by omega), isTrueWord_boolWord, decide_eq_true_eq, decide_eq_true_eq]
    exact ⟨by omega, hka.symm⟩

include hs hk in
/-- The substitution case decides the label condition at a label with the
substitution tag. -/
theorem compCase_iff (r : List Bool) (h0 : y.drop l.pos = false :: true :: true :: r) :
    isTrueWord (compCase.sem (envL y l k)) = true ↔
      ∃ a, labelAt y l = Sig.code a ∧ sigCoded.card a = k := by
  obtain ⟨h3, hr⟩ := three_bits y l false true true r h0
  have hLend := lend_le y l hs
  rw [compCase, isTrueWord_andF_iff _ _ _ _ (sem_ok1 y l k _ _ _ r h0),
    isTrueWord_andF_iff _ _ _ _ (sem_ok2 y l k _ _ _ r h0),
    isTrueWord_andF_iff _ _ _ _ (sem_endsAt E2 R4 _ y _ (l.pos + l.len) (sem_E2 y l k _ _ _ r h0)
      (nrun_endPos_le _ _ _) (sem_R4 y l k) hs.2),
    nrunOk_iff, nrunOk_iff, decide_eq_true_eq]
  have hV : ∀ (m1 m2 : ℕ) (rest1 rest2 : List Bool), y.drop (l.pos + 3) = natCode m1 ++ rest1 →
      y.drop (nrun (l.pos + 3) 0 y).endPos = natCode m2 ++ rest2 →
      (eqSeg K4 (tailAppL V2)).sem (envL y l k) =
        boolWord (decide (k = min (m2 + 1) y.length)) := by
    intro m1 m2 rest1 rest2 hw1 hw2
    obtain ⟨hy2, hu2⟩ := split_at y _ _ (natCode_append_ne_nil m2 rest2) hw2
    have hlen1 : l.pos + 3 ≤ y.length := h3
    refine sem_eqSeg K4 (tailAppL V2) _ y k (min (m2 + 1) y.length) rfl ?_ (by omega)
      (Nat.min_le_right _ _)
    rw [sem_tailAppL, V2, natValueAt_natCode _ y W4 E1 _ rest2 m2 _ rfl
      (by rw [E1, sem_numEndAt _ y W4 F1 (l.pos + 3) rfl (sem_F1 y l k) hlen1]) hu2
      (by rw [List.append_assoc]; exact hy2), tail_drop_min]
  constructor
  · intro h
    obtain ⟨⟨m1, rest1, hw1⟩, ⟨m2, rest2, hw2⟩, hend, hkm⟩ := h
    rw [hV m1 m2 rest1 rest2 hw1 hw2, isTrueWord_boolWord, decide_eq_true_eq] at hkm
    rw [endPos_of y _ m1 rest1 hw1] at hw2 hend
    rw [endPos_of y _ m2 rest2 hw2] at hend
    have hrest1 : rest1 = natCode m2 ++ rest2 := by
      rw [← hw2, ← List.drop_drop, hw1, List.drop_left]
    refine ⟨.comp m1 m2, ?_, ?_⟩
    · rw [label_take y l false true true r h0 (by omega), ← hr, hw1, hrest1, ← List.append_assoc,
        show l.len - 3 = (natCode m1 ++ natCode m2).length by
          rw [List.length_append]; omega,
        List.take_left]
      rfl
    · change m2 + 1 = k
      omega
  · intro h
    obtain ⟨a, ha, hka⟩ := h
    have hlab := label_append y l
    rw [ha] at hlab
    obtain ⟨m1, m2, rfl⟩ := shape_of_comp a _ r (hlab.trans h0)
    have hlen := length_label y l hs
    rw [ha, Sig.code, List.length_cons, List.length_cons, List.length_cons, List.length_append]
      at hlen
    have hw1 : y.drop (l.pos + 3) = natCode m1 ++ (natCode m2 ++ y.drop (l.pos + l.len)) := by
      rw [hr]
      rw [Sig.code, List.cons_append, List.cons_append, List.cons_append] at hlab
      have := (hlab.trans h0)
      simp only [List.cons.injEq, true_and] at this
      rw [← this, List.append_assoc]
    have hw2 : y.drop (l.pos + 3 + (natCode m1).length) =
        natCode m2 ++ y.drop (l.pos + l.len) := by
      rw [← List.drop_drop, hw1, List.drop_left]
    have hw2' : y.drop (nrun (l.pos + 3) 0 y).endPos = natCode m2 ++ y.drop (l.pos + l.len) := by
      rw [endPos_of y _ m1 _ hw1]
      exact hw2
    refine ⟨⟨m1, _, hw1⟩, ⟨m2, _, hw2'⟩, ?_, ?_⟩
    · rw [endPos_of y _ m1 _ hw1, endPos_of y _ m2 _ hw2]
      omega
    · rw [hV m1 m2 _ _ hw1 hw2', isTrueWord_boolWord, decide_eq_true_eq]
      change m2 + 1 = k at hka
      omega

include hs hk in
/-- The recursion case decides the label condition at a label with the
recursion tag. -/
theorem srnCase_iff (r : List Bool) (h0 : y.drop l.pos = true :: false :: false :: r) :
    isTrueWord (srnCase.sem (envL y l k)) = true ↔
      ∃ a, labelAt y l = Sig.code a ∧ sigCoded.card a = k := by
  obtain ⟨h3, hr⟩ := three_bits y l true false false r h0
  have hLend := lend_le y l hs
  rw [srnCase, isTrueWord_andF_iff _ _ _ _ (sem_ok1 y l k _ _ _ r h0),
    isTrueWord_andF_iff _ _ _ _ (sem_ok2 y l k _ _ _ r h0),
    isTrueWord_andF_iff _ _ _ _ (sem_ok3 y l k _ _ _ r h0),
    isTrueWord_andF_iff _ _ _ _ (sem_endsAt E3 R4 _ y _ (l.pos + l.len) (sem_E3 y l k _ _ _ r h0)
      (nrun_endPos_le _ _ _) (sem_R4 y l k) hs.2),
    nrunOk_iff, nrunOk_iff, nrunOk_iff, decide_eq_true_eq]
  -- the order test of the third and second fields, and the arity test
  have hrest : ∀ (m1 m2 m3 : ℕ) (rest1 rest2 rest3 : List Bool),
      y.drop (l.pos + 3) = natCode m1 ++ rest1 →
      y.drop (nrun (l.pos + 3) 0 y).endPos = natCode m2 ++ rest2 →
      y.drop (nrun (nrun (l.pos + 3) 0 y).endPos 0 y).endPos = natCode m3 ++ rest3 →
      (natLtAt W4 E2 E1).sem (envL y l k) = boolWord (decide (m3 < m2)) ∧
        (eqSeg K4 (addSeg V2 (addSeg V2 V2 W4) W4)).sem (envL y l k) =
          boolWord (decide (k = min (m2 + m2 + m2) y.length)) := by
    intro m1 m2 m3 rest1 rest2 rest3 hw1 hw2 hw3
    obtain ⟨hy2, hu2⟩ := split_at y _ _ (natCode_append_ne_nil m2 rest2) hw2
    obtain ⟨hy3, hu3⟩ := split_at y _ _ (natCode_append_ne_nil m3 rest3) hw3
    have hE1 : E1.sem (envL y l k) = y.drop (nrun (l.pos + 3) 0 y).endPos :=
      sem_E1 y l k _ _ _ r h0
    have hE2 : E2.sem (envL y l k) = y.drop (nrun (nrun (l.pos + 3) 0 y).endPos 0 y).endPos :=
      sem_E2 y l k _ _ _ r h0
    have hV2 : V2.sem (envL y l k) = y.drop m2 :=
      natValueAt_natCode _ y W4 E1 _ rest2 m2 _ rfl hE1 hu2 (by rw [List.append_assoc]; exact hy2)
    constructor
    · exact natLtAt_natCode _ y W4 E2 E1 _ rest3 _ rest2 m3 m2 _ _ rfl hE2 hE1 hu3
        (by rw [List.append_assoc]; exact hy3) hu2 (by rw [List.append_assoc]; exact hy2)
    · refine sem_eqSeg _ _ _ y k (min (m2 + m2 + m2) y.length) rfl ?_ (by omega)
        (Nat.min_le_right _ _)
      rw [sem_addSeg V2 _ W4 _ y m2 (m2 + m2) hV2
        (sem_addSeg V2 V2 W4 _ y m2 m2 hV2 hV2 rfl) rfl, drop_min_length]
  constructor
  · intro h
    obtain ⟨⟨m1, rest1, hw1⟩, ⟨m2, rest2, hw2⟩, ⟨m3, rest3, hw3⟩, hend, h⟩ := h
    obtain ⟨hlt, hkm⟩ := hrest m1 m2 m3 rest1 rest2 rest3 hw1 hw2 hw3
    rw [isTrueWord_andF_iff _ _ _ _ hlt, hkm, isTrueWord_boolWord, decide_eq_true_eq,
      decide_eq_true_eq] at h
    obtain ⟨hlt, hkm⟩ := h
    rw [endPos_of y _ m1 rest1 hw1] at hw2 hw3 hend
    rw [endPos_of y _ m2 rest2 hw2] at hw3 hend
    rw [endPos_of y _ m3 rest3 hw3] at hend
    have hrest2 : rest2 = natCode m3 ++ rest3 := by
      rw [← hw3, ← List.drop_drop, hw2, List.drop_left]
    have hrest1 : rest1 = natCode m2 ++ rest2 := by
      rw [← hw2, ← List.drop_drop, hw1, List.drop_left]
    refine ⟨.srn m1 m2 ⟨m3, hlt⟩, ?_, ?_⟩
    · rw [label_take y l true false false r h0 (by omega), ← hr, hw1, hrest1, hrest2,
        ← List.append_assoc, ← List.append_assoc,
        show l.len - 3 = (natCode m1 ++ natCode m2 ++ natCode m3).length by
          rw [List.length_append, List.length_append]; omega,
        List.take_left]
      rfl
    · change 3 * m2 = k
      omega
  · intro h
    obtain ⟨a, ha, hka⟩ := h
    have hlab := label_append y l
    rw [ha] at hlab
    obtain ⟨m1, m2, j, rfl⟩ := shape_of_srn a _ r (hlab.trans h0)
    have hlen := length_label y l hs
    rw [ha, Sig.code, List.length_cons, List.length_cons, List.length_cons, List.length_append,
      List.length_append] at hlen
    have hw1 : y.drop (l.pos + 3) =
        natCode m1 ++ (natCode m2 ++ (natCode j ++ y.drop (l.pos + l.len))) := by
      rw [hr]
      rw [Sig.code, List.cons_append, List.cons_append, List.cons_append] at hlab
      have := (hlab.trans h0)
      simp only [List.cons.injEq, true_and] at this
      rw [← this, List.append_assoc, List.append_assoc]
    have hw2 : y.drop (l.pos + 3 + (natCode m1).length) =
        natCode m2 ++ (natCode j ++ y.drop (l.pos + l.len)) := by
      rw [← List.drop_drop, hw1, List.drop_left]
    have hw2' : y.drop (nrun (l.pos + 3) 0 y).endPos =
        natCode m2 ++ (natCode j ++ y.drop (l.pos + l.len)) := by
      rw [endPos_of y _ m1 _ hw1]
      exact hw2
    have hw3 : y.drop (l.pos + 3 + (natCode m1).length + (natCode m2).length) =
        natCode j ++ y.drop (l.pos + l.len) := by
      rw [← List.drop_drop, hw2, List.drop_left]
    have hw3' : y.drop (nrun (nrun (l.pos + 3) 0 y).endPos 0 y).endPos =
        natCode j ++ y.drop (l.pos + l.len) := by
      rw [endPos_of y _ m1 _ hw1, endPos_of y _ m2 _ hw2]
      exact hw3
    obtain ⟨hlt, hkm⟩ := hrest m1 m2 j _ _ _ hw1 hw2' hw3'
    refine ⟨⟨m1, _, hw1⟩, ⟨m2, _, hw2'⟩, ⟨j, _, hw3'⟩, ?_, ?_⟩
    · rw [endPos_of y _ m1 _ hw1, endPos_of y _ m2 _ hw2, endPos_of y _ j _ hw3]
      omega
    · rw [isTrueWord_andF_iff _ _ _ _ hlt, hkm, isTrueWord_boolWord, decide_eq_true_eq,
        decide_eq_true_eq]
      change 3 * m2 = k at hka
      exact ⟨j.2, by omega⟩


/-- Every code has at least four bits. -/
theorem four_le_length_code (a : Shape) : 4 ≤ (Sig.code a).length := by
  cases a <;> simp only [Sig.code, List.length_cons, List.length_append, List.length_nil] <;>
    (try have := length_natCode (by assumption : ℕ)) <;> omega

/-- The label check at a label of fewer than three bits from the location: the
empty word. -/
theorem sem_short (h : (y.drop l.pos).length ≤ 2) : labelOk.sem (envL y l k) = [] := by
  rw [labelOk]
  cases h0 : y.drop l.pos with
  | nil => rw [sem_onBitAt_nil _ _ _ _ _ (by rw [sem_L4, h0]), sem_constL]
  | cons b0 r0 =>
    rw [sem_onBitAt _ _ _ _ _ b0 r0 (by rw [sem_L4, h0])]
    cases r0 with
    | nil =>
      cases b0
      · rw [if_neg (by decide),
          sem_onBitAt_nil _ _ _ _ _ (by rw [sem_tailAppL, sem_L4, h0]; rfl), sem_constL]
      · rw [if_pos rfl, sem_onBitAt_nil _ _ _ _ _ (by rw [sem_tailAppL, sem_L4, h0]; rfl),
          sem_constL]
    | cons b1 r1 =>
      cases r1 with
      | nil =>
        have h2 : (tailAppL (tailAppL L4)).sem (envL y l k) = [] := by
          rw [sem_tailAppL, sem_tailAppL, sem_L4, h0]
          rfl
        have h1 : (tailAppL L4).sem (envL y l k) = b1 :: [] := by
          rw [sem_tailAppL, sem_L4, h0]
          rfl
        cases b0
        · rw [if_neg (by decide), sem_onBitAt _ _ _ _ _ b1 [] h1]
          cases b1
          · rw [if_neg (by decide), sem_onBitAt_nil _ _ _ _ _ h2, sem_constL]
          · rw [if_pos rfl, sem_onBitAt_nil _ _ _ _ _ h2, sem_constL]
        · rw [if_pos rfl, sem_onBitAt _ _ _ _ _ b1 [] h1]
          cases b1
          · rw [if_neg (by decide), sem_onBitAt_nil _ _ _ _ _ h2, sem_constL]
          · rw [if_pos rfl, sem_constL]
      | cons b2 r2 =>
        rw [h0] at h
        simp only [List.length_cons] at h
        omega

/-- The case of the tag, by its three bits: the five cases of a shape, and the
empty word at the three tags of no shape. -/
@[expose] def tagCase : Bool → Bool → Bool → LOf 4
  | false, false, false => constCase
  | false, false, true => projCase
  | false, true, false => sbsCase
  | false, true, true => compCase
  | true, false, false => srnCase
  | true, _, _ => constL 4 []

/-- The label check at a label of three bits or more dispatches to the case of
the tag. -/
theorem sem_tag (b0 b1 b2 : Bool) (r : List Bool) (h0 : y.drop l.pos = b0 :: b1 :: b2 :: r) :
    labelOk.sem (envL y l k) = (tagCase b0 b1 b2).sem (envL y l k) := by
  have h1 : (tailAppL L4).sem (envL y l k) = b1 :: b2 :: r := by
    rw [sem_tailAppL, sem_L4, h0]
    rfl
  have h2 : (tailAppL (tailAppL L4)).sem (envL y l k) = b2 :: r := by
    rw [sem_tailAppL, sem_tailAppL, sem_L4, h0]
    rfl
  rw [labelOk, sem_onBitAt _ _ _ _ _ b0 (b1 :: b2 :: r) (by rw [sem_L4, h0])]
  cases b0
  · rw [if_neg (by decide), sem_onBitAt _ _ _ _ _ b1 (b2 :: r) h1]
    cases b1
    · rw [if_neg (by decide), sem_onBitAt _ _ _ _ _ b2 r h2]
      cases b2
      · rw [if_neg (by decide)]
        rfl
      · rw [if_pos rfl]
        rfl
    · rw [if_pos rfl, sem_onBitAt _ _ _ _ _ b2 r h2]
      cases b2
      · rw [if_neg (by decide)]
        rfl
      · rw [if_pos rfl]
        rfl
  · rw [if_pos rfl, sem_onBitAt _ _ _ _ _ b1 (b2 :: r) h1]
    cases b1
    · rw [if_neg (by decide), sem_onBitAt _ _ _ _ _ b2 r h2]
      cases b2
      · rw [if_neg (by decide)]
        rfl
      · rw [if_pos rfl]
        rfl
    · rw [if_pos rfl]
      cases b2 <;> rfl

include hs hk in
/-- At a sound label and an arity below the word's length, the label check
reads as the signature's label condition. -/
theorem labelOk_eq :
    isTrueWord (labelOk.sem (envL y l k)) = sigCoded.labelSpec (labelAt y l) k := by
  rw [Bool.eq_iff_iff, labelSpec_eq_true_iff]
  have hlab := label_append y l
  by_cases hshort : (y.drop l.pos).length ≤ 2
  · rw [sem_short y l k hshort]
    refine ⟨fun h ↦ absurd h (by decide), fun h ↦ ?_⟩
    obtain ⟨a, ha, _⟩ := h
    rw [ha] at hlab
    have := congrArg List.length hlab
    rw [List.length_append] at this
    have h4 : 4 ≤ (sigCoded.code a).length := four_le_length_code a
    omega
  · obtain ⟨b0, b1, b2, r, h0⟩ : ∃ b0 b1 b2 r, y.drop l.pos = b0 :: b1 :: b2 :: r := by
      cases h0 : y.drop l.pos with
      | nil => rw [h0] at hshort; exact absurd (Nat.zero_le _) hshort
      | cons b0 r0 =>
        cases r0 with
        | nil => rw [h0, List.length_singleton] at hshort; exact absurd (by decide) hshort
        | cons b1 r1 =>
          cases r1 with
          | nil =>
            rw [h0, List.length_cons, List.length_singleton] at hshort
            exact absurd (by decide) hshort
          | cons b2 r2 => exact ⟨b0, b1, b2, r2, rfl⟩
    rw [sem_tag y l k b0 b1 b2 r h0]
    cases b0 <;> cases b1 <;> cases b2
    · exact constCase_iff y l k hs hk r h0
    · exact projCase_iff y l k hs hk r h0
    · exact sbsCase_iff y l k hs hk r h0
    · exact compCase_iff y l k hs hk r h0
    · exact srnCase_iff y l k hs hk r h0
    all_goals
      refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
      · change isTrueWord ((constL 4 []).sem (envL y l k)) = true at h
        rw [sem_constL] at h
        exact absurd h (by decide)
      · obtain ⟨a, ha, _⟩ := h
        rw [ha] at hlab
        exact (no_shape a _ r _ _ (hlab.trans h0) (by decide)).elim

end Correct

/-- The label check computes the signature's label condition on every word. -/
theorem computesLabel : sigCoded.ComputesLabel labelOk y :=
  fun l k hs hk ↦ labelOk_eq y l k hs hk


end Label

end

end Geb.SizeBounded.Logspace.WTree.SigLabel
