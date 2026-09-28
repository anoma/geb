/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
-- Modified from geb-mathlib by scripts/geb-mathlib-backport.patch.
module

public import Geb.Prototypes.Computability.SizeBounded.Logspace.WTree.BitFold
public import Geb.Prototypes.Computability.SizeBounded.Logspace.WTree.NumBits

set_option doc.verso true in
/-!
# Comparing numerals and reading one into a counter

Three instances of the lockstep fold over the bits of numerals,
{name}`Geb.SizeBounded.Logspace.WTree.BitFold.bitFold`: the equality test of
two coded numbers, their order, and the reading of a coded number into a
counter, an end segment of the word, which saturates at the word's length.
Each is an expression of arity four, the word and three positions, of which
the equality and the order read two and the reading one. The equality folds
over the codes, which the code's injectivity makes sufficient and which the
scanner's end position alone delimits; the order and the reading fold over
the payloads, which they need aligned by index. The updates are
truth tables on flags, {lit}`tt2` and {lit}`tt3`, and conditionals on flags.

# Main definitions

* {lit}`flagK`, {lit}`tt2`, {lit}`tt3` — a constant flag and the truth
  tables of two and three flags.
* {lit}`natEq`, {lit}`natLt`, {lit}`natValue` — the equality test, the order
  test and the reading into a counter.
* {lit}`natCode_eq_of_getD` — numbers whose codes agree below a bound both
  lie within are equal.

# Main statements

* {lit}`sem_tt2`, {lit}`sem_tt3`, {lit}`sem_ifFlag` — the meanings of the
  truth tables and of the conditional on a flag.
* {lit}`natEq_natCode`, {lit}`natLt_natCode`, {lit}`natValue_natCode` — on a
  word holding coded numbers at the positions, the tests decide equality and
  order of the numbers, and the reading is the word dropped by the number.

# References

* \[Kristiansen2005\]

# Tags

logspace, binary numeral, comparison, counter
-/

set_option doc.verso true

namespace Geb.SizeBounded.Logspace.WTree.NumArith

open Numeral BitFold NumExpr

public section

/-- A constant flag. -/
@[expose] def flagK (n : ℕ) (b : Bool) : LOf n := constL n (boolWord b)

/-- The meaning of a conditional on a flag. -/
theorem sem_ifFlag {n : ℕ} (f t e : LOf n) (x : Fin n → List Bool) (b : Bool)
    (hf : f.sem x = boolWord b) : (ifFlag f t e).sem x = if b then t.sem x else e.sem x := by
  rw [ifFlag, sem_cond4L, hf, cond4Sem_boolWord_same]

/-- The truth table of two flags. -/
@[expose] def tt2 {n : ℕ} (a b : LOf n) (v : Bool → Bool → Bool) : LOf n :=
  ifFlag a (ifFlag b (flagK n (v true true)) (flagK n (v true false)))
    (ifFlag b (flagK n (v false true)) (flagK n (v false false)))

/-- The truth table's meaning. -/
theorem sem_tt2 {n : ℕ} (a b : LOf n) (v : Bool → Bool → Bool) (x : Fin n → List Bool)
    (A B : Bool) (ha : a.sem x = boolWord A) (hb : b.sem x = boolWord B) :
    (tt2 a b v).sem x = boolWord (v A B) := by
  rw [tt2, sem_ifFlag _ _ _ x A ha]
  cases A <;> simp only [↓reduceIte, Bool.false_eq_true] <;> rw [sem_ifFlag _ _ _ x B hb] <;>
    cases B <;> rfl

/-- The truth table of three flags. -/
@[expose] def tt3 {n : ℕ} (a b c : LOf n) (v : Bool → Bool → Bool → Bool) : LOf n :=
  ifFlag a (tt2 b c (v true)) (tt2 b c (v false))

/-- The truth table's meaning. -/
theorem sem_tt3 {n : ℕ} (a b c : LOf n) (v : Bool → Bool → Bool → Bool) (x : Fin n → List Bool)
    (A B C : Bool) (ha : a.sem x = boolWord A) (hb : b.sem x = boolWord B)
    (hc : c.sem x = boolWord C) : (tt3 a b c v).sem x = boolWord (v A B C) := by
  rw [tt3, sem_ifFlag _ _ _ x A ha]
  cases A <;> simp only [↓reduceIte, Bool.false_eq_true] <;> exact sem_tt2 _ _ _ x B C hb hc

section Equality

/-- The flag, the sole register. -/
@[expose] def flagE : LOf 5 := projL 5 0

/-- The bit of the first number. -/
@[expose] def bitAE : LOf 5 := projL 5 1

/-- The bit of the second number. -/
@[expose] def bitBE : LOf 5 := projL 5 2

/-- The update of the equality test: the flag conjoined with the agreement of
the two bits. -/
@[expose] def updEq : Fin 1 → LOf 5 := ![andOkAt flagE (tt2 bitAE bitBE (· == ·))]

/-- The base of the equality test: the flag set. -/
@[expose] def baseEq : Fin 1 → LOf 4 := ![constL 4 [true]]

/-- The equality test of the numbers at the first two positions: their codes
agree bit by bit, which by the code's injectivity is the numbers' equality,
and the code needs only the scanner's end position to delimit. -/
@[expose] def natEq : LOf 4 := bitFold codeScan baseEq updEq 0

/-- The agreement of the bits of the two numbers below an index. -/
@[expose] def eqBits (bA bB : ℕ → Bool) : ℕ → Bool :=
  Nat.rec true fun i r ↦ r && (bA i == bB i)

/-- The register of the equality test after the indices below a bound. -/
theorem iter_eq (y : List Bool) (bA bB bC : ℕ → Bool) (pA pB pC : ℕ) : ∀ n,
    iter updEq y bA bB bC (regs0 baseEq y pA pB pC) n 0 = boolWord (eqBits bA bB n) :=
  Nat.rec rfl fun n ih ↦ by
    change (andOkAt flagE (tt2 bitAE bitBE (· == ·))).sem _ = _
    rw [andOkAt, sem_cond4L, sem_tt2 _ _ _ _ (bA n) (bB n) rfl rfl, sem_constL]
    change cond4Sem (iter updEq y bA bB bC (regs0 baseEq y pA pB pC) n 0) [] _ _ = _
    rw [ih, cond4Sem_boolWord]
    rfl

/-- The agreement below a bound holds exactly when the bits agree at every
index below it. -/
theorem eqBits_eq_true_iff (bA bB : ℕ → Bool) : ∀ n,
    eqBits bA bB n = true ↔ ∀ i < n, bA i = bB i :=
  Nat.rec ⟨fun _ i h ↦ absurd h (Nat.not_lt_zero i), fun _ ↦ rfl⟩ fun n ih ↦ by
    change (eqBits bA bB n && (bA n == bB n)) = true ↔ _
    rw [Bool.and_eq_true, ih, beq_iff_eq]
    constructor
    · intro h i hi
      by_cases hin : i = n
      · rw [hin]
        exact h.2
      · exact h.1 i (by omega)
    · intro h
      exact ⟨fun i hi ↦ h i (by omega), h n (Nat.lt_succ_self n)⟩

/-- A list that another agrees with at every index below its length is that
other's prefix of that length. -/
theorem take_eq_of_getD (l1 l2 : List Bool) (h12 : l1.length ≤ l2.length)
    (h : ∀ i < l1.length, l1.getD i false = l2.getD i false) : l2.take l1.length = l1 := by
  refine List.ext_getElem (by rw [List.length_take]; omega) fun i h1 h2 ↦ ?_
  have hi := h i h2
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem h2, List.getElem?_eq_getElem (by omega)] at hi
  rw [List.getElem_take]
  exact hi.symm

/-- Numbers whose codes agree at every index below a bound that both codes lie
within are equal. -/
theorem natCode_eq_of_getD (A B n : ℕ) (hA : (natCode A).length ≤ n)
    (hB : (natCode B).length ≤ n)
    (h : ∀ i < n, (natCode A).getD i false = (natCode B).getD i false) : A = B := by
  have key : ∀ C D : ℕ, (natCode C).length ≤ (natCode D).length →
      (∀ i < (natCode C).length, (natCode C).getD i false = (natCode D).getD i false) → C = D := by
    intro C D hle hi
    have hsplit : natCode D = natCode C ++ (natCode D).drop (natCode C).length := by
      conv_lhs => rw [← List.take_append_drop (natCode C).length (natCode D)]
      rw [take_eq_of_getD _ _ hle hi]
    have hD := readNatCode_natCode_append D []
    rw [List.append_nil, hsplit,
      readNatCode_natCode_append C ((natCode D).drop (natCode C).length)] at hD
    exact (Prod.mk.inj (Option.some.inj hD)).1
  rcases Nat.le_total (natCode A).length (natCode B).length with hle | hle
  · exact key A B hle fun i hi ↦ h i (Nat.lt_of_lt_of_le hi hA)
  · exact (key B A hle fun i hi ↦ (h i (Nat.lt_of_lt_of_le hi hB)).symm).symm

/-- The bits of a number coded at a position, as the fold reads them, are the
number's bits. -/
theorem payBit_eq_testBit (y u r : List Bool) (A p : ℕ) (hu : u.length = p)
    (hy : y = u ++ natCode A ++ r) (i : ℕ) : payBit y p i = A.testBit i := by
  rw [payBit_natCode y u r A p hu hy, bits_getD_eq_testBit]

/-- A coded number's position lies within the word. -/
theorem pos_le_length (y u r : List Bool) (A p : ℕ) (hu : u.length = p)
    (hy : y = u ++ natCode A ++ r) : p ≤ y.length := by
  rw [hy, List.length_append, List.length_append, hu]
  omega

/-- A coded number's binary size is bounded by the word's length. -/
theorem size_le_length (y u r : List Bool) (A : ℕ) (hy : y = u ++ natCode A ++ r) :
    A.size ≤ y.length := by
  have := size_le_length_natCode A
  rw [hy, List.length_append, List.length_append]
  omega

/-- A coded number is below the power of two at the word's length. -/
theorem lt_two_pow_length (y u r : List Bool) (A : ℕ) (hy : y = u ++ natCode A ++ r) :
    A < 2 ^ y.length :=
  lt_two_pow_of_size_le A y.length (size_le_length y u r A hy)

/-- On a word holding coded numbers at the first two positions, the equality
test decides their equality. -/
theorem natEq_natCode (y uA rA uB rB : List Bool) (A B pA pB pC : ℕ) (huA : uA.length = pA)
    (hyA : y = uA ++ natCode A ++ rA) (huB : uB.length = pB) (hyB : y = uB ++ natCode B ++ rB)
    (hC : pC ≤ y.length) :
    natEq.sem ![y, y.drop pA, y.drop pB, y.drop pC] = boolWord (decide (A = B)) := by
  have hhA := codeBit_natCode y uA rA A pA huA hyA
  have hhB := codeBit_natCode y uB rB B pB huB hyB
  rw [natEq, sem_bitFold_code _ _ y pA pB pC (pos_le_length y uA rA A pA huA hyA)
    (pos_le_length y uB rB B pB huB hyB) hC, iter_eq]
  have : eqBits (codeBit y pA) (codeBit y pB) y.length = decide (A = B) := by
    by_cases h : A = B
    · rw [decide_eq_true h]
      exact (eqBits_eq_true_iff _ _ y.length).mpr fun i _ ↦ by rw [hhA, hhB, h]
    · rw [decide_eq_false h]
      cases he : eqBits (codeBit y pA) (codeBit y pB) y.length
      · rfl
      · exact absurd (natCode_eq_of_getD A B y.length (length_natCode_le y uA rA A hyA)
          (length_natCode_le y uB rB B hyB) fun i hi ↦ by
            rw [← hhA, ← hhB]
            exact (eqBits_eq_true_iff _ _ y.length).mp he i hi) h
  rw [this]

end Equality

section Order

/-- The update of the order test: the verdict kept where the bits agree, the
second number's bit where they differ. -/
@[expose] def updLt : Fin 1 → LOf 5 := ![ifFlag (tt2 bitAE bitBE (· == ·)) flagE bitBE]

/-- The base of the order test: the verdict clear. -/
@[expose] def baseLt : Fin 1 → LOf 4 := ![constL 4 []]

/-- The order test: the number at the first position is below the number at
the second. -/
@[expose] def natLt : LOf 4 := bitFold payScan baseLt updLt 0

/-- The verdict after the bits below an index: the second number's bit at the
highest index below it where the bits differ, clear when none. -/
@[expose] def ltBits (bA bB : ℕ → Bool) : ℕ → Bool :=
  Nat.rec false fun i r ↦ if (bA i == bB i) then r else bB i

/-- The register of the order test after the indices below a bound. -/
theorem iter_lt (y : List Bool) (bA bB bC : ℕ → Bool) (pA pB pC : ℕ) : ∀ n,
    iter updLt y bA bB bC (regs0 baseLt y pA pB pC) n 0 = boolWord (ltBits bA bB n) :=
  Nat.rec rfl fun n ih ↦ by
    change (ifFlag (tt2 bitAE bitBE (· == ·)) flagE bitBE).sem _ = _
    rw [sem_ifFlag _ _ _ _ _ (sem_tt2 _ _ _ _ (bA n) (bB n) rfl rfl)]
    change (if (bA n == bB n) then
        iter updLt y bA bB bC (regs0 baseLt y pA pB pC) n 0 else boolWord (bB n)) =
      boolWord (if (bA n == bB n) then ltBits bA bB n else bB n)
    rw [ih]
    cases bA n == bB n <;> rfl

/-- The verdict below a bound decides the order of the remainders modulo the
power of two at the bound. -/
theorem ltBits_eq (bA bB : ℕ → Bool) (A B : ℕ) (hhA : ∀ i, bA i = A.testBit i)
    (hhB : ∀ i, bB i = B.testBit i) : ∀ n,
      ltBits bA bB n = decide (A % 2 ^ n < B % 2 ^ n) :=
  Nat.rec (by
      rw [Nat.pow_zero, Nat.mod_one, Nat.mod_one, decide_eq_false (Nat.lt_irrefl 0)]
      rfl)
    fun n ih ↦ by
      change (if (bA n == bB n) then ltBits bA bB n else bB n) = _
      rw [ih, hhA, hhB, mod_two_pow_succ A n, mod_two_pow_succ B n]
      have hA := Nat.mod_lt A (Nat.two_pow_pos n)
      have hB := Nat.mod_lt B (Nat.two_pow_pos n)
      cases A.testBit n <;> cases B.testBit n
      · rw [if_pos (by decide), Bool.toNat_false, Nat.mul_zero, Nat.add_zero, Nat.add_zero]
      · rw [if_neg (by decide), Bool.toNat_false, Bool.toNat_true, Nat.mul_zero, Nat.mul_one,
          Nat.add_zero, decide_eq_true (by omega)]
      · rw [if_neg (by decide), Bool.toNat_false, Bool.toNat_true, Nat.mul_zero, Nat.mul_one,
          Nat.add_zero, decide_eq_false (by omega)]
      · rw [if_pos (by decide), Bool.toNat_true, Nat.mul_one]
        by_cases h : A % 2 ^ n < B % 2 ^ n
        · rw [decide_eq_true h, decide_eq_true (by omega)]
        · rw [decide_eq_false h, decide_eq_false (by omega)]

/-- On a word holding coded numbers at the first two positions, the order test
decides their order. -/
theorem natLt_natCode (y uA rA uB rB : List Bool) (A B pA pB pC : ℕ) (huA : uA.length = pA)
    (hyA : y = uA ++ natCode A ++ rA) (huB : uB.length = pB) (hyB : y = uB ++ natCode B ++ rB)
    (hC : pC ≤ y.length) :
    natLt.sem ![y, y.drop pA, y.drop pB, y.drop pC] = boolWord (decide (A < B)) := by
  rw [natLt, sem_bitFold_pay _ _ y pA pB pC (pos_le_length y uA rA A pA huA hyA)
    (pos_le_length y uB rB B pB huB hyB) hC, iter_lt,
    ltBits_eq _ _ A B (payBit_eq_testBit y uA rA A pA huA hyA)
      (payBit_eq_testBit y uB rB B pB huB hyB),
    Nat.mod_eq_of_lt (lt_two_pow_length y uA rA A hyA),
    Nat.mod_eq_of_lt (lt_two_pow_length y uB rB B hyB)]

end Order

section Value

/-- The value, the first register. -/
@[expose] def valueV : LOf 6 := projL 6 0

/-- The power of two, the second register. -/
@[expose] def powerV : LOf 6 := projL 6 1

/-- The bit of the first number. -/
@[expose] def bitAV : LOf 6 := projL 6 2

/-- The word. -/
@[expose] def wordVV : LOf 6 := projL 6 5

/-- The update of the reading: the value raised by the power at a set bit, and
the power doubled while it is nonzero. Once the power exceeds the word's
length its end segment is empty and doubling it again would leave it so, and
the doubling is itself a recursion over the word, so the conditional takes the
count of doublings from the word's length down to its logarithm. -/
@[expose] def updValue : Fin 2 → LOf 6 :=
  ![ifFlag bitAV (addSeg powerV valueV wordVV) valueV, dblApp powerV wordVV]

/-- The base of the reading: the word for the value at zero and the word
dropped by one for the power at one. -/
@[expose] def baseValue : Fin 2 → LOf 4 := ![projL 4 0, tailAppL (projL 4 0)]

/-- The reading of the number at the first position into a counter, the word
dropped by the number. -/
@[expose] def natValue : LOf 4 := bitFold payScan baseValue updValue 0

/-- The registers of the reading after the indices below a bound: the word
dropped by the number's remainder modulo the power of two at the bound, and
the word dropped by that power. -/
theorem iter_value (y : List Bool) (bA bB bC : ℕ → Bool) (pA pB pC A : ℕ)
    (hhA : ∀ i, bA i = A.testBit i) :
    ∀ n, iter updValue y bA bB bC (regs0 baseValue y pA pB pC) n =
      ![y.drop (A % 2 ^ n), y.drop (2 ^ n)] :=
  Nat.rec (funext fun j ↦ match j with
    | 0 => by
      change (projL 4 0).sem ![y, y.drop pA, y.drop pB, y.drop pC] = y.drop (A % 2 ^ 0)
      rw [sem_projL, Nat.pow_zero, Nat.mod_one, List.drop_zero]
      rfl
    | 1 => by
      change (tailAppL (projL 4 0)).sem ![y, y.drop pA, y.drop pB, y.drop pC] = y.drop (2 ^ 0)
      rw [sem_tailAppL, sem_projL, Nat.pow_zero, List.drop_one]
      rfl)
    fun n ih ↦ by
      funext j
      match j with
      | 0 =>
        change updF updValue y (iter updValue y bA bB bC (regs0 baseValue y pA pB pC) n) _ _ _ 0 =
          y.drop (A % 2 ^ (n + 1))
        rw [ih]
        unfold updF
        change (ifFlag bitAV (addSeg powerV valueV wordVV) valueV).sem _ = _
        rw [sem_ifFlag _ _ _ _ (bA n) rfl, hhA, mod_two_pow_succ]
        cases A.testBit n
        · rw [Bool.toNat_false, Nat.mul_zero, Nat.add_zero]
          rfl
        · rw [Bool.toNat_true, Nat.mul_one]
          exact sem_addSeg powerV valueV wordVV _ y (2 ^ n) (A % 2 ^ n) rfl rfl rfl
      | 1 =>
        change updF updValue y (iter updValue y bA bB bC (regs0 baseValue y pA pB pC) n) _ _ _ 1 =
          y.drop (2 ^ (n + 1))
        rw [ih]
        unfold updF
        change (dblApp powerV wordVV).sem _ = _
        rw [sem_dblApp]
        change dbl.sem ![y.drop (2 ^ n), y] = _
        rw [sem_dbl_drop, Nat.pow_succ, Nat.mul_comm]

/-- On a word holding a coded number at the first position, the reading is
the word dropped by the number. -/
theorem natValue_natCode (y uA rA : List Bool) (A pA pB pC : ℕ) (huA : uA.length = pA)
    (hyA : y = uA ++ natCode A ++ rA) (hB : pB ≤ y.length) (hC : pC ≤ y.length) :
    natValue.sem ![y, y.drop pA, y.drop pB, y.drop pC] = y.drop A := by
  rw [natValue, sem_bitFold_pay _ _ y pA pB pC (pos_le_length y uA rA A pA huA hyA) hB hC,
    iter_value y _ _ _ pA pB pC A (payBit_eq_testBit y uA rA A pA huA hyA), Matrix.cons_val_zero,
    Nat.mod_eq_of_lt (lt_two_pow_length y uA rA A hyA)]

end Value


end

end Geb.SizeBounded.Logspace.WTree.NumArith
