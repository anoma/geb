/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.SizeBounded.Logspace.WTree.NumArith

set_option doc.verso true in
/-!
# Checking a numeral against a sum

An instance of the lockstep fold over the bits of numerals,
{name}`Geb.SizeBounded.Logspace.WTree.BitFold.bitFold`, that checks the
number at the third position against the sum of the numbers at the first two
and a carry in: a ripple-carry adder whose registers are a flag, conjoined at
each index with the agreement of the third number's bit with the sum bit,
and the carry, which is the majority of the two bits and the carry before.
The check accepts when the flag is set and the carry out is clear.

# Main definitions

* {lit}`xor3`, {lit}`maj` — the sum bit and the carry out of three bits.
* {lit}`natSum` — the check, of arity four, with the carry in a parameter of
  the expression.

# Main statements

* {lit}`sum_inv` — the invariant of the adder over the indices: the carry
  accounts for the remainders, and the flag holds exactly when the third
  number's remainder is the sum's.
* {lit}`natSum_natCode` — on a word holding coded numbers at the three
  positions, the check decides whether the third is the sum of the first two
  and the carry in.

# References

* \[Kristiansen2005\]

# Tags

logspace, binary numeral, addition, ripple carry
-/

set_option doc.verso true

namespace Geb.SizeBounded.Logspace.WTree.NumSum

open Numeral BitFold NumExpr NumArith

public section

/-- The sum bit of three bits. -/
@[expose] def xor3 (a b c : Bool) : Bool := decide ((a.toNat + b.toNat + c.toNat) % 2 = 1)

/-- The carry out of three bits. -/
@[expose] def maj (a b c : Bool) : Bool := decide (2 ≤ a.toNat + b.toNat + c.toNat)

/-- The sum bit as a number is the remainder of the bits' sum. -/
theorem xor3_toNat (a b c : Bool) : (xor3 a b c).toNat = (a.toNat + b.toNat + c.toNat) % 2 := by
  cases a <;> cases b <;> cases c <;> rfl

/-- The carry out as a number is the quotient of the bits' sum. -/
theorem maj_toNat (a b c : Bool) : (maj a b c).toNat = (a.toNat + b.toNat + c.toNat) / 2 := by
  cases a <;> cases b <;> cases c <;> rfl

/-- A bit agrees with the sum bit exactly when, as numbers, it is the
remainder of the bits' sum. -/
theorem beq_xor3 (d a b c : Bool) :
    (d == xor3 a b c) = decide (d.toNat = (a.toNat + b.toNat + c.toNat) % 2) := by
  cases d <;> cases a <;> cases b <;> cases c <;> rfl

/-- The flag, the first register. -/
@[expose] def okV : LOf 6 := projL 6 0

/-- The carry, the second register. -/
@[expose] def carryV : LOf 6 := projL 6 1

/-- The bit of the first number. -/
@[expose] def bitAS : LOf 6 := projL 6 2

/-- The bit of the second number. -/
@[expose] def bitBS : LOf 6 := projL 6 3

/-- The bit of the third number. -/
@[expose] def bitCS : LOf 6 := projL 6 4

/-- The update of the adder: the flag conjoined with the agreement of the
third bit with the sum bit, and the carry out. -/
@[expose] def updSum : Fin 2 → LOf 6 :=
  ![andOkAt okV (tt2 bitCS (tt3 bitAS bitBS carryV xor3) (· == ·)), tt3 bitAS bitBS carryV maj]

/-- The base of the adder: the flag set and the carry in. -/
@[expose] def baseSum (cin : Bool) : Fin 2 → LOf 4 := ![constL 4 [true], flagK 4 cin]

/-- The check: the flag after the fold, when the carry out is clear. -/
@[expose] def natSum (cin : Bool) : LOf 4 :=
  cond4L (bitFold payScan (baseSum cin) updSum 1) (bitFold payScan (baseSum cin) updSum 0)
    (constL 4 [])
    (constL 4 [])

/-- The flag and the carry after the indices below a bound. -/
@[expose] def sumRegs (bA bB bC : ℕ → Bool) (cin : Bool) : ℕ → Bool × Bool :=
  Nat.rec (true, cin) fun i r ↦
    (r.1 && (bC i == xor3 (bA i) (bB i) r.2), maj (bA i) (bB i) r.2)

/-- The registers of the adder after the indices below a bound. -/
theorem iter_sum (y : List Bool) (bA bB bC : ℕ → Bool) (pA pB pC : ℕ) (cin : Bool) : ∀ n,
    iter updSum y bA bB bC (regs0 (baseSum cin) y pA pB pC) n =
      ![boolWord (sumRegs bA bB bC cin n).1, boolWord (sumRegs bA bB bC cin n).2] :=
  Nat.rec (funext fun j ↦ match j with | 0 => rfl | 1 => rfl) fun n ih ↦ by
    funext j
    match j with
    | 0 =>
      change updF updSum y (iter updSum y bA bB bC (regs0 (baseSum cin) y pA pB pC) n) _ _ _ 0 = _
      rw [ih]
      unfold updF
      change (andOkAt okV (tt2 bitCS (tt3 bitAS bitBS carryV xor3) (· == ·))).sem _ = _
      rw [andOkAt, sem_cond4L, sem_tt2 _ _ _ _ (bC n) _ rfl
        (sem_tt3 _ _ _ _ _ (bA n) (bB n) (sumRegs bA bB bC cin n).2 rfl rfl rfl), sem_constL]
      change cond4Sem (boolWord (sumRegs bA bB bC cin n).1) [] _ _ = _
      rw [cond4Sem_boolWord]
      rfl
    | 1 =>
      change updF updSum y (iter updSum y bA bB bC (regs0 (baseSum cin) y pA pB pC) n) _ _ _ 1 = _
      rw [ih]
      unfold updF
      exact sem_tt3 _ _ _ _ _ (bA n) (bB n) (sumRegs bA bB bC cin n).2 rfl rfl rfl

/-- The remainder of a sum modulo a number is the remainder of the sum of the
remainders. -/
theorem add_add_mod (A B c m : ℕ) : (A + B + c) % m = (A % m + B % m + c) % m := by
  have hA := Nat.div_add_mod A m
  have hB := Nat.div_add_mod B m
  rw [show A + B + c = A % m + B % m + c + m * (A / m + B / m) by rw [Nat.mul_add]; omega,
    Nat.add_mul_mod_self_left]

/-- One index of the adder, as arithmetic on the remainders below a power of
two: the carry out accounts for the remainders one bit longer, and the flag
conjoined with the agreement of the third bit with the sum bit holds exactly
when the third number's longer remainder is the sum's. -/
theorem adder_step (P AP BP CP SP cin : ℕ) (hAl : AP < P) (hBl : BP < P) (hCl : CP < P)
    (hSl : SP < P) (hcin : cin ≤ 1) (a b c cy s : Bool) (t : ℕ) (ht : t < 2)
    (ih1 : AP + BP + cin = SP + P * cy.toNat)
    (hdm : 2 * P * t + (SP + P * s.toNat) = AP + P * a.toNat + (BP + P * b.toNat) + cin)
    (ok : Bool) (ih2 : ok = true ↔ CP = SP) :
    AP + P * a.toNat + (BP + P * b.toNat) + cin =
        SP + P * s.toNat + 2 * P * (maj a b cy).toNat ∧
      ((ok && (c == xor3 a b cy)) = true ↔ CP + P * c.toNat = SP + P * s.toNat) := by
  rw [maj_toNat, beq_xor3, Bool.and_eq_true, decide_eq_true_eq, ih2]
  rcases (show t = 0 ∨ t = 1 by omega) with rfl | rfl <;>
    cases a <;> cases b <;> cases c <;> cases cy <;> cases s <;>
    simp only [Bool.toNat_true, Bool.toNat_false] at ih1 hdm ⊢ <;>
    exact ⟨by omega, ⟨fun h ↦ by obtain ⟨h1, h2⟩ := h; first | exact h2.elim | omega,
      fun h ↦ ⟨by omega, by first | trivial | omega⟩⟩⟩

/-- The invariant of the adder over the indices: the carry accounts for the
remainders of the two numbers and the carry in against the remainder of the
sum, and the flag holds exactly when the third number's remainder is the
sum's. -/
theorem sum_inv (bA bB bC : ℕ → Bool) (A B C : ℕ) (cin : Bool)
    (hhA : ∀ i, bA i = A.testBit i) (hhB : ∀ i, bB i = B.testBit i)
    (hhC : ∀ i, bC i = C.testBit i) : ∀ n,
      A % 2 ^ n + B % 2 ^ n + cin.toNat =
          (A + B + cin.toNat) % 2 ^ n + 2 ^ n * (sumRegs bA bB bC cin n).2.toNat ∧
        ((sumRegs bA bB bC cin n).1 = true ↔ C % 2 ^ n = (A + B + cin.toNat) % 2 ^ n) :=
  Nat.rec (by
      rw [Nat.pow_zero, Nat.mod_one, Nat.mod_one, Nat.mod_one, Nat.mod_one, Nat.one_mul]
      exact ⟨rfl, ⟨fun _ ↦ rfl, fun _ ↦ rfl⟩⟩)
    fun n ih ↦ by
      obtain ⟨ih1, ih2⟩ := ih
      change A % 2 ^ (n + 1) + B % 2 ^ (n + 1) + cin.toNat =
          (A + B + cin.toNat) % 2 ^ (n + 1) + 2 ^ (n + 1) *
            (maj (bA n) (bB n) (sumRegs bA bB bC cin n).2).toNat ∧
        (((sumRegs bA bB bC cin n).1 &&
            (bC n == xor3 (bA n) (bB n) (sumRegs bA bB bC cin n).2)) = true ↔
          C % 2 ^ (n + 1) = (A + B + cin.toNat) % 2 ^ (n + 1))
      have hT : (A + B + cin.toNat) % 2 ^ (n + 1) =
          (A % 2 ^ (n + 1) + B % 2 ^ (n + 1) + cin.toNat) % 2 ^ (n + 1) := add_add_mod _ _ _ _
      have hdm := Nat.div_add_mod (A % 2 ^ (n + 1) + B % 2 ^ (n + 1) + cin.toNat) (2 ^ (n + 1))
      have ht : (A % 2 ^ (n + 1) + B % 2 ^ (n + 1) + cin.toNat) / 2 ^ (n + 1) < 2 := by
        rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)]
        have := Nat.mod_lt A (Nat.two_pow_pos (n + 1))
        have := Nat.mod_lt B (Nat.two_pow_pos (n + 1))
        have := Bool.toNat_le cin
        omega
      obtain ⟨t, htdef⟩ : ∃ t, (A % 2 ^ (n + 1) + B % 2 ^ (n + 1) + cin.toNat) / 2 ^ (n + 1) = t :=
        ⟨_, rfl⟩
      rw [htdef] at ht hdm
      rw [← hT] at hdm
      have hP1 : 2 ^ (n + 1) = 2 * 2 ^ n := by rw [Nat.pow_succ, Nat.mul_comm]
      have hAl := Nat.mod_lt A (Nat.two_pow_pos n)
      have hBl := Nat.mod_lt B (Nat.two_pow_pos n)
      have hCl := Nat.mod_lt C (Nat.two_pow_pos n)
      have hSl := Nat.mod_lt (A + B + cin.toNat) (Nat.two_pow_pos n)
      rw [mod_two_pow_succ A n, mod_two_pow_succ B n, mod_two_pow_succ (A + B + cin.toNat) n,
        hP1] at hdm
      rw [hhA, hhB, hhC, mod_two_pow_succ A n, mod_two_pow_succ B n, mod_two_pow_succ C n,
        mod_two_pow_succ (A + B + cin.toNat) n, hP1]
      exact adder_step (2 ^ n) (A % 2 ^ n) (B % 2 ^ n) (C % 2 ^ n) ((A + B + cin.toNat) % 2 ^ n)
        cin.toNat hAl hBl hCl hSl (Bool.toNat_le cin) (A.testBit n) (B.testBit n) (C.testBit n)
        (sumRegs bA bB bC cin n).2 ((A + B + cin.toNat).testBit n) t ht ih1 hdm
        (sumRegs bA bB bC cin n).1 ih2

/-- On a word holding coded numbers at the three positions, the check decides
whether the third is the sum of the first two and the carry in. -/
theorem natSum_natCode (y uA rA uB rB uC rC : List Bool) (A B C pA pB pC : ℕ) (cin : Bool)
    (huA : uA.length = pA) (hyA : y = uA ++ natCode A ++ rA) (huB : uB.length = pB)
    (hyB : y = uB ++ natCode B ++ rB) (huC : uC.length = pC) (hyC : y = uC ++ natCode C ++ rC) :
    (natSum cin).sem ![y, y.drop pA, y.drop pB, y.drop pC] =
      boolWord (decide (C = A + B + cin.toNat)) := by
  have hA := pos_le_length y uA rA A pA huA hyA
  have hB := pos_le_length y uB rB B pB huB hyB
  have hC := pos_le_length y uC rC C pC huC hyC
  rw [natSum, sem_cond4L, sem_bitFold_pay _ _ y pA pB pC hA hB hC,
    sem_bitFold_pay _ _ y pA pB pC hA hB hC, iter_sum, sem_constL]
  change cond4Sem (boolWord (sumRegs (payBit y pA) (payBit y pB) (payBit y pC) cin y.length).2)
    (boolWord (sumRegs (payBit y pA) (payBit y pB) (payBit y pC) cin y.length).1) [] [] = _
  rw [cond4Sem_boolWord_same]
  obtain ⟨inv1, inv2⟩ := sum_inv _ _ _ A B C cin (payBit_eq_testBit y uA rA A pA huA hyA)
    (payBit_eq_testBit y uB rB B pB huB hyB) (payBit_eq_testBit y uC rC C pC huC hyC) y.length
  rw [Nat.mod_eq_of_lt (lt_two_pow_length y uA rA A hyA),
    Nat.mod_eq_of_lt (lt_two_pow_length y uB rB B hyB)] at inv1
  rw [Nat.mod_eq_of_lt (lt_two_pow_length y uC rC C hyC)] at inv2
  have hCl := lt_two_pow_length y uC rC C hyC
  have hSl := Nat.mod_lt (A + B + cin.toNat) (Nat.two_pow_pos y.length)
  by_cases h : C = A + B + cin.toNat
  · rw [decide_eq_true h]
    have hS : (A + B + cin.toNat) % 2 ^ y.length = A + B + cin.toNat :=
      Nat.mod_eq_of_lt (by rw [← h]; exact hCl)
    rw [hS] at inv1 inv2
    have hcy : (sumRegs (payBit y pA) (payBit y pB) (payBit y pC) cin y.length).2 = false := by
      cases hc : (sumRegs (payBit y pA) (payBit y pB) (payBit y pC) cin y.length).2
      · rfl
      · rw [hc, Bool.toNat_true] at inv1
        have := Nat.two_pow_pos y.length
        omega
    rw [hcy, inv2.mpr h]
    rfl
  · rw [decide_eq_false h]
    cases hc : (sumRegs (payBit y pA) (payBit y pB) (payBit y pC) cin y.length).2
    · rw [hc, Bool.toNat_false, Nat.mul_zero, Nat.add_zero] at inv1
      cases hok : (sumRegs (payBit y pA) (payBit y pB) (payBit y pC) cin y.length).1
      · rfl
      · exfalso
        exact h (by rw [inv2.mp hok]; exact inv1.symm)
    · rfl

end

end Geb.SizeBounded.Logspace.WTree.NumSum
