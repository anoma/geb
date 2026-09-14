/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Mathlib.Data.Nat.Size
public import Mathlib.Tactic.Attr.Core
public import Mathlib.Tactic.Push

set_option doc.verso true

/-!
# Binary counter costs

Least-significant-bit-first increment changes an initial sequence of ones and the next zero.
The number of ones is a potential that bounds the total changes under repeated increments.
These are costs of the list algorithm; a Turing-machine bound additionally requires simulation.

## Main definitions

* {lit}`increment`: binary increment, permitting leading zeroes.
* {lit}`flips`: the number of digits changed by an increment.
* {lit}`totalFlips`: the cumulative digit changes starting at zero.

## Main statements

* {lit}`flips_add_count_increment`: the exact potential identity.
* {lit}`totalFlips_le`: at most two changes per increment, amortized.
* {lit}`flips_bits_le_succ_size`: the incremented number's binary size bounds all changed bits.
* {lit}`size_mono`: increasing counter values have nondecreasing binary size.

## Tags

binary counter, amortized complexity, potential
-/

@[expose] public section

namespace Geb.BitTree.Counter

/-- Increment a binary word whose least significant digit comes first. -/
def increment : List Bool → List Bool :=
  List.rec [true] fun b bs next ↦ if b then false :: next else true :: bs

/-- Number of bit changes, including the final zero-to-one change. -/
def flips : List Bool → ℕ :=
  List.foldr (fun b n ↦ if b then n + 1 else 1) 1

/-- Carry propagation resets an initial sequence of ones. -/
theorem increment_replicate_true_append (k : ℕ) (bs : List Bool) :
    increment (List.replicate k true ++ bs) =
      List.replicate k false ++ increment bs := by
  apply Nat.rec (motive := fun k ↦
    increment (List.replicate k true ++ bs) =
      List.replicate k false ++ increment bs) ?_ ?_ k
  · rfl
  · intro k ih
    simpa [List.replicate_succ, increment] using congrArg (false :: ·) ih

/-- Every initial one contributes one bit change before the remaining increment. -/
theorem flips_replicate_true_append (k : ℕ) (bs : List Bool) :
    flips (List.replicate k true ++ bs) = k + flips bs := by
  apply Nat.rec (motive := fun k ↦
    flips (List.replicate k true ++ bs) = k + flips bs) ?_ ?_ k
  · simp
  · intro k ih
    simp [List.replicate_succ, flips] at ih ⊢
    omega

/-- Every increment changes at least one bit. -/
theorem flips_pos (bs : List Bool) : 0 < flips bs := by
  apply List.rec (motive := fun bs ↦ 0 < flips bs) ?_ ?_ bs
  · decide
  · intro b bs ih
    cases b <;> simp_all [flips]

/-- Every bit strictly before the last changed position is one. -/
theorem getD_eq_true_of_lt_flips (bs : List Bool) (i : ℕ) (h : i + 1 < flips bs) :
    bs[i]?.getD false = true := by
  revert i
  apply List.rec (motive := fun bs ↦ ∀ i, i + 1 < flips bs →
    bs[i]?.getD false = true) ?_ ?_ bs
  · intro i hi
    simp only [flips, List.foldr_nil] at hi
    omega
  · intro b bs ih i hi
    cases b
    · simp only [flips, List.foldr_cons, Bool.false_eq_true, ↓reduceIte] at hi
      omega
    · cases i with
      | zero => rfl
      | succ i =>
        change bs[i]?.getD false = true
        apply ih
        change i + 1 + 1 < flips bs + 1 at hi
        omega

/-- The final changed position contains zero, counting blanks as zero. -/
theorem getD_last_flip (bs : List Bool) : bs[flips bs - 1]?.getD false = false := by
  apply List.rec (motive := fun bs ↦ bs[flips bs - 1]?.getD false = false) ?_ ?_ bs
  · rfl
  · intro b bs ih
    cases b
    · rfl
    · have hf := flips_pos bs
      have he : flips (true :: bs) - 1 = (flips bs - 1) + 1 := by
        change flips bs + 1 - 1 = flips bs - 1 + 1
        omega
      simpa only [he, List.getElem?_cons_succ] using ih

/-- Increment resets the initial ones, sets the following zero, and preserves later bits. -/
theorem getD_increment (bs : List Bool) (i : ℕ) :
    (increment bs)[i]?.getD false =
      if i + 1 < flips bs then false
      else if i + 1 = flips bs then true else bs[i]?.getD false := by
  revert i
  apply List.rec (motive := fun bs ↦ ∀ i,
    (increment bs)[i]?.getD false =
      if i + 1 < flips bs then false
      else if i + 1 = flips bs then true else bs[i]?.getD false) ?_ ?_ bs
  · intro i
    cases i with
    | zero => rfl
    | succ i =>
      change false = if i + 1 + 1 < 1 then false
        else if i + 1 + 1 = 1 then true else false
      simp only [show ¬i + 1 + 1 < 1 from by omega,
        show i + 1 + 1 ≠ 1 from by omega, ↓reduceIte]
  · intro b bs ih i
    cases b
    · cases i with
      | zero => rfl
      | succ i =>
        change bs[i]?.getD false = if i + 1 + 1 < 1 then false
          else if i + 1 + 1 = 1 then true else bs[i]?.getD false
        simp only [show ¬i + 1 + 1 < 1 from by omega,
          show i + 1 + 1 ≠ 1 from by omega, ↓reduceIte]
    · cases i with
      | zero =>
        have hf := flips_pos bs
        change false = if 1 < flips bs + 1 then false
          else if 1 = flips bs + 1 then true else true
        simp only [show 1 < flips bs + 1 from by omega, ↓reduceIte]
      | succ i =>
        change (increment bs)[i]?.getD false =
          if i + 1 + 1 < flips bs + 1 then false
          else if i + 1 + 1 = flips bs + 1 then true else bs[i]?.getD false
        have hlt : (i + 1 + 1 < flips bs + 1) ↔ (i + 1 < flips bs) := by
          constructor <;> intro h <;> omega
        have heq : (i + 1 + 1 = flips bs + 1) ↔ (i + 1 = flips bs) := by
          constructor <;> intro h <;> omega
        simpa only [hlt, heq] using ih i

/-- Each increment consumes one unit of potential for every trailing one it resets. -/
theorem flips_add_count_increment (bs : List Bool) :
    flips bs + (increment bs).count true = bs.count true + 2 := by
  apply List.rec (motive := fun bs ↦
    flips bs + (increment bs).count true = bs.count true + 2) ?_ ?_ bs
  · rfl
  · intro b bs ih
    cases b <;> simp_all [flips, increment] <;> omega

/-- Binary increment agrees with successor on natural numbers. -/
theorem increment_bits (n : ℕ) : increment n.bits = (n + 1).bits := by
  apply Nat.binaryRec' (motive := fun n ↦ increment n.bits = (n + 1).bits) ?_ ?_ n
  · rfl
  · intro b k hk ih
    rw [Nat.bits_append_bit k b hk]
    cases b
    · simp [increment, Nat.bit_val, Nat.bit1_bits]
    · change false :: increment k.bits = (Nat.bit true k + 1).bits
      rw [ih, Nat.bit_val]
      have he : 2 * k + true.toNat + 1 = 2 * (k + 1) := by simp; omega
      rw [he, Nat.bit0_bits (k + 1) (by omega)]

/-- Cumulative bit changes of increments from zero to the argument. -/
def totalFlips : ℕ → ℕ :=
  Nat.rec 0 fun n cost ↦ cost + flips n.bits

/-- Total changes plus the final potential equal twice the number of increments. -/
theorem totalFlips_add_count (n : ℕ) : totalFlips n + n.bits.count true = 2 * n := by
  apply Nat.rec (motive := fun n ↦ totalFlips n + n.bits.count true = 2 * n) ?_ ?_ n
  · rfl
  · intro k ih
    have h := flips_add_count_increment k.bits
    rw [increment_bits] at h
    change totalFlips k + flips k.bits + (k + 1).bits.count true = 2 * (k + 1)
    omega

/-- Binary increment changes at most two digits per increment, amortized. -/
theorem totalFlips_le (n : ℕ) : totalFlips n ≤ 2 * n := by
  have h := totalFlips_add_count n
  omega

/-- An increment visits no more than the represented digits and the first blank digit. -/
theorem flips_le_length (bs : List Bool) : flips bs ≤ bs.length + 1 := by
  apply List.rec (motive := fun bs ↦ flips bs ≤ bs.length + 1) ?_ ?_ bs
  · exact Nat.le_refl _
  · intro b bs ih
    cases b <;> simp_all [flips]

/-- Every changed digit belongs to the resulting counter representation. -/
theorem flips_le_increment_length (bs : List Bool) : flips bs ≤ (increment bs).length := by
  apply List.rec (motive := fun bs ↦ flips bs ≤ (increment bs).length) ?_ ?_ bs
  · exact Nat.le_refl _
  · intro b bs ih
    cases b <;> simp_all [flips, increment]

/-- The incremented number's binary size bounds all digits changed by the increment. -/
theorem flips_bits_le_succ_size (n : ℕ) : flips n.bits ≤ (n + 1).size := by
  have h := flips_le_increment_length n.bits
  rwa [increment_bits, Nat.size_eq_bits_len] at h

/-- A counter value has exactly its binary size in represented digits. -/
theorem length_bits (n : ℕ) : n.bits.length = n.size := Nat.size_eq_bits_len n

/-- An increment visits at most one more cell than the binary size of its argument. -/
theorem flips_bits_le (n : ℕ) : flips n.bits ≤ n.size + 1 := by
  simpa [length_bits] using flips_le_length n.bits

/-- A number below a power of two uses no more digits than that exponent. -/
theorem size_le_of_lt_pow (n w : ℕ) (h : n < 2 ^ w) : n.size ≤ w := by
  revert w
  apply Nat.binaryRec' (motive := fun n ↦ ∀ w, n < 2 ^ w → n.size ≤ w) ?_ ?_ n
  · intro w _
    simp
  · intro b k hk ih w h
    have hn : Nat.bit b k ≠ 0 := by
      cases b <;> simp_all [Nat.bit_val]
      omega
    rw [Nat.size_bit hn]
    cases w with
    | zero => simp only [Nat.pow_zero] at h; omega
    | succ w =>
      have hk' : k < 2 ^ w := by
        rw [Nat.bit_val, Nat.pow_succ] at h
        omega
      have hs := ih w hk'
      omega

/-- A number is smaller than the power of two above all its represented digits. -/
theorem lt_pow_size (n : ℕ) : n < 2 ^ n.size := by
  apply Nat.binaryRec' (motive := fun n ↦ n < 2 ^ n.size) ?_ ?_ n
  · decide
  · intro b k hk ih
    have hn : Nat.bit b k ≠ 0 := by
      cases b <;> simp_all [Nat.bit_val]
      omega
    rw [Nat.size_bit hn, Nat.pow_succ, Nat.bit_val]
    cases b <;> simp only [Bool.toNat_false, Bool.toNat_true] <;> omega

/-- Binary size is monotone in the represented natural number. -/
theorem size_mono {m n : ℕ} (h : m ≤ n) : m.size ≤ n.size := by
  have hn := lt_pow_size n
  exact size_le_of_lt_pow m n.size (by omega)

end Geb.BitTree.Counter
