/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.SizeBounded.Logspace.WTree.NumScan
public import Mathlib.Data.Nat.Bitwise

/-!
# The bits of a number, its remainders and its size

The bit at an index of a number's bits, least significant first, is the
number's bit at that index; the remainder modulo one more power of two takes
that bit; and a number whose binary size is bounded is below the power of two
at the bound. These relate the scanner's reading of a numeral's bits to the
number's arithmetic.

## Main statements

* `bits_getD_eq_testBit` — the bit at an index of the bits is the number's
  bit.
* `mod_two_pow_succ` — the remainder modulo the next power of two.
* `lt_two_pow_of_size_le` — a bound on the binary size bounds the number.
* `size_le_length_natCode` — a number's binary size is at most its code's
  length.

## Tags

binary numeral, test bit, remainder
-/

namespace Geb.SizeBounded.Logspace.WTree.Numeral

public section

/-- The bit at an index of a number's bits, least significant first, is the
number's bit at that index. -/
theorem bits_getD_eq_testBit (n i : ℕ) : n.bits.getD i false = n.testBit i := by
  rw [Nat.testBit_eq_inth, List.getI_eq_getElem?_getD, List.getD_eq_getElem?_getD]
  rfl

/-- The number with given bits is below the power of two at their count. -/
theorem fromBits_lt : ∀ bs : List Bool, fromBits bs < 2 ^ bs.length :=
  List.rec Nat.one_pos fun b bs ih ↦ by
    change Nat.bit b (fromBits bs) < 2 ^ (bs.length + 1)
    rw [Nat.bit_val, Nat.pow_succ]
    have := Bool.toNat_le b
    omega

/-- A number whose binary size is bounded is below the power of two at the
bound. -/
theorem lt_two_pow_of_size_le (n L : ℕ) (h : n.size ≤ L) : n < 2 ^ L := by
  have h1 := fromBits_lt n.bits
  rw [fromBits_bits, length_bits] at h1
  exact Nat.lt_of_lt_of_le h1 (Nat.pow_le_pow_right (by decide) h)

/-- The remainder modulo the next power of two takes the bit at the power. -/
theorem mod_two_pow_succ (x i : ℕ) :
    x % 2 ^ (i + 1) = x % 2 ^ i + 2 ^ i * (x.testBit i).toNat := by
  have hb : (x.testBit i).toNat = x / 2 ^ i % 2 := by
    rw [Nat.testBit_eq_decide_div_mod_eq]
    rcases Nat.mod_two_eq_zero_or_one (x / 2 ^ i) with h | h <;> rw [h] <;> rfl
  rw [hb]
  obtain ⟨q, hq⟩ : ∃ q, x / 2 ^ i = q := ⟨_, rfl⟩
  obtain ⟨r, hr⟩ : ∃ r, x % 2 ^ i = r := ⟨_, rfl⟩
  have h1 : 2 ^ i * q + r = x := by rw [← hq, ← hr]; exact Nat.div_add_mod x (2 ^ i)
  have h2 : 2 * (q / 2) + q % 2 = q := Nat.div_add_mod q 2
  have hrl : r < 2 ^ i := by rw [← hr]; exact Nat.mod_lt x (Nat.two_pow_pos i)
  rw [hq, hr]
  have hx : x = 2 ^ (i + 1) * (q / 2) + (r + 2 ^ i * (q % 2)) :=
    calc x = 2 ^ i * q + r := h1.symm
      _ = 2 ^ i * (2 * (q / 2) + q % 2) + r := by rw [h2]
      _ = 2 ^ (i + 1) * (q / 2) + (r + 2 ^ i * (q % 2)) := by
        rw [Nat.mul_add, ← Nat.mul_assoc, Nat.pow_succ]
        omega
  have hlt : r + 2 ^ i * (q % 2) < 2 ^ (i + 1) := by
    rw [Nat.pow_succ]
    rcases Nat.mod_two_eq_zero_or_one q with h | h <;> rw [h] <;> omega
  rw [hx, Nat.mul_add_mod, Nat.mod_eq_of_lt hlt]

/-- A number's binary size is at most its code's length. -/
theorem size_le_length_natCode (m : ℕ) : m.size ≤ (natCode m).length := by
  rw [length_natCode]
  omega

end

end Geb.SizeBounded.Logspace.WTree.Numeral
