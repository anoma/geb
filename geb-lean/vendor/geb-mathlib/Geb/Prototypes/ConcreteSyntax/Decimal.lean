/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
-- Modified from geb-mathlib by scripts/geb-mathlib-backport.patch.
module

public import Mathlib.Tactic.ToDual
public import Mathlib.Util.CompileInductive

/-!
# Decimal digits

The shortest decimal spelling of a natural number (`Geb.Csexp.decOf`) and the value of a
spelling (`Geb.Csexp.digitsVal`), with the round trip between them
(`Geb.Csexp.digitsVal_decOf`), as the lengths of the canonical encoding of [RFC9804] are
written. The digits are computed by hand, every route to a decimal round trip in mathlib and in
core depending on `Classical.choice`.

## Main definitions

* `Geb.Csexp.decOf` — the shortest decimal spelling of a number.
* `Geb.Csexp.digitsVal` — the value of a decimal spelling.

## Main statements

* `Geb.Csexp.digitsVal_decOf` — the value of a number's spelling is the number.

## References

* [RFC9804]

## Tags

decimal, digits, S-expression
-/

@[expose] public section

namespace Geb.Csexp


/-- The ASCII character for a decimal digit; meaningful for `d < 10`. -/
def digitChar (d : Nat) : Char := Char.ofNat (48 + d)

/-- The decimal value of an ASCII digit character. -/
def charDigit (c : Char) : Option Nat :=
  if 48 ≤ c.toNat && c.toNat ≤ 57 then some (c.toNat - 48) else none

theorem charDigit_digitChar (d : Nat) (h : d < 10) :
    charDigit (digitChar d) = some d := by
  revert h; revert d; decide

theorem mapM_charDigit_digitChar : ∀ ds : List Nat, (∀ d ∈ ds, d < 10) →
    (ds.map digitChar).mapM charDigit = some ds :=
  List.rec (motive := fun ds ↦ (∀ d ∈ ds, d < 10) →
      (ds.map digitChar).mapM charDigit = some ds)
    (fun _ ↦ rfl)
    (fun d ds ih h ↦ by
      have hd : d < 10 := h d (by simp)
      have ht : ∀ x ∈ ds, x < 10 := fun x hx ↦ h x (by simp [hx])
      simp [List.mapM_cons, charDigit_digitChar d hd, ih ht])

/-- The value of a little-endian decimal digit list. -/
def ofLE : List Nat → Nat := List.rec 0 fun d _ ih ↦ d + 10 * ih

@[simp] theorem ofLE_nil : ofLE [] = 0 := rfl

@[simp] theorem ofLE_cons (d : Nat) (ds : List Nat) :
    ofLE (d :: ds) = d + 10 * ofLE ds := rfl

/-- Little-endian decimal digits of `n`, on an explicit recursion bound.
Each step divides by ten, so `n` itself is always a sufficient bound. -/
def digitsLEAux : Nat → Nat → List Nat :=
  Nat.rec (fun _ ↦ []) fun _ ih n ↦ if n = 0 then [] else n % 10 :: ih (n / 10)

@[simp] theorem digitsLEAux_zero (n : Nat) : digitsLEAux 0 n = [] := rfl

theorem digitsLEAux_succ (f n : Nat) :
    digitsLEAux (f + 1) n =
      if n = 0 then [] else n % 10 :: digitsLEAux f (n / 10) := rfl

/-- Little-endian decimal digits. Hand-rolled because every route to a
decimal round trip in mathlib and in core depends on `Classical.choice`;
see the module docstring's implementation notes. -/
def digitsLE (n : Nat) : List Nat := digitsLEAux n n

theorem ofLE_digitsLEAux : ∀ f n : Nat, n ≤ f → ofLE (digitsLEAux f n) = n :=
  Nat.rec (motive := fun f ↦ ∀ n : Nat, n ≤ f → ofLE (digitsLEAux f n) = n)
    (fun n hn ↦ by
      simp only [digitsLEAux_zero, ofLE_nil]
      exact (Nat.le_zero.mp hn).symm)
    (fun f ih n hn ↦ by
      rw [digitsLEAux_succ]
      split
      next h => simp [h]
      next h => rw [ofLE_cons, ih (n / 10) (by omega)]; omega)

theorem ofLE_digitsLE (n : Nat) : ofLE (digitsLE n) = n :=
  ofLE_digitsLEAux n n (Nat.le_refl n)

theorem digitsLEAux_lt : ∀ f n : Nat, ∀ d ∈ digitsLEAux f n, d < 10 :=
  Nat.rec (motive := fun f ↦ ∀ n : Nat, ∀ d ∈ digitsLEAux f n, d < 10)
    (fun n d hd ↦ by simp at hd)
    (fun f ih n d hd ↦ by
      rw [digitsLEAux_succ] at hd
      split at hd
      next => simp at hd
      next =>
        rcases List.mem_cons.mp hd with rfl | hd'
        · omega
        · exact ih (n / 10) d hd')

theorem digitsLE_lt (n : Nat) : ∀ d ∈ digitsLE n, d < 10 := digitsLEAux_lt n n

theorem digitsLE_ne_nil {n : Nat} (h : n ≠ 0) : digitsLE n ≠ [] := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  simp [digitsLE, digitsLEAux_succ]

/-- Shortest-form decimal, big-endian, `"0"` for zero. -/
def decOf (n : Nat) : List Char :=
  if n = 0 then ['0'] else (digitsLE n).reverse.map digitChar

/-- The value of a big-endian decimal digit string, or `none` if any
character is not a digit. Leading zeros are accepted, and so is the empty
string, whose value is `0`: the parser may admit more than the printer
emits, since the retraction law constrains only the composite. -/
def digitsVal (cs : List Char) : Option Nat :=
  (cs.mapM charDigit).map fun l ↦ ofLE l.reverse

/-- The decimal round trip: reading back a shortest-form spelling
recovers the number. This is what the retraction law rests on at the
label level. -/
theorem digitsVal_decOf (n : Nat) : digitsVal (decOf n) = some n := by
  unfold decOf digitsVal
  by_cases h : n = 0
  · subst h; decide
  · have hlt : ∀ d ∈ (digitsLE n).reverse, d < 10 := by
      intro d hd
      exact digitsLE_lt n d (List.mem_reverse.mp hd)
    rw [if_neg h, mapM_charDigit_digitChar _ hlt]
    simp [ofLE_digitsLE]

theorem decOf_all_digits (n : Nat) : ∀ c ∈ decOf n, (charDigit c).isSome := by
  intro c hc
  unfold decOf at hc
  by_cases h : n = 0
  · subst h; rw [if_pos rfl, List.mem_singleton] at hc; subst hc; decide
  · rw [if_neg h] at hc
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc
    have : d < 10 := digitsLE_lt n d (List.mem_reverse.mp hd)
    simp [charDigit_digitChar d this]

theorem decOf_ne_nil (n : Nat) : decOf n ≠ [] := by
  unfold decOf
  by_cases h : n = 0
  · subst h; simp
  · rw [if_neg h]
    simp [digitsLE_ne_nil h]

end Geb.Csexp

end
