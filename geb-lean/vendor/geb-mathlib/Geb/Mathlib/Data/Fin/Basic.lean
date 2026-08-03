/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Mathlib.Data.Nat.Notation

/-!
# Choice-free division, remainder and pairing on `Fin`

Batteries' `Fin.divNat` proves its bound through
`Nat.div_lt_of_lt_mul`, which depends on `Classical.choice`. The
three operations here are choice-free counterparts of `Fin.divNat`,
`Fin.modNat` and `Fin.mkDivMod`, together with the round trips
exhibiting them as a bijection `Fin m × Fin n ≃ Fin (m * n)`.

## Main definitions

* `Fin.divNatC`, `Fin.modNatC` — the quotient and remainder of an
  index of `Fin (m * n)`.
* `Fin.pairC` — the index of `Fin (m * n)` with given quotient and
  remainder, the counterpart of `Fin.mkDivMod`.

## Main statements

* `Fin.divNatC_pairC`, `Fin.modNatC_pairC`,
  `Fin.pairC_divNatC_modNatC` — the three round trips.

## Implementation notes

`Fin.modNat` and `Fin.mkDivMod` depend on no axiom outside `propext`,
so `Fin.modNatC` and `Fin.pairC` are present for uniformity rather
than necessity. Both round trips stated over `Fin.divNat` inherit its
dependence on `Classical.choice`, so a family mixing the Batteries
declarations in would still rebuild two of the three round trips;
the three here are stated over one pairing throughout. `Fin.pairC a b` is
`a * n + b` where `Fin.mkDivMod a b` is `n * a + b`, the same pairing
with the multiplication commuted.

`Nat`'s division and order API interleaves choice-dependent lemmas
with choice-free ones under no separating convention of name or
namespace: `Nat.div_lt_of_lt_mul` and `Nat.lt_of_mul_lt_mul_left`
depend on `Classical.choice` while `Nat.div_mul_le_self`,
`Nat.add_mul_div_right` and `Nat.div_add_mod'` do not. The bound
proofs below therefore route through `omega` over hypotheses named
individually, or through case analysis on `Nat.lt_or_ge`, rather than
through whichever lemma states the bound directly.

The upstream target of this module is Batteries rather than mathlib4,
the declarations it replaces being Batteries declarations; where such
content belongs is `TODO.md` § Upstream destination of core- and
Batteries-targeted content.

## Tags

fin, division, remainder, pairing, choice-free
-/

@[expose] public section

namespace Fin

/-- The quotient of an index of `Fin (m * n)` by `n`, choice-free
(unlike `Fin.divNat`). -/
def divNatC {m n : ℕ} (i : Fin (m * n)) : Fin m :=
  ⟨i / n, by
    rcases Nat.lt_or_ge ((i : ℕ) / n) m with h | h
    · exact h
    · have h3 : (i : ℕ) / n * n < m * n :=
        Nat.lt_of_le_of_lt (Nat.div_mul_le_self i n) i.isLt
      have h5 : m * n ≤ (i : ℕ) / n * n := Nat.mul_le_mul_right n h
      omega⟩

/-- The remainder of an index of `Fin (m * n)` modulo `n`, the
counterpart of `Fin.modNat` over `Fin.pairC`. -/
def modNatC {m n : ℕ} (i : Fin (m * n)) : Fin n :=
  ⟨i % n, Nat.mod_lt _ (by
    have h := i.isLt
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · omega
    · exact hn)⟩

/-- The index of `Fin (m * n)` with quotient `a` and remainder `b`,
the counterpart of `Fin.mkDivMod`. -/
def pairC {m n : ℕ} (a : Fin m) (b : Fin n) : Fin (m * n) :=
  ⟨a * n + b, by
    have h1 : ((a : ℕ) + 1) * n ≤ m * n := Nat.mul_le_mul_right n a.isLt
    have h2 : ((a : ℕ) + 1) * n = a * n + n := by rw [Nat.add_mul, Nat.one_mul]
    have h3 := b.isLt
    omega⟩

/-- The quotient of a pairing is its first component. -/
@[simp] theorem divNatC_pairC {m n : ℕ} (a : Fin m) (b : Fin n) :
    divNatC (pairC a b) = a := by
  apply Fin.ext
  change ((a : ℕ) * n + b) / n = (a : ℕ)
  rw [Nat.add_comm, Nat.add_mul_div_right _ _
      (Nat.lt_of_le_of_lt (Nat.zero_le _) b.isLt),
    Nat.div_eq_of_lt b.isLt, Nat.zero_add]

/-- The remainder of a pairing is its second component. -/
@[simp] theorem modNatC_pairC {m n : ℕ} (a : Fin m) (b : Fin n) :
    modNatC (pairC a b) = b := by
  apply Fin.ext
  change ((a : ℕ) * n + b) % n = (b : ℕ)
  rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt b.isLt]

/-- Pairing an index's quotient with its remainder recovers it. -/
@[simp] theorem pairC_divNatC_modNatC {m n : ℕ} (i : Fin (m * n)) :
    pairC (divNatC i) (modNatC i) = i := by
  apply Fin.ext
  change (i : ℕ) / n * n + (i : ℕ) % n = (i : ℕ)
  exact Nat.div_add_mod' i n

end Fin
