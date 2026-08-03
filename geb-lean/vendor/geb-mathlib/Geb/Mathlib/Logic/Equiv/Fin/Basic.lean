/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Mathlib.Data.Fin.Basic
public import Mathlib.Data.Fin.Tuple.Basic

/-!
# Choice-free product and exponential encodings of `Fin`

mathlib's `finProdFinEquiv : Fin m × Fin n ≃ Fin (m * n)` and
`finFunctionFinEquiv : (Fin n → Fin m) ≃ Fin (m ^ n)` both depend on
`Classical.choice`, the first through `Fin.divNat` and the second
through the `Finset.sum` lemmas its round trips run on. The two
equivalences here are their choice-free counterparts.

## Main definitions

* `finProdFinEquivC` — the product encoding.
* `finFunctionFinEquivC` — the exponential encoding.
* `Fin.funEncodeC`, `Fin.funDecodeC` — its two directions under
  names the `simp` lemmas are stated over.

## Main statements

* `Fin.funDecodeC_funEncodeC`, `Fin.funEncodeC_funDecodeC` — the two
  round trips of the exponential encoding.

## Implementation notes

The exponential is built by recursion on the arity over the product
encoding rather than by base-`m` digit arithmetic: the digit
construction's round trips are `Finset.sum` lemmas, each a separate
choice audit, and mathlib's version of that construction is the one
that depends on `Classical.choice`. The recursion is an explicit
`Nat.rec` at the motive `fun k ↦ (Fin k → Fin m) ≃ Fin (m ^ k)`: what
recurses is the equivalence itself, whose type varies with the arity,
and the successor step composes the equivalence at `k` with
`finProdFinEquivC`.

`Fin.funDecodeC` returns a function, so the recursion building the
equivalence is re-run on each application of the decoded function;
binding the equivalence above the lambda would run it once.

## Tags

fin, equiv, product, exponential, choice-free
-/

@[expose] public section

/-- The choice-free product encoding, assembled from `Fin.pairC`,
`Fin.divNatC` and `Fin.modNatC` (unlike mathlib's
`finProdFinEquiv`, which depends on `Classical.choice`). -/
def finProdFinEquivC {m n : ℕ} : Fin m × Fin n ≃ Fin (m * n) where
  toFun p := Fin.pairC p.1 p.2
  invFun i := (Fin.divNatC i, Fin.modNatC i)
  left_inv p := Prod.ext (Fin.divNatC_pairC p.1 p.2) (Fin.modNatC_pairC p.1 p.2)
  right_inv i := Fin.pairC_divNatC_modNatC i

/-- The choice-free exponential encoding, by recursion on the arity
over `finProdFinEquivC` (unlike mathlib's `finFunctionFinEquiv`,
whose base-`m` digit round trips depend on `Classical.choice`). -/
def finFunctionFinEquivC {m n : ℕ} : (Fin n → Fin m) ≃ Fin (m ^ n) :=
  Nat.rec (motive := fun k ↦ (Fin k → Fin m) ≃ Fin (m ^ k))
    (((Equiv.equivPUnit (Fin 0 → Fin m)).trans finOneEquiv.symm).trans
      (finCongr (Nat.pow_zero m).symm))
    (fun k ih ↦
      (((Fin.consEquiv (fun _ : Fin (k + 1) ↦ Fin m)).symm.trans
        (Equiv.prodCongr (Equiv.refl (Fin m)) ih)).trans finProdFinEquivC).trans
        (finCongr (Nat.pow_succ' (m := m) (n := k)).symm))
    n

namespace Fin

/-- Encode a function `Fin n → Fin m` as an index of `Fin (m ^ n)`:
the forward direction of `finFunctionFinEquivC`. -/
def funEncodeC {m n : ℕ} (g : Fin n → Fin m) : Fin (m ^ n) :=
  finFunctionFinEquivC g

/-- Decode an index of `Fin (m ^ n)` as a function `Fin n → Fin m`:
the inverse direction of `finFunctionFinEquivC`. -/
def funDecodeC {m n : ℕ} (i : Fin (m ^ n)) : Fin n → Fin m :=
  finFunctionFinEquivC.symm i

/-- Decoding an encoded function recovers it. -/
@[simp] theorem funDecodeC_funEncodeC {m n : ℕ} (g : Fin n → Fin m) :
    funDecodeC (funEncodeC g) = g :=
  finFunctionFinEquivC.left_inv g

/-- Encoding a decoded index recovers it. -/
@[simp] theorem funEncodeC_funDecodeC {m n : ℕ} (i : Fin (m ^ n)) :
    funEncodeC (funDecodeC i) = i :=
  finFunctionFinEquivC.right_inv i

end Fin
