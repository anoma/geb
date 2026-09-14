/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Mathlib.Data.Nat.Size
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Data.List.MinMax
public import Mathlib.Order.Nat
public import Geb.Mathlib.Data.Vector.OfFn

set_option doc.verso true

/-!
# Non-size-increasing numerical functions

The numerical semantics of Mazzanti's algebra {lit}`S(sbs₀, sbs₁)` use binary
length, including length zero for the number zero. Non-size-increase permits a
constant cutoff: the output length is bounded by the maximum input length or
that cutoff, whichever is larger. This is stronger than a general linear bound.

## Main definitions

* {lit}`NonSizeIncreasing` is the size condition of Section 2.
* {lit}`sizeBoundedSucc` is the size-bounded binary successor.
* {lit}`simultaneousRec` implements simultaneous recursion on binary notation.

## Main statements

* {lit}`bounded_comp` and {lit}`bounded_simultaneousRec` prove the size closure
  properties used in Lemma 2.1, with explicit cutoffs.

## Implementation notes

The cutoff is a metatheoretic invariant, not a recursion bound supplied by the
programmer. Recursion uses {name}`Nat.binaryRec` with a vector of simultaneous
results. The zero/even-zero ambiguity is handled by the same guard as the paper.
Arity zero is allowed for constant bases of unary recursions.

These are size theorems. They do not establish a Turing-machine time or space bound.

## References

* \[Mazzanti2016\], Section 2 and Lemma 2.1.

## Tags

implicit complexity, non-size-increasing function, simultaneous recursion
-/

@[expose] public section

namespace Geb.Mazzanti

/-- Numerical functions of a fixed finite arity. -/
abbrev Sem (n : ℕ) := (Fin n → ℕ) → ℕ

/-- Maximum of a finite tuple of natural numbers, with zero for an empty tuple. -/
def maxValue {n : ℕ} (x : Fin n → ℕ) : ℕ := (List.ofFn x).foldr max 0

/-- Each tuple entry is at most its maximum. -/
theorem le_maxValue {n : ℕ} (x : Fin n → ℕ) (i : Fin n) : x i ≤ maxValue x :=
  List.le_max_of_le (List.mem_ofFn.mpr ⟨i, rfl⟩) (Nat.le_refl _)

/-- A bound on every tuple entry bounds its maximum. -/
theorem maxValue_le {n : ℕ} {x : Fin n → ℕ} {L : ℕ}
    (h : ∀ i, x i ≤ L) : maxValue x ≤ L :=
  List.max_le_of_forall_le _ _ (fun _ hi ↦ by obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hi; exact h i)

/-- The largest binary length of an argument, or zero at arity zero. -/
def inputSize {n : ℕ} (x : Fin n → ℕ) : ℕ := maxValue fun i ↦ (x i).size

/-- Each argument length is bounded by the largest argument length. -/
theorem size_le_inputSize {n : ℕ} (x : Fin n → ℕ) (i : Fin n) :
    (x i).size ≤ inputSize x := le_maxValue (fun j ↦ (x j).size) i

/-- A uniform bound on argument lengths bounds their maximum. -/
theorem inputSize_le {n : ℕ} {x : Fin n → ℕ} {L : ℕ}
    (h : ∀ i, (x i).size ≤ L) : inputSize x ≤ L :=
  maxValue_le h

/-- A function preserves every common length bound above its fixed cutoff. -/
def Bounded {n : ℕ} (f : Sem n) (k : ℕ) : Prop :=
  ∀ L, k ≤ L → ∀ x, (∀ i, (x i).size ≤ L) → (f x).size ≤ L

/-- Mazzanti's non-size-increase permits a fixed constant cutoff. -/
def NonSizeIncreasing {n : ℕ} (f : Sem n) : Prop :=
  ∃ k, ∀ x, (f x).size ≤ max (inputSize x) k

/-- The uniform-bound formulation is equivalent to the paper's maximum bound. -/
theorem nonSizeIncreasing_iff {n : ℕ} {f : Sem n} :
    NonSizeIncreasing f ↔ ∃ k, Bounded f k := by
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨k, fun L hL x hx ↦ (hk x).trans (max_le (inputSize_le hx) hL)⟩
  · rintro ⟨k, hk⟩
    exact ⟨k, fun x ↦ hk _ (Nat.le_max_right _ _) x
      (fun i ↦ (size_le_inputSize x i).trans (Nat.le_max_left _ _))⟩

/-- Binary successor when its result fits the second argument's binary length;
otherwise the first argument is returned unchanged. -/
def sizeBoundedSucc (b : Bool) (x y : ℕ) : ℕ :=
  if (Nat.bit b x).size ≤ y.size then Nat.bit b x else x

/-- Size-bounded successor preserves every common input length bound. -/
theorem size_sizeBoundedSucc_le (b : Bool) (x y L : ℕ)
    (hx : x.size ≤ L) (hy : y.size ≤ L) : (sizeBoundedSucc b x y).size ≤ L := by
  unfold sizeBoundedSucc
  split
  · next h => exact h.trans hy
  · exact hx

/-- Substitution preserves a common cutoff for the head and all arguments. -/
theorem bounded_comp {a b : ℕ} {h : Sem b} {g : Fin b → Sem a} {k : ℕ}
    (hh : Bounded h k) (hg : ∀ i, Bounded (g i) k) :
    Bounded (fun x ↦ h (fun i ↦ g i x)) k :=
  fun L hL x hx ↦ hh L hL _ (fun i ↦ hg i L hL x hx)

/-- Increasing the fixed cutoff preserves the uniform bound. -/
theorem Bounded.mono {n : ℕ} {f : Sem n} {k l : ℕ} (h : Bounded f k) (hkl : k ≤ l) :
    Bounded f l := fun L hL ↦ h L (hkl.trans hL)

/-- Simultaneous recursion, with step arguments ordered as predecessor,
parameters, and the vector of previous results, as in Section 2. -/
def simultaneousRec {a b : ℕ} (g : Fin b → Sem a)
    (h : Bool → Fin b → Sem (a + b + 1)) (x : ℕ) (y : Fin a → ℕ) : Fin b → ℕ :=
  (Nat.binaryRec (motive := fun _ ↦ Vector ℕ b) (Vector.ofFnC fun j ↦ g j y)
    (fun bit n previous ↦ Vector.ofFnC fun j ↦
      h bit j (Fin.cons n (Fin.append y previous.get))) x).get

/-- The base equation of simultaneous recursion. -/
@[simp] theorem simultaneousRec_zero {a b : ℕ} (g : Fin b → Sem a)
    (h : Bool → Fin b → Sem (a + b + 1)) (y : Fin a → ℕ) :
    simultaneousRec g h 0 y = fun j ↦ g j y :=
  funext fun j ↦ Vector.get_ofFnC (fun j ↦ g j y) j

/-- The step equation excludes the noncanonical even successor of zero. -/
theorem simultaneousRec_bit {a b : ℕ} (g : Fin b → Sem a)
    (h : Bool → Fin b → Sem (a + b + 1)) (bit : Bool) (x : ℕ)
    (hx : x = 0 → bit = true) (y : Fin a → ℕ) :
    simultaneousRec g h (Nat.bit bit x) y =
      fun j ↦ h bit j (Fin.cons x (Fin.append y (simultaneousRec g h x y))) := by
  unfold simultaneousRec
  rw [Nat.binaryRec_eq bit x (Or.inr hx)]
  exact funext fun j ↦ Vector.get_ofFnC _ j

/-- A vector of parameters followed by a vector of results preserves their common bound. -/
theorem size_append_le {a b : ℕ} {x : Fin a → ℕ} {y : Fin b → ℕ} {L : ℕ}
    (hx : ∀ i, (x i).size ≤ L) (hy : ∀ i, (y i).size ≤ L) :
    ∀ i, (Fin.append x y i).size ≤ L := by
  intro i
  exact Fin.addCases (fun j ↦ by simpa using hx j) (fun j ↦ by simpa using hy j) i

/-- All simultaneous results preserve a common cutoff of the base and step functions. -/
theorem size_simultaneousRec_le {a b : ℕ} {g : Fin b → Sem a}
    {h : Bool → Fin b → Sem (a + b + 1)} {k L : ℕ}
    (hg : ∀ j, Bounded (g j) k) (hh : ∀ bit j, Bounded (h bit j) k)
    (hk : k ≤ L) (y : Fin a → ℕ) (hy : ∀ i, (y i).size ≤ L) (x : ℕ) :
    x.size ≤ L → ∀ j, (simultaneousRec g h x y j).size ≤ L := by
  refine Nat.binaryRec' (motive := fun x ↦ x.size ≤ L →
    ∀ j, (simultaneousRec g h x y j).size ≤ L) ?_ ?_ x
  · intro _ j
    rw [simultaneousRec_zero]
    exact hg j L hk y hy
  · intro bit n hn ih hsize j
    have hpred : n.size ≤ L := by
      rw [Nat.size_bit (Nat.bit_ne_zero_iff.mpr hn)] at hsize
      omega
    rw [simultaneousRec_bit g h bit n hn]
    apply hh bit j L hk
    exact Fin.cases hpred (size_append_le hy (ih hpred))

/-- Each component of simultaneous recursion is non-size-increasing with the common cutoff. -/
theorem bounded_simultaneousRec {a b : ℕ} {g : Fin b → Sem a}
    {h : Bool → Fin b → Sem (a + b + 1)} {k : ℕ}
    (hg : ∀ j, Bounded (g j) k) (hh : ∀ bit j, Bounded (h bit j) k) (j : Fin b) :
    Bounded (fun x ↦ simultaneousRec g h (x 0) (Fin.tail x) j) k :=
  fun _ hk x hx ↦ size_simultaneousRec_le hg hh hk (Fin.tail x)
    (fun i ↦ hx i.succ) (x 0) (hx 0) j

end Geb.Mazzanti
