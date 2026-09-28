/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
-- Modified from geb-mathlib by scripts/geb-mathlib-backport.patch.
module

public import Mathlib.Data.PFunctor.Univariate.Basic
public import Mathlib.Logic.Equiv.Defs

set_option doc.verso true in
/-!
# Depths as a W-type

The finite observations of an M-type are indexed by depth. A depth is a tree
of the polynomial with a nullary zero shape and a unary successor shape, so
the index is itself a W-type and recursion on it is {name}`WType.elim`. The
polynomial is stated at every pair of universes, so that the depths of an
M-type of a polynomial functor in universes {lit}`uA` and {lit}`uB` lie in
the same universes as that functor.

## Main definitions

* {lit}`depthSig`, {lit}`Depth`, {lit}`Depth.zero`, {lit}`Depth.succ` — the
  polynomial of depths, its W-type, and the two constructors.
* {lit}`Depth.rec` — dependent elimination on depths, computed by the fold.
* {lit}`Depth.equivNat` — the depths are the natural numbers.

## Main statements

* {lit}`Depth.induction` — induction on depths.
* {lit}`Depth.rec_zero`, {lit}`Depth.rec_succ` — the computation rules of
  dependent elimination.

## Implementation notes

Dependent elimination is derived from the non-dependent fold: the fold
computes the depth it is applied to together with the value, and the value
is transported along the proof, by the proposition-valued recursor, that the
computed depth is the given one. The comparison with {name}`Nat` is used only
to relate the construction to mathlib's approximations, which mathlib indexes
by {name}`Nat`.

## References

* \[VanDenBergDeMarchi2007\], Section 2.

## Tags

W-type, natural numbers, dependent elimination, depth
-/
set_option doc.verso true

@[expose] public section

universe u uA uB

namespace Geb.MType

/-- The polynomial of depths: zero is nullary and successor is unary. -/
def depthSig : PFunctor.{uA, uB} where
  A := ULift Bool
  B b := match b with
    | ⟨false⟩ => PEmpty
    | ⟨true⟩ => PUnit

/-- Depths, represented by well-founded unary trees. Both universes are
parameters because the base of {lit}`PFunctor.dependent` shares its universes
with the dependent part, which here is the polynomial whose M-type is built. -/
@[nolint checkUnivs]
abbrev Depth : Type (max uA uB) := depthSig.{uA, uB}.W

namespace Depth

/-- The depth with no observable layer. -/
def zero : Depth.{uA, uB} := WType.mk ⟨false⟩ PEmpty.elim

/-- One additional observable layer. -/
def succ (n : Depth.{uA, uB}) : Depth.{uA, uB} := WType.mk ⟨true⟩ fun _ ↦ n

/-- Induction on depths, by the proposition-valued recursor. -/
theorem induction {motive : Depth.{uA, uB} → Prop} (hz : motive zero)
    (hs : ∀ n, motive n → motive (succ n)) : ∀ n, motive n :=
  WType.rec fun b f ih ↦ by
    obtain ⟨b⟩ := b
    cases b with
    | false =>
      obtain rfl : f = PEmpty.elim := funext fun i ↦ nomatch i
      exact hz
    | true => exact hs (f PUnit.unit) (ih PUnit.unit)

/-- The fold computing a depth together with a dependent value at it. -/
def recData {motive : Depth.{uA, uB} → Type u} (hz : motive zero)
    (hs : ∀ n, motive n → motive (succ n)) : Depth.{uA, uB} → Sigma motive :=
  WType.elim _ fun x ↦ match x with
    | ⟨⟨false⟩, _⟩ => ⟨zero, hz⟩
    | ⟨⟨true⟩, f⟩ => ⟨succ (f PUnit.unit).1, hs (f PUnit.unit).1 (f PUnit.unit).2⟩

/-- The depth computed by {name}`recData` is its input. -/
theorem recData_fst {motive : Depth.{uA, uB} → Type u} (hz : motive zero)
    (hs : ∀ n, motive n → motive (succ n)) : ∀ n, (recData hz hs n).1 = n :=
  induction rfl fun _ ih ↦ congrArg succ ih

/-- Dependent elimination on depths: the fold {name}`recData`, followed by
transport along {name}`recData_fst`. -/
protected def rec {motive : Depth.{uA, uB} → Type u} (hz : motive zero)
    (hs : ∀ n, motive n → motive (succ n)) (n : Depth.{uA, uB}) : motive n :=
  cast (congrArg motive (recData_fst hz hs n)) (recData hz hs n).2

/-- The zero computation rule. -/
@[simp] theorem rec_zero {motive : Depth.{uA, uB} → Type u} (hz : motive zero)
    (hs : ∀ n, motive n → motive (succ n)) : Depth.rec hz hs zero = hz := rfl

/-- The successor computation rule. -/
@[simp] theorem rec_succ {motive : Depth.{uA, uB} → Type u} (hz : motive zero)
    (hs : ∀ n, motive n → motive (succ n)) (n : Depth.{uA, uB}) :
    Depth.rec hz hs (succ n) = hs n (Depth.rec hz hs n) := by
  have transport (m n : Depth.{uA, uB}) (h : m = n) (v : motive m) :
      cast (congrArg motive (congrArg succ h)) (hs m v) = hs n (cast (congrArg motive h) v) := by
    cases h
    rfl
  exact transport _ _ (recData_fst hz hs n) _

/-- The natural number a depth represents. -/
def toNat : Depth.{uA, uB} → ℕ :=
  WType.elim ℕ fun x ↦ match x with
    | ⟨⟨false⟩, _⟩ => 0
    | ⟨⟨true⟩, f⟩ => f PUnit.unit + 1

/-- The depth representing a natural number. -/
def ofNat : ℕ → Depth.{uA, uB} := Nat.rec zero fun _ ↦ succ

/-- {name}`toNat` sends the successor to the successor. -/
@[simp] theorem toNat_succ (n : Depth.{uA, uB}) : toNat (succ n) = toNat n + 1 := rfl

/-- The depths are the natural numbers. -/
def equivNat : Depth.{uA, uB} ≃ ℕ where
  toFun := toNat
  invFun := ofNat
  left_inv := induction rfl fun _ ih ↦ congrArg succ ih
  right_inv := Nat.rec rfl fun _ ih ↦ congrArg Nat.succ ih

end Depth

end Geb.MType
