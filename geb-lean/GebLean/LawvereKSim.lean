import Mathlib.Data.Fin.Basic
import Mathlib.Data.Nat.Basic

/-!
# Lawvere theory of the K^sim hierarchy: term language

This module defines `KMor1 : ℕ → Type`, the type family of
K^sim single-output morphisms (one per arity), together with
`KMorN`, the multi-output Lawvere-theory wrapper.  The level
function `KMor1.level` and its `KMorN`-counterpart
`KMor1.levelN` are also defined here.  Interpretation into
`ℕ` lives in `LawvereKSimInterp.lean`; the extensional
quotient in `LawvereKSimQuot.lean`.

See `docs/lawvere-k-sim-hierarchy.md` for the canonical
mathematical reference and design principles P1 – P10.
-/

namespace GebLean

/-- The K^sim term language at arity `n`: K^sim
single-output morphisms representing functions `ℕ^n → ℕ`.

Generators per `docs/lawvere-k-sim-hierarchy.md`:
`zero`, `succ`, `proj`, `comp`, `simrec`, `raise`.  Per P8,
`simrec` carries an output index plus base and step
families written as `KMorN`-shaped values; the families
are unfolded inline as `Fin (k+1) → KMor1 _` because
`KMorN` itself is defined later as an abbreviation. -/
inductive KMor1 : ℕ → Type where
  /-- Constant `0` at any arity. -/
  | zero {n : ℕ} : KMor1 n
  /-- Successor function (arity `1`). -/
  | succ : KMor1 1
  /-- The `i`-th projection out of `n` arguments. -/
  | proj {n : ℕ} (i : Fin n) : KMor1 n
  /-- Composition: apply a `b`-ary morphism to the
  results of `b` `a`-ary morphisms. -/
  | comp {a b : ℕ} (f : KMor1 b)
      (gs : Fin b → KMor1 a) : KMor1 a
  /-- Simultaneous primitive recursion at output index
  `i`, with system size `k+1`, base-case family `h`,
  and step-function family `g`.  Produces a morphism
  of arity `a+1` (one slot for the recursion variable
  followed by `a` slots for the parameter list). -/
  | simrec {a k : ℕ}
      (i : Fin (k+1))
      (h : Fin (k+1) → KMor1 a)
      (g : Fin (k+1) → KMor1 (a + 1 + (k + 1))) :
      KMor1 (a + 1)
  /-- Level-bumping marker (no operational effect on
  `interp`; lifts a term's structural level by one). -/
  | raise {n : ℕ} (f : KMor1 n) : KMor1 n

instance (n : ℕ) : Inhabited (KMor1 n) := ⟨KMor1.zero⟩

end GebLean
