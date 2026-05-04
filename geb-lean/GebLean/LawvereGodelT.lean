import Mathlib.Data.Set.Insert
import GebLean.LawvereNatBT

/-!
# `LawvereGodelT`: Base/type module for Beckmann-Weiermann's T*

The signature `S : Set GodelTBase` selects which base types are
available (`nat` is always usable; `tree` is opt-in).
`GodelTType S` is the resulting type system: a base former
gated by membership in `S`, plus arrows.  `interp` is the
standard set-theoretic semantics; `level` is B-W's measure
`g` (Definition 7).
-/

namespace GebLean

/-- Base types in the typed combinatory system.  `nat` is
always available; `tree` is opt-in via the `S : Set GodelTBase`
parameter. -/
inductive GodelTBase : Type
  | nat
  | tree
  deriving DecidableEq, Repr, Inhabited

/-- Carrier of each base type. -/
@[reducible] def GodelTBase.carrier : GodelTBase → Type
  | .nat => Nat
  | .tree => BTL

/-- Types over a chosen base-type set.  `arrow` is the only
type former besides `base`; this matches Beckmann-Weiermann
Definition 1. -/
inductive GodelTType (S : Set GodelTBase) : Type
  | base (b : GodelTBase) (h : b ∈ S) : GodelTType S
  | arrow : GodelTType S → GodelTType S → GodelTType S

namespace GodelTType

/-- Standard interpretation of a type: base types use their
carriers, arrow types are Lean function types. -/
@[reducible] def interp {S : Set GodelTBase} : GodelTType S → Type
  | .base b _ => b.carrier
  | .arrow σ τ => σ.interp → τ.interp

/-- Type-level measure `g` from Beckmann-Weiermann Definition
7.  `g (.base _) = 0`; `g (.arrow σ τ) = max (g σ + 1) (g τ)`. -/
def level {S : Set GodelTBase} : GodelTType S → Nat
  | .base _ _ => 0
  | .arrow σ τ => max (σ.level + 1) τ.level

end GodelTType

end GebLean
