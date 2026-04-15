import GebLean.LawvereERDelta

/-!
# Tests for LawvereERDelta

Sanity tests for the embedding `Δ : LawvereERCat ⥤
LawvereERLexCat` and its full/faithful/preserves-
products instances.
-/

open GebLean
open CategoryTheory

-- The constructive FullyFaithful data is
-- available.
example : erDeltaFunctor.FullyFaithful :=
  erDeltaFunctor.fullyFaithful

-- Faithful instance is available (derived from
-- fullyFaithful).
example : erDeltaFunctor.Faithful := inferInstance

-- Full instance is available (derived from
-- fullyFaithful).
example : erDeltaFunctor.Full := inferInstance

-- PreservesFiniteProducts instance is available.
example :
    Limits.PreservesFiniteProducts erDeltaFunctor :=
  inferInstance

-- Δ sends 0 to the terminal LexObj.
example : erDeltaFunctor.obj (0 : LawvereERCat) =
    LexObj.terminal := rfl

-- Δ sends 2 to an object of arity 2.
example :
    (erDeltaFunctor.obj (2 : LawvereERCat)).arity =
      2 := rfl
