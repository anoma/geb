import GebLean.LawvereNatBTInterp

/-!
# Tests for LawvereNatBTInterp

Sanity tests for the interpretation functor and faithfulness.
-/

open GebLean
open CategoryTheory

-- The interpretation functor type-checks.
example : LawvereNatBTCat ⥤ Type := natBTInterpFunctor

-- Faithfulness instance is available.
example : natBTInterpFunctor.Faithful := inferInstance

-- Objects go to the expected product of function types.
example : natBTInterpFunctor.obj (0, 0) =
    ((Fin 0 → ℕ) × (Fin 0 → BTL)) := rfl

example : natBTInterpFunctor.obj (2, 3) =
    ((Fin 2 → ℕ) × (Fin 3 → BTL)) := rfl
