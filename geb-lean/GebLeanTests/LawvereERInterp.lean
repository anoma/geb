import GebLean.LawvereERInterp

/-!
# Tests for LawvereERInterp

Sanity tests for the interpretation functor and
faithfulness.
-/

open GebLean
open CategoryTheory

-- The interpretation functor maps arity 2 to
-- `Fin 2 -> Nat`.
example : erInterpFunctor.obj 2 =
    (Fin 2 → ℕ) := rfl

-- Faithfulness instance is available.
example : erInterpFunctor.Faithful :=
  inferInstance
