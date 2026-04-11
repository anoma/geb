import GebLean.LawvereER
import Mathlib.Data.Fin.VecNotation

/-!
# Tests for LawvereER

`#guard` sanity tests covering the interpretation
of each generator and of `ERMorN` tuple
composition.
-/

open GebLean

-- The empty context for `ERMor1 0` terms.
private def ctx0 : Fin 0 → ℕ := Fin.elim0

-- A convenient unary context `(x)`.
private def ctx1 (x : ℕ) : Fin 1 → ℕ :=
  fun _ => x

-- A convenient binary context `(x, y)`.
private def ctx2 (x y : ℕ) : Fin 2 → ℕ :=
  ![x, y]

-- zero at the empty context.
#guard ERMor1.zero.interp ctx0 == 0

-- succ of 5.
#guard ERMor1.succ.interp (ctx1 5) == 6

-- proj 0 out of (7, 3).
#guard (ERMor1.proj (0 : Fin 2)).interp
  (ctx2 7 3) == 7

-- proj 1 out of (7, 3).
#guard (ERMor1.proj (1 : Fin 2)).interp
  (ctx2 7 3) == 3

-- sub at (7, 3) is 4.
#guard ERMor1.sub.interp (ctx2 7 3) == 4

-- sub is cut-off: sub at (3, 7) is 0.
#guard ERMor1.sub.interp (ctx2 3 7) == 0

-- bsum of `proj 1` at `(x, y)` is `x * y`.
-- At `(3, 4)` it sums `4` three times: 12.
#guard (ERMor1.bsum
  (ERMor1.proj (1 : Fin 2))).interp
  (ctx2 3 4) == 12

-- bprod of `proj 1` at `(x, y)` is `y ^ x`.
-- At `(3, 2)` it multiplies `2` three times: 8.
#guard (ERMor1.bprod
  (ERMor1.proj (1 : Fin 2))).interp
  (ctx2 3 2) == 8

-- Empty bprod returns 1 (bound = 0).
#guard (ERMor1.bprod
  (ERMor1.proj (1 : Fin 2))).interp
  (ctx2 0 5) == 1

-- Empty bsum returns 0.
#guard (ERMor1.bsum
  (ERMor1.proj (1 : Fin 2))).interp
  (ctx2 0 5) == 0

-- An ERMorN 2 1 tuple of one binary term: sub.
private def subTuple : ERMorN 2 1 :=
  fun _ => ERMor1.sub

-- An ERMorN 2 2 tuple swapping two inputs.
private def swapTuple : ERMorN 2 2 :=
  fun i => match i with
    | ⟨0, _⟩ => ERMor1.proj (1 : Fin 2)
    | ⟨1, _⟩ => ERMor1.proj (0 : Fin 2)

-- subTuple at (7, 3) computes sub once.
#guard (subTuple.interp (ctx2 7 3)) 0 == 4

-- swapTuple at (7, 3) swaps to (3, 7).
#guard (swapTuple.interp (ctx2 7 3)) 0 == 3
#guard (swapTuple.interp (ctx2 7 3)) 1 == 7

-- Composition of ERMorN.id with subTuple is
-- subTuple (verified pointwise on one context).
#guard
  (((ERMorN.id 2).comp subTuple).interp
    (ctx2 7 3)) 0 == 4

-- Composition of swap followed by sub computes
-- (3, 7) → 3 - 7 = 0 (cut-off).
#guard
  ((swapTuple.comp subTuple).interp
    (ctx2 7 3)) 0 == 0
