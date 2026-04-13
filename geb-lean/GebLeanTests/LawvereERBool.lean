import GebLean.LawvereERBool
import Mathlib.Data.Fin.VecNotation

/-!
# Tests for LawvereERBool

`#guard` sanity tests for `boolNot`, `boolAnd`, and
`boolEqNat`.
-/

open GebLean

private def ctx1 (x : ℕ) : Fin 1 → ℕ := fun _ => x

private def ctx2 (x y : ℕ) : Fin 2 → ℕ := ![x, y]

-- boolNot: 1 if input is 0, else 0
#guard ERMor1.boolNot.interp (ctx1 0) == 1
#guard ERMor1.boolNot.interp (ctx1 1) == 0
#guard ERMor1.boolNot.interp (ctx1 5) == 0

-- boolAnd: multiplication
#guard ERMor1.boolAnd.interp (ctx2 0 0) == 0
#guard ERMor1.boolAnd.interp (ctx2 1 1) == 1
#guard ERMor1.boolAnd.interp (ctx2 1 0) == 0
#guard ERMor1.boolAnd.interp (ctx2 0 1) == 0
#guard ERMor1.boolAnd.interp (ctx2 3 4) == 12

-- subSwap: y - x
#guard ERMor1.subSwap.interp (ctx2 3 7) == 4
#guard ERMor1.subSwap.interp (ctx2 7 3) == 0

-- boolEqNat: 1 iff equal
#guard ERMor1.boolEqNat.interp (ctx2 3 3) == 1
#guard ERMor1.boolEqNat.interp (ctx2 0 0) == 1
#guard ERMor1.boolEqNat.interp (ctx2 3 5) == 0
#guard ERMor1.boolEqNat.interp (ctx2 5 3) == 0
