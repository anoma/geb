import GebLean.LawvereERArith
import Mathlib.Data.Fin.VecNotation

/-!
# Tests for LawvereERArith

Sanity tests for derived arithmetic operations on ER terms.
-/

open GebLean

-- expER at [3, 2] computes 2 ^ 3 = 8
#guard ERMor1.expER.interp ![3, 2] = 8

-- expER at [0, 5] computes 5 ^ 0 = 1
#guard ERMor1.expER.interp ![0, 5] = 1

-- expER at [5, 0] computes 0 ^ 5 = 0
#guard ERMor1.expER.interp ![5, 0] = 0

-- expER at [4, 3] computes 3 ^ 4 = 81
#guard ERMor1.expER.interp ![4, 3] = 81
