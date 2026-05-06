import GebLean.Utilities.KArith
import Mathlib.Data.Fin.VecNotation

/-!
# Tests for K^sim-derived arithmetic functions.
-/

open GebLean

#guard KMor1.pred.interp ![0] == 0
#guard KMor1.pred.interp ![1] == 0
#guard KMor1.pred.interp ![5] == 4

#guard KMor1.isZero.interp ![0] == 1
#guard KMor1.isZero.interp ![1] == 0
#guard KMor1.isZero.interp ![10] == 0

#guard KMor1.add.interp ![0, 7] == 7
#guard KMor1.add.interp ![3, 4] == 7
#guard KMor1.add.interp ![5, 0] == 5

#guard KMor1.double.interp ![0] == 0
#guard KMor1.double.interp ![5] == 10

#guard KMor1.cond.interp ![0, 11, 22] == 11
#guard KMor1.cond.interp ![1, 11, 22] == 22
#guard KMor1.cond.interp ![2, 11, 22] == 22

#guard KMor1.notEq1.interp ![0] == 0
#guard KMor1.notEq1.interp ![1] == 1
#guard KMor1.notEq1.interp ![2] == 0
#guard KMor1.notEq1.interp ![5] == 0

#guard KMor1.mult.interp ![0, 7] == 0
#guard KMor1.mult.interp ![3, 4] == 12
#guard KMor1.mult.interp ![1, 5] == 5

#guard KMor1.monus.interp ![5, 3] == 2
#guard KMor1.monus.interp ![3, 5] == 0
#guard KMor1.monus.interp ![5, 5] == 0

#guard KMor1.eq.interp ![3, 3] == 0
#guard KMor1.eq.interp ![3, 5] == 1
#guard KMor1.eq.interp ![5, 3] == 1
#guard KMor1.eq.interp ![0, 0] == 0

#guard KMor1.condEq.interp ![3, 3, 11, 22] == 11
#guard KMor1.condEq.interp ![3, 5, 11, 22] == 22
#guard KMor1.condEq.interp ![0, 0, 11, 22] == 11

#guard KMor1.pow2.interp ![0] == 1
#guard KMor1.pow2.interp ![1] == 2
#guard KMor1.pow2.interp ![4] == 16

#guard KMor1.mod.interp ![0, 5] == 0
#guard KMor1.mod.interp ![5, 1] == 0
#guard KMor1.mod.interp ![5, 5] == 0
#guard KMor1.mod.interp ![6, 3] == 0
#guard KMor1.mod.interp ![7, 3] == 1
#guard KMor1.mod.interp ![3, 0] == 3

#guard KMor1.div.interp ![7, 3] == 2
#guard KMor1.div.interp ![6, 3] == 2
#guard KMor1.div.interp ![5, 1] == 5
#guard KMor1.div.interp ![3, 5] == 0
#guard KMor1.div.interp ![5, 0] == 5
#guard KMor1.div.interp ![0, 5] == 0
#guard KMor1.div.interp ![5, 5] == 1

#guard KMor1.divNat.interp ![7, 3] == 2
#guard KMor1.divNat.interp ![5, 0] == 0
#guard KMor1.divNat.interp ![0, 5] == 0
#guard KMor1.divNat.interp ![5, 5] == 1

example : KMor1.pow.interp ![2, 3] = 8 := by simp
example : KMor1.pow.interp ![3, 2] = 9 := by simp
example : KMor1.pow.interp ![1, 5] = 1 := by simp
example : KMor1.pow.interp ![5, 1] = 5 := by simp
example : KMor1.pow.interp ![0, 0] = 1 := by simp
example : KMor1.pow.interp ![0, 1] = 0 := by simp
example : KMor1.pow.interp ![5, 0] = 1 := by simp
example : KMor1.pow.interp ![2, 5] = 32 := by simp
