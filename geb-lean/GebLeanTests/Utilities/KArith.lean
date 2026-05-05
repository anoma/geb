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
