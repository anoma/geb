import GebLean.Utilities.KArith
import Mathlib.Data.Fin.VecNotation

/-!
# Tests for K^sim-derived arithmetic functions.
-/

open GebLean

#guard KMor1.pred.interp ![0] == 0
#guard KMor1.pred.interp ![1] == 0
#guard KMor1.pred.interp ![5] == 4
