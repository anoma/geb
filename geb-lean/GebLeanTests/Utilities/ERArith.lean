import GebLean.Utilities.ERArith

/-!
# Tests for `ERMor1.div` and `ERMor1.mod`.
-/

open GebLean

#guard (ERMor1.div).interp ![7, 3] = 2
#guard (ERMor1.div).interp ![10, 2] = 5
#guard (ERMor1.div).interp ![0, 5] = 0
#guard (ERMor1.div).interp ![5, 0] = 0

#guard (ERMor1.mod).interp ![7, 3] = 1
#guard (ERMor1.mod).interp ![10, 5] = 0
#guard (ERMor1.mod).interp ![0, 5] = 0
