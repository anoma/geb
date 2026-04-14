import GebLean.Utilities.Tower

/-!
# Tests for tower function

Sanity tests for the iterated-exponential `tower` function.
-/

open GebLean

-- tower 0 x = x
#guard tower 0 5 = 5

-- tower 1 x = 2 ^ x
#guard tower 1 3 = 8

-- tower 2 3 = 2 ^ (2 ^ 3) = 2 ^ 8 = 256
#guard tower 2 3 = 256

-- tower 3 1 = 2 ^ (2 ^ (2 ^ 1)) = 2 ^ (2 ^ 2) = 2 ^ 4 = 16
#guard tower 3 1 = 16
