import GebLean.Utilities.ERArith

/-!
# Tests for `ERMor1.div`, `ERMor1.mod`, and `ERMor1.beta`.
-/

open GebLean

#guard (ERMor1.div).interp ![7, 3] = 2
#guard (ERMor1.div).interp ![10, 2] = 5
#guard (ERMor1.div).interp ![0, 5] = 0
#guard (ERMor1.div).interp ![5, 0] = 0

#guard (ERMor1.mod).interp ![7, 3] = 1
#guard (ERMor1.mod).interp ![10, 5] = 0
#guard (ERMor1.mod).interp ![0, 5] = 0

#guard (ERMor1.beta).interp ![5, 3, 0] = 5 % 4
#guard (ERMor1.beta).interp ![7, 2, 1] = 7 % 5
#guard (ERMor1.beta).interp ![10, 3, 2] = 10 % 10

example (a b : ℕ) :
    (ERMor1.beta).interp ![a, b, 0] = a % (1 + b) := by
  rw [ERMor1.interp_beta]
  ring_nf

example : ∃ a b : ℕ, ∀ i : Fin 3,
    a % (1 + (i.val + 1) * b) =
      (![5, 7, 11] i : ℕ) := Nat.beta_exists _
