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

/-- At arity 1 with outer context `![5]`, searching with bound
`proj 0` (so the bound is `5`) and predicate "slot 0 is zero"
returns `0`: the least `j < 5` with `1 - j = 1` is `j = 0`. -/
example :
    (ERMor1.boundedSearch (ERMor1.proj 0)
      (ERMor1.comp ERMor1.boolNot fun (_ : Fin 1) =>
        ERMor1.proj 0)).interp ![5] = 0 := by
  apply ERMor1.boundedSearch_eq_unique _ _ _ 0
  · intro j
    change (1 : ℕ) - j ≤ 1
    omega
  · change (0 : ℕ) < 5
    omega
  · change (1 : ℕ) - 0 = 1
    rfl
  · intro j' hj' hpj'
    change (1 : ℕ) - j' = 1 at hpj'
    omega
