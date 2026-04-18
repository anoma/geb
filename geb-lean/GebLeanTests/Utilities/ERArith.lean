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

/-- `boundedRec` is dominated by the bound for any context. -/
example (ctx : Fin 1 → ℕ) :
    (ERMor1.boundedRec ERMor1.zero
        (ERMor1.comp ERMor1.succ
          fun (_ : Fin 1) => ERMor1.proj 1)
        (ERMor1.comp ERMor1.succ
          fun (_ : Fin 1) => ERMor1.proj 0)).interp
        ctx ≤
      ERMor1.succ.interp (Fin.cons (ctx 0) Fin.elim0) :=
  ERMor1.interp_boundedRec_le_bound _ _ _ _

/-- At `n = 0`, `boundedRec` with base `zero`, step `succ ∘
proj 1`, and bound `succ ∘ proj 0` returns `0`, confirmed via
`boundedRec_eq_natRec_of_bounded`. -/
example :
    (ERMor1.boundedRec ERMor1.zero
        (ERMor1.comp ERMor1.succ
          fun (_ : Fin 1) => ERMor1.proj 1)
        (ERMor1.comp ERMor1.succ
          fun (_ : Fin 1) => ERMor1.proj 0)).interp
        (Fin.cons 0 Fin.elim0) = 0 := by
  rw [ERMor1.boundedRec_eq_natRec_of_bounded]
  · rfl
  · intro j hj
    have hj0 : j = 0 := Nat.le_zero.mp hj
    subst hj0
    simp
  · intro j hj
    have hj0 : j = 0 := Nat.le_zero.mp hj
    subst hj0
    simp
