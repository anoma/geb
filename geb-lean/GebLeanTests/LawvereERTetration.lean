import GebLean.LawvereERTetration

/-!
# Tests for tetration non-elementary result

Sanity tests: tetration computation and type-checks of the non-ER /
non-fullness theorems.
-/

open GebLean

-- tetration 0 = tower 0 1 = 1
#guard tetration 0 = 1

-- tetration 1 = tower 1 1 = 2
#guard tetration 1 = 2

-- tetration 2 = tower 2 1 = 4
#guard tetration 2 = 4

-- tetration 3 = tower 3 1 = 16
#guard tetration 3 = 16

-- tetration 4 = tower 4 1 = 2^16 = 65536
#guard tetration 4 = 65536

-- Non-ER theorem type-checks
example : ¬ ∃ t : ERMor1 1, ∀ x : ℕ,
    t.interp (fun _ => x) = tetration x :=
  tetration_not_ER

-- Non-fullness via tetration type-checks
example : ¬ erInterpFunctor.Full :=
  erInterpFunctor_not_full_via_tetration
